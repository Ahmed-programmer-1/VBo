# Megamax grabber (built on vidgrab.py): opens a Megamax/share4max window, skips ads, tries its hosts, captures + verifies m3u8/mp4
import html as htmllib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import urljoin, urlparse

try:
    import requests
except ImportError:
    sys.exit("pip install requests")
from playwright.sync_api import sync_playwright

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
DEFAULT_REFERER = "https://shahiid-anime.net/"
MEGAMAX_HOSTS = ("share4max", "megamax")
HOST_RX = (r"kraken|vidmoly|sibnet|streamruby|hgcloud|turbovid|vidhls|streamlare|vidtube|filelions|lulu|dood|streamtape|mixdrop|uqload|voe|filemoon|streamwish|vidhide|vidguard|upstream|"
           r"earnvids|streamhg|mp4upload|vidoza|streamsb|ok\.?ru|vkvideo|\bvk\b")
BLOCK_HOSTS = ("monetag", "doubleclick", "googlesyndication", "adsterra", "popads", "propellerads",
               "histats", "googletagmanager", "google-analytics", "exoclick", "juicyads", "popcash",
               "clickadu", "hilltopads", "adcash", "trafficjunky", "onclick", "bidgear", "richads",
               "pushnami", "a-ads", "admaven", "yllix", "tsyndicate", "highperformanceformat",
               "profitableratecpm", "effectivegatecpm", "cpmstar", "adskeeper", "mgid")

# media detection (network URLs) and in-text detection (from vidgrab, handles escaped slashes)
MEDIA_URL_RE = re.compile(r"\.(?:m3u8|mp4)(?:$|[?#&])|/master\.txt|urlset/master|/hls[^/]*/[^?]*\.txt", re.I)
MEDIA_TEXT_RE = re.compile(r'https?:?(?:\\?/){2}[^\s"\'<>\\]+?\.(?:m3u8|mp4)[^\s"\'<>\\]*', re.I)
BAD_WORDS = ("preview", "thumb", "sprite", "trailer", "/ads/", "banner")
PACKED_RE = re.compile(r"}\('(.*)',(\d+),(\d+),'(.*?)'\.split\('\|'\)", re.S)

CAUGHT = {}            # url -> {"referer": ...} seen on the network after a host click
BAD = Counter()        # url -> failed verification count
SUCCESS = Counter()    # host name -> times it worked (adaptive order)
DEBUG = "--debug" in sys.argv
HEADLESS = "--headless" in sys.argv
ALLOW_MP4 = "--allow-mp4" in sys.argv    # default: m3u8 ONLY (an MP4 is accepted only when you start the tool with --allow-mp4)
MIN_SECONDS = 18 * 60                     # real episodes only; override with --min-minutes=N
for _a in sys.argv:
    if _a.startswith("--min-minutes="):
        try:
            MIN_SECONDS = float(_a.split("=", 1)[1]) * 60
        except ValueError:
            pass


def set_min_seconds(v):
    # Used per job (a 5-minute short film must not be rejected by the 18-minute episode rule); returns the old value
    global MIN_SECONDS
    old, MIN_SECONDS = MIN_SECONDS, v
    return old


BLOCK_ADS = "--block-ads" in sys.argv   # default: ads are NOT blocked (players often hide the video when ad scripts are blocked)
AVOID = ["mixdrop", "dood"]            # hosts skipped entirely (inside Megamax and as outer servers)
SCORE_FILE = "server_reliability.json"
_SC_LOCK = threading.Lock()


def _load_scores():
    try:
        with open(SCORE_FILE, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


SCORES = _load_scores()   # {scope: {server name: {"ok": x, "fail": y}}}  - learned between runs


def avoided(name):
    low = (name or "").lower()
    return any(a and a in low for a in AVOID)


def reliability(scope, name):
    d = SCORES.get(scope, {}).get((name or "").lower())
    return 0.5 if not d else (d["ok"] + 1.0) / (d["ok"] + d["fail"] + 2.0)


def attempts(scope, name):
    d = SCORES.get(scope, {}).get((name or "").lower())
    return 0.0 if not d else d["ok"] + d["fail"]


def record(scope, name, ok):
    # Success raises a server's reliability, every failure lowers it; old evidence slowly fades
    with _SC_LOCK:
        d = SCORES.setdefault(scope, {}).setdefault((name or "").lower(), {"ok": 0.0, "fail": 0.0})
        d["ok"] *= 0.97
        d["fail"] *= 0.97
        d["ok" if ok else "fail"] += 1.0
        try:
            with open(SCORE_FILE + ".tmp", "w", encoding="utf-8") as f:
                json.dump(SCORES, f, ensure_ascii=False, indent=1)
            os.replace(SCORE_FILE + ".tmp", SCORE_FILE)
        except Exception:
            pass


def rank_names(scope, names, prefer=(), avoid=None):
    # Order: preferred names first (unless they keep failing), then by learned reliability, then page order. Avoided names are dropped.
    avoid = AVOID if avoid is None else avoid
    keep = [n for n in dict.fromkeys(names) if not any(a and a in n.lower() for a in avoid)]

    def key(item):
        i, n = item
        low = n.lower()
        pi = next((k for k, p in enumerate(prefer) if p and p in low), len(prefer))
        if pi < len(prefer) and attempts(scope, n) >= 4 and reliability(scope, n) < 0.25:
            pi = len(prefer)   # a "preferred" server that almost never works is demoted
        return (pi, -reliability(scope, n), i)
    return [n for _, n in sorted(enumerate(keep), key=key)]


# test/sample videos that players serve as a decoy
DECOY_MARKERS = ("test-videos.co.uk", "bigbuckbunny", "big_buck_bunny", "big-buck-bunny", "sintel", "tears_of_steel",
                 "elephants_dream", "commondatastorage.googleapis.com", "sample-videos", "samplelib",
                 "file-examples", "learningcontainer", "techslides", "w3schools", "mdn.github.io", "/sample.mp4")
CTX, BROWSER_THREAD = None, None   # the Playwright context + the thread that owns it (its API is not thread-safe)
COOKIES = {}                       # host -> Cookie header, copied from the browser when a link is accepted (used by download threads)
DURATIONS = {}
KINDS = {}   # accepted url -> "hls" | "mp4" (many CDNs serve MP4 on URLs without any extension)


def opt(name, default, cast=int):
    for a in sys.argv:
        if a.startswith(f"--{name}="):
            try:
                return cast(a.split("=", 1)[1])
            except ValueError:
                pass
    return default


WORKERS = opt("workers", 64)      # parallel connections inside ONE download
PARALLEL = opt("parallel", 2)     # episodes downloaded at the same time
MAX_ROUNDS = 3                    # first pass + retries of failed downloads with other servers
PRIO_KW = {"creationflags": subprocess.HIGH_PRIORITY_CLASS} if sys.platform == "win32" else {}
DEBUG_REQS = []

INIT_JS = """
(() => {
  try { window.open = function () { return {closed: false, focus() {}, blur() {}, close() {}, postMessage() {}, document: {write() {}, close() {}}, location: {href: ''}}; }; } catch (e) {}
  try { Object.defineProperty(navigator, 'webdriver', {get: () => undefined}); } catch (e) {}
  window.__mm = window.__mm || [];
  const push = u => { try { window.__mm.push(String(u)); } catch (e) {} };
  const of = window.fetch;
  if (of) window.fetch = function (...a) { try { push(a[0] && a[0].url ? a[0].url : a[0]); } catch (e) {} return of.apply(this, a); };
  const xo = XMLHttpRequest.prototype.open;
  XMLHttpRequest.prototype.open = function (m, u) { push(u); return xo.apply(this, arguments); };
  try { const d = Object.getOwnPropertyDescriptor(HTMLMediaElement.prototype, 'src');
        Object.defineProperty(HTMLMediaElement.prototype, 'src', {configurable: true, enumerable: d.enumerable, get: d.get, set: function (v) { push(v); return d.set.call(this, v); }}); } catch (e) {}
  try { const sa = Element.prototype.setAttribute;
        Element.prototype.setAttribute = function (k, v) { try { if (String(k).toLowerCase() === 'src' && /^(VIDEO|SOURCE|AUDIO)$/.test(this.tagName)) push(v); } catch (e) {} return sa.apply(this, arguments); }; } catch (e) {}
  setInterval(() => {
    try {
      if (window.Hls && Hls.prototype && !Hls.prototype.__mm) {
        const ls = Hls.prototype.loadSource;
        Hls.prototype.loadSource = function (u) { push(u); return ls.apply(this, arguments); };
        Hls.prototype.__mm = 1;
      }
    } catch (e) {}
  }, 300);
})();
"""

JS_ROWS = """(rx) => {
  const re = new RegExp(rx, 'i');
  document.querySelectorAll('[data-mm-idx]').forEach(e => { delete e.dataset.mmIdx; });
  const first = el => ((el.innerText || '').split('\\n')[0] || '').trim();
  const ago = el => { const L = (el.innerText || '').split('\\n').map(x => x.trim()).filter(Boolean); return L.length >= 2 && L[0].length <= 30 && /(second|minute|hour|day|week|month|year)s? ago/i.test(L[1]); };
  const out = [], seen = new Set();
  document.querySelectorAll('body *').forEach(el => {
    const t = first(el);
    if (!t || t.length > 30 || !(re.test(t) || ago(el))) return;
    if ([...el.children].some(c => first(c) === t)) return;
    const row = el.closest('li, tr, a, button, [class*="server"], [class*="item"], [class*="row"]') || el.parentElement || el;
    if (seen.has(row)) return;
    seen.add(row);
    row.dataset.mmIdx = String(out.length);
    out.push({idx: out.length, name: t.toLowerCase()});
  });
  return out;
}"""

JS_SCAN = """() => {
  const out = [];
  try { (window.__mm || []).forEach(u => out.push(u)); } catch (e) {}
  try { performance.getEntriesByType('resource').forEach(e => out.push(e.name)); } catch (e) {}
  try { document.querySelectorAll('video,source').forEach(v => { if (v.currentSrc) out.push(v.currentSrc); if (v.src) out.push(v.src); }); } catch (e) {}
  try { if (window.jwplayer) { const p = jwplayer().getPlaylist() || [];
        p.forEach(i => { (i.sources || []).forEach(s => out.push(s.file)); if (i.file) out.push(i.file); }); } } catch (e) {}
  try { if (window.videojs) Object.values(videojs.getPlayers()).forEach(p => { if (p && p.currentSrc) out.push(p.currentSrc()); }); } catch (e) {}
  return out.filter(x => typeof x === 'string' && x);
}"""

JS_NUDGE = """() => {
  try { document.querySelectorAll('video').forEach(v => { v.muted = true; const p = v.play(); if (p && p.catch) p.catch(() => {}); }); } catch (e) {}
  try { document.querySelectorAll('.jw-icon-display, .jw-display-icon-container, .vjs-big-play-button, .plyr__control--overlaid, #play, [class*="play-btn"], [aria-label="Play"]').forEach(b => b.click()); } catch (e) {}
  try { if (window.jwplayer) jwplayer().play(); } catch (e) {}
}"""


# ---------------------------------------------------------------- helpers (ported from vidgrab.py)
def cookie_header(url):
    return COOKIES.get(urlparse(url or "").netloc, "")


def headers(referer=None, url=None):
    h = {"User-Agent": UA, "Accept": "*/*"}
    c = cookie_header(url) if url else ""
    if c:
        h["Cookie"] = c
    if referer:
        h["Referer"] = referer
        p = urlparse(referer)
        h["Origin"] = f"{p.scheme}://{p.netloc}"
    return h


def browser_get(url, referer, ranged=False):
    # The browser's own network stack and cookies (only usable from the thread that owns the browser)
    if CTX is None or threading.current_thread() is not BROWSER_THREAD:
        return None
    try:
        h = headers(referer)
        h.pop("User-Agent", None)
        if ranged:
            h["Range"] = "bytes=0-2047"
        return CTX.request.get(url, headers=h, timeout=20000)
    except Exception:
        return None


def remember_cookies(url):
    if CTX is not None and threading.current_thread() is BROWSER_THREAD:
        try:
            COOKIES[urlparse(url).netloc] = "; ".join(f"{c['name']}={c['value']}" for c in CTX.cookies(url))
        except Exception:
            pass


def fetch(url, referer=None):
    try:
        r = requests.get(url, headers=headers(referer, url), timeout=30)
        r.raise_for_status()
        return r.text
    except Exception:
        r = browser_get(url, referer)   # some CDNs refuse scripts but serve the browser
        if r is not None and r.status == 200:
            return r.text()
        raise


def _base(n, base):
    d = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    return d[n] if n < base else _base(n // base, base) + d[n % base]


def unpack(text):
    # Decode eval(function(p,a,c,k,e,d)...) packed JS
    out = []
    for m in PACKED_RE.finditer(text):
        payload, a, c, words = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4).split("|")
        table = {}
        for i in range(c):
            table[_base(i, a)] = words[i] if i < len(words) and words[i] else _base(i, a)
        out.append(re.sub(r"\b\w+\b", lambda x: table.get(x.group(0), x.group(0)), payload.replace("\\'", "'")))
    return "\n".join(out)


def clean(u):
    return htmllib.unescape(u.replace("\\/", "/")).rstrip("\\")


def find_media(text, page_url):
    text = text + "\n" + unpack(text)
    found = []
    for m in MEDIA_TEXT_RE.finditer(text):
        u = clean(m.group(0))
        u = "https:" + u if u.startswith("//") else u
        if u not in found:
            found.append(u)
    for m in re.finditer(r'["\'](/[^"\'\s]+\.(?:m3u8|mp4)[^"\'\s]*)["\']', text):
        u = urljoin(page_url, clean(m.group(1)))
        if u not in found:
            found.append(u)
    return found


def best_variant(master_url, referer, txt=None):
    txt = txt or fetch(master_url, referer)
    if "#EXT-X-STREAM-INF" not in txt:
        return master_url
    best, best_bw = None, -1
    lines = txt.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("#EXT-X-STREAM-INF"):
            bw = re.search(r"BANDWIDTH=(\d+)", line)
            bw = int(bw.group(1)) if bw else 0
            for nxt in lines[i + 1:]:
                if nxt and not nxt.startswith("#"):
                    if bw > best_bw:
                        best, best_bw = urljoin(master_url, nxt.strip()), bw
                    break
    return best or master_url


def boost_system():
    # Best effort: high CPU priority and keep Windows awake while working
    try:
        if sys.platform == "win32":
            import ctypes
            k = ctypes.windll.kernel32
            k.SetPriorityClass(k.GetCurrentProcess(), 0x00000080)   # HIGH_PRIORITY_CLASS
            k.SetThreadExecutionState(0x80000000 | 0x00000001)      # ES_CONTINUOUS | ES_SYSTEM_REQUIRED
        else:
            os.nice(-5)
    except Exception:
        pass


def ffmpeg_download(url, out, referer):
    if not shutil.which("ffmpeg"):
        print("ffmpeg not found. Install it from https://ffmpeg.org and add it to PATH")
        return False
    p = urlparse(referer)
    ck = cookie_header(url)
    hdr = f"Referer: {referer}\r\nOrigin: {p.scheme}://{p.netloc}\r\nUser-Agent: {UA}\r\n" + (f"Cookie: {ck}\r\n" if ck else "")
    cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-headers", hdr, "-allowed_extensions", "ALL",
           "-i", url, "-c", "copy", "-bsf:a", "aac_adtstoasc", "-movflags", "+faststart", out]
    return subprocess.call(cmd, **PRIO_KW) == 0


def direct_download(url, out, referer):
    with requests.get(url, headers=headers(referer), stream=True, timeout=30) as r:
        r.raise_for_status()
        total = int(r.headers.get("content-length", 0))
        done = 0
        with open(out, "wb") as f:
            for chunk in r.iter_content(1 << 20):
                f.write(chunk)
                done += len(chunk)
                if total:
                    print(f"\r  {done * 100 // total}%  ({done >> 20} MB)", end="", flush=True)
    print()
    return True


class Meter:
    def __init__(self, total, show=True):
        self.total, self.show = total, show
        self.n = self.bytes = 0
        self.t0, self.last = time.time(), 0.0
        self.lock = threading.Lock()

    def add(self, size, items=1):
        with self.lock:
            self.n += items
            self.bytes += size
            now = time.time()
            if self.show and (now - self.last > 0.4 or self.n >= self.total):
                self.last = now
                speed = self.bytes / max(now - self.t0, 0.001) / 1e6
                print(f"\r  {self.n}/{self.total}  {self.bytes / 1e6:.0f} MB  {speed:.1f} MB/s   ", end="", flush=True)


def thread_session(store, referer):
    # One keep-alive session per worker thread; trust_env=False skips slow system-proxy lookups
    if not hasattr(store, "s"):
        s = requests.Session()
        s.trust_env = False
        s.headers.update(headers(referer))
        store.s = s
    return store.s


def fast_hls_download(url, referer, out, workers=None, show=True):
    # Download every HLS segment in parallel, then remux locally with ffmpeg (copy, no re-encode)
    workers = workers or WORKERS
    if not shutil.which("ffmpeg"):
        print("ffmpeg not found. Install it from https://ffmpeg.org and add it to PATH")
        return False
    try:
        playlist_url = best_variant(url, referer)
        text = fetch(playlist_url, referer)
    except Exception as e:
        print("   playlist fetch failed:", e)
        return False
    if "#EXT-X-BYTERANGE" in text or "#EXT-X-STREAM-INF" in text:
        return False  # unusual layout: let plain ffmpeg handle it
    tmp = out + ".parts"
    os.makedirs(tmp, exist_ok=True)
    jobs, lines, n = [], [], 0
    seg_ext = (".ts", ".m4s", ".mp4", ".aac", ".m4a", ".cmfv", ".cmfa", ".m4v")
    for raw in text.splitlines():
        s = raw.strip()
        if s.startswith(("#EXT-X-KEY", "#EXT-X-MAP")):
            m = re.search(r'URI="([^"]+)"', s)
            if m:
                n += 1
                name = f"aux{n}" + (".mp4" if s.startswith("#EXT-X-MAP") else ".key")
                jobs.append((urljoin(playlist_url, m.group(1)), name))
                s = s.replace(m.group(1), name)
            lines.append(s)
        elif s and not s.startswith("#"):
            n += 1
            ext = os.path.splitext(urlparse(s).path)[1].lower()
            name = f"seg{n:06d}" + (ext if ext in seg_ext else ".ts")
            jobs.append((urljoin(playlist_url, s), name))
            lines.append(name)
        else:
            lines.append(s)

    meter = Meter(len(jobs), show)
    store = threading.local()

    def fetch_one(job):
        u, name = job
        path = os.path.join(tmp, name)
        if os.path.exists(path) and os.path.getsize(path) > 0:  # resume
            meter.add(os.path.getsize(path))
            return True
        for attempt in range(6):
            try:
                r = thread_session(store, referer).get(u, headers=headers(None, u) if cookie_header(u) else None, timeout=(10, 40), stream=True)
                r.raise_for_status()
                size = 0
                with open(path + ".part", "wb") as f:
                    for chunk in r.iter_content(1 << 18):
                        f.write(chunk)
                        size += len(chunk)
                os.replace(path + ".part", path)
                meter.add(size)
                return True
            except Exception:
                time.sleep(min(0.3 * 2 ** attempt, 5))
        return False

    with ThreadPoolExecutor(max_workers=workers) as ex:
        ok = list(ex.map(fetch_one, jobs))
    if show:
        print()
    if not all(ok):
        print(f"   {ok.count(False)} part(s) failed; partial files kept in {tmp} (re-run resumes them)")
        return False

    local = os.path.join(tmp, "local.m3u8")
    with open(local, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-allowed_extensions", "ALL",
           "-protocol_whitelist", "file,crypto,data", "-i", local,
           "-c", "copy", "-bsf:a", "aac_adtstoasc", "-movflags", "+faststart", out]
    if subprocess.call(cmd, **PRIO_KW) != 0:
        return False
    shutil.rmtree(tmp, ignore_errors=True)
    return True


def fast_direct_download(url, out, referer, workers=None, show=True):
    # Multi-connection ranged download for a direct MP4
    workers = workers or WORKERS
    try:
        r = requests.get(url, headers={**headers(referer, url), "Range": "bytes=0-0"}, stream=True, timeout=20)
        total = int((r.headers.get("Content-Range", "/0").split("/")[-1]) or 0)
        status = r.status_code
        r.close()
    except Exception:
        return direct_download(url, out, referer)
    if status != 206 or total < (8 << 20):
        return direct_download(url, out, referer)
    block = 8 << 20
    ranges = [(a, min(a + block - 1, total - 1)) for a in range(0, total, block)]
    with open(out, "wb") as f:
        f.truncate(total)
    meter = Meter(len(ranges), show)
    store = threading.local()

    def part(rg):
        a, b = rg
        for attempt in range(6):
            try:
                r = thread_session(store, referer).get(url, headers={"Range": f"bytes={a}-{b}", **({"Cookie": cookie_header(url)} if cookie_header(url) else {})}, timeout=(10, 60), stream=True)
                if r.status_code != 206:
                    raise IOError("range not honoured")
                size = 0
                with open(out, "r+b") as f:
                    f.seek(a)
                    for chunk in r.iter_content(1 << 18):
                        f.write(chunk)
                        size += len(chunk)
                meter.add(size)
                return True
            except Exception:
                time.sleep(min(0.3 * 2 ** attempt, 5))
        return False

    with ThreadPoolExecutor(max_workers=min(workers, 32)) as ex:
        ok = list(ex.map(part, ranges))
    if show:
        print()
    return all(ok)


def download(link, referer, out, show=True, kind=None):
    try:
        os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
        if kind == "mp4" or (kind is None and link.lower().split("?")[0].endswith(".mp4")):
            return fast_direct_download(link, out, referer, show=show)
        if fast_hls_download(link, referer, out, show=show):
            return True
        print("   fast mode unavailable/failed, falling back to plain ffmpeg ...")
        return ffmpeg_download(best_variant(link, referer), out, referer)
    except Exception as e:
        print("   download failed:", e)
        return False


# ---------------------------------------------------------------- media logic
def is_media(u):
    if not u or u.startswith(("blob:", "data:", "about:")):
        return False
    low = u.lower()
    if not MEDIA_URL_RE.search(low):
        return False
    return not (".mp4" in low and any(w in low for w in BAD_WORDS))


def rank(u):
    path = u.lower().split("?")[0]
    if path.endswith(".m3u8"):
        return 0 if "master" in path else 1
    if path.endswith(".mp4"):
        return 3
    return 2


def _sniff(head, ct, url, total):
    if head.lstrip()[:7] == b"#EXTM3U":
        return "hls", 0
    if b"ftyp" in head[:16] or ct.startswith("video/mp4") or url.lower().split("?")[0].endswith(".mp4"):
        return "mp4", total
    return None, 0


def probe(url, referer):
    # -> ("hls" | "mp4" | None, total bytes): looks at the first bytes the server really returns (content, not URL).
    # Python with the browser's cookies first (ranged, then plain); if the CDN refuses scripts, the browser's own stack.
    for extra in ({"Range": "bytes=0-2047"}, {}):
        try:
            r = requests.get(url, headers={**headers(referer, url), **extra}, stream=True, timeout=15)
            if r.status_code not in (200, 206):
                r.close()
                continue
            head = next(r.iter_content(2048), b"")
            ct = (r.headers.get("Content-Type") or "").lower()
            total = int((r.headers.get("Content-Range") or "/0").split("/")[-1] or 0) or int(r.headers.get("Content-Length") or 0)
            r.close()
            return _sniff(head, ct, url, total)
        except Exception:
            continue
    r = browser_get(url, referer, ranged=True)
    if r is not None and r.status in (200, 206):
        try:
            h = r.headers
            total = int((h.get("content-range") or "/0").split("/")[-1] or 0) or int(h.get("content-length") or 0)
            return _sniff(r.body()[:2048], (h.get("content-type") or "").lower(), url, total)
        except Exception:
            pass
    return None, 0


def verify(url, referer):
    return probe(url, referer)[0] is not None


def hls_seconds(url, referer, body=None):
    # Total duration of an HLS playlist (sum of #EXTINF); a master playlist resolves to its best variant. None = could not be read.
    try:
        txt = body if body and body.lstrip().startswith("#EXTM3U") else fetch(url, referer)
        if "#EXT-X-STREAM-INF" in txt:
            txt = fetch(best_variant(url, referer, txt), referer)
        return sum(float(x) for x in re.findall(r"#EXTINF:([\d.]+)", txt))
    except Exception:
        return None


def mp4_seconds(url, referer, total=0):
    if shutil.which("ffprobe"):
        hdr = f"Referer: {referer}\r\nUser-Agent: {UA}\r\n"
        try:
            out = subprocess.run(["ffprobe", "-v", "error", "-headers", hdr, "-show_entries", "format=duration",
                                  "-of", "default=nw=1:nk=1", url], capture_output=True, text=True, timeout=30).stdout
            return float(out.strip())
        except Exception:
            pass
    # no ffprobe: a real file is big enough for the minimum length (about 0.5 Mbit/s or more)
    return MIN_SECONDS if total >= max(2 << 20, MIN_SECONDS * 60000) else 0.0


def accept(url, referer):
    # A candidate counts only if it is not a known decoy, really answers, and is long enough to be the episode
    low = url.lower()
    if any(k in low for k in DECOY_MARKERS):
        BAD[url] = 9
        print(f"      ignored decoy: {url[:90]}")
        return False
    kind, total = probe(url, referer)
    body = (CAUGHT.get(url) or {}).get("body")
    if kind is None and body and body.lstrip().startswith("#EXTM3U"):
        kind = "hls"   # the browser itself received this playlist, even if scripts cannot
    if kind is None:
        BAD[url] += 1
        return False
    if kind == "mp4" and not ALLOW_MP4:
        BAD[url] = 9
        print(f"      note: this server gives a direct MP4, not m3u8 (ignored; start with --allow-mp4 to accept it): {url[:80]}")
        return False
    secs = mp4_seconds(url, referer, total) if kind == "mp4" else hls_seconds(url, referer, body)
    if secs is None:   # the duration cannot be read (the CDN refuses scripts): trust the playlist the browser played
        secs = MIN_SECONDS
        print(f"      (duration not verified) {url[:80]}")
    if secs < MIN_SECONDS:
        BAD[url] = 9
        print(f"      ignored (only {secs / 60:.1f} min): {url[:90]}")
        return False
    DURATIONS[url], KINDS[url] = secs, kind
    remember_cookies(url)
    return True


def media_candidates(page, deep=False):
    cands = {u: dict(v) for u, v in CAUGHT.items()}
    for fr in page.frames:
        try:
            for u in fr.evaluate(JS_SCAN):
                u = urljoin(fr.url, clean(u)) if not u.startswith("http") else clean(u)
                if is_media(u):
                    cands.setdefault(u, {"referer": fr.url})
            if deep:
                for u in find_media(fr.content(), fr.url):
                    if is_media(u):
                        cands.setdefault(u, {"referer": fr.url})
        except Exception:
            continue
    return cands


def player_frame(page):
    # the biggest non-ad iframe = the player
    best, area = None, 0
    for fr in page.frames:
        if fr == page.main_frame or not fr.url.startswith("http") or any(k in fr.url for k in BLOCK_HOSTS):
            continue
        try:
            box = fr.frame_element().bounding_box()
        except Exception:
            continue
        if box and box["width"] * box["height"] > area:
            best, area = fr, box["width"] * box["height"]
    return best


def click_center(page, fr=None):
    # Many players start loading the media ONLY after a real click on their big play button (they sit in the middle)
    try:
        if fr is not None and fr != page.main_frame:
            el = fr.frame_element()
            el.scroll_into_view_if_needed(timeout=2000)
            box = el.bounding_box()
        else:
            vs = page.viewport_size or {"width": 1280, "height": 720}
            box = {"x": 0, "y": 0, "width": vs["width"], "height": vs["height"]}
        if box:
            page.mouse.click(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
    except Exception:
        pass


def wait_media(page, timeout=35, frame="auto"):
    t0, n, mp4_hit, deadline, seen = time.time(), 0, None, None, set()
    while time.time() - t0 < timeout and not (deadline and time.time() >= deadline):
        page.wait_for_timeout(1000)
        n += 1
        if n in (2, 4, 6, 9, 12, 15, 19, 23, 27, 31):
            for fr in page.frames:
                try:
                    fr.evaluate(JS_NUDGE)
                except Exception:
                    pass
            click_center(page, player_frame(page) if frame == "auto" else frame)
        cands = media_candidates(page, deep=(n % 3 == 0))
        for url in sorted(cands, key=rank):
            if BAD[url] >= 2 or url in seen:
                continue
            ref = cands[url].get("referer") or DEFAULT_REFERER
            if accept(url, ref):
                if KINDS.get(url) == "hls":
                    return url, ref
                seen.add(url)
                if mp4_hit is None:  # an m3u8 may still show up; otherwise the MP4 is used
                    mp4_hit, deadline = (url, ref), time.time() + 6
    return mp4_hit or (None, None)


# ---------------------------------------------------------------- page driving
def open_page(page, url):
    for attempt in range(1, 4):
        try:
            page.goto(url, wait_until="domcontentloaded", timeout=60000, referer=DEFAULT_REFERER)
            break
        except Exception as e:
            print(f"   (load warning {attempt}/3): {str(e).splitlines()[0]}")
    if page.url.startswith("chrome-error"):
        print("   (the tab landed on a browser error page, retrying once)")
        page.wait_for_timeout(2000)
        try:
            page.goto(url, wait_until="domcontentloaded", timeout=60000, referer=DEFAULT_REFERER)
        except Exception:
            pass
    for _ in range(40):  # wait out a "checking your browser" page
        try:
            title = (page.title() or "").lower()
        except Exception:
            title = ""
        if "just a moment" in title or "لحظة" in title:
            page.wait_for_timeout(1500)
        else:
            break
    page.wait_for_timeout(1200)


def wait_rows(page, seconds=15, frames=None):
    end = time.time() + seconds
    while time.time() < end:
        rows = []
        for fr in (frames or page.frames):
            try:
                rows += [(fr, r) for r in fr.evaluate(JS_ROWS, HOST_RX)]
            except Exception:
                continue
        if rows:
            return rows
        page.wait_for_timeout(800)
    return []


PLAY_SELECTORS = ["a.v-btn:has(.mdi-play)", ".v-img__placeholder a.v-btn", ".mdi-play", "a.v-btn"]


def press_play(page, frames=None):
    # The window first shows a poster with one big play button; the host list appears only after pressing it
    for sel in PLAY_SELECTORS:
        for fr in (frames or page.frames):
            try:
                loc = fr.locator(sel).first
                if loc.count() == 0:
                    continue
                try:
                    loc.click(timeout=2500)
                except Exception:
                    loc.dispatch_event("click")  # an invisible ad layer may swallow real clicks
                return True
            except Exception:
                continue
    return False


def get_rows(page, frames=None):
    home = page.url
    rows = wait_rows(page, 4, frames)
    for attempt in range(4):
        if rows:
            return rows
        if press_play(page, frames):
            print(f"   pressed the play button ({attempt + 1})")
        if page.url.startswith("chrome-error") or urlparse(page.url).netloc != urlparse(home).netloc:
            print("   the click sent the tab away (ad hijack): going back to the player")
            open_page(page, home)
        rows = wait_rows(page, 6, frames)
    return rows


def click_row(frame, idx):
    loc = frame.locator(f'[data-mm-idx="{idx}"]').first
    btn = loc.locator('button, [class*="play"], a, svg').last
    try:
        target = btn if btn.count() else loc
        target.click(timeout=3000)
        return True
    except Exception:
        pass
    try:  # an invisible ad overlay may swallow real clicks: fire the event straight on the element
        loc.dispatch_event("click")
        return True
    except Exception:
        return False


def dump_debug(page, tag):
    try:
        print("   debug: tab =", page.url, "| frames:", [fr.url for fr in page.frames][:6])
        with open("debug_megamax.html", "w", encoding="utf-8") as f:
            for i, fr in enumerate(page.frames):
                f.write(f"\n<!-- FRAME {i}: {fr.url} -->\n{fr.content()}\n")
        with open("debug_requests.txt", "w", encoding="utf-8") as f:
            f.write(f"# {tag}\n" + "\n".join(DEBUG_REQS))
    except Exception:
        pass


def grab(page, url, want_all=False, skip_hosts=()):
    # Try the Megamax hosts one by one; ANY failure on a host just moves on to the next one
    results = []
    try:
        open_page(page, url)
        rows = get_rows(page)
    except Exception as e:
        print("   page error:", str(e).splitlines()[0])
        return results
    if not rows:
        print("   no host rows found in the Megamax window")
        dump_debug(page, "no rows")
        return results
    all_names = [n for n in dict.fromkeys(r["name"] for _, r in rows) if n not in skip_hosts]
    skipped = [n for n in all_names if avoided(n)]
    if skipped:
        print("   avoiding:", ", ".join(skipped))
    names = rank_names("megamax", [n for n in all_names if n not in skipped])
    print("   hosts (trying order):", ", ".join(names) or "(none left)")
    first = True
    for name in names:
        try:
            CAUGHT.clear()
            BAD.clear()
            DEBUG_REQS.clear()
            if not first:
                open_page(page, url)  # clean state for each host
                rows = get_rows(page)
            first = False
            target = next(((fr, r["idx"]) for fr, r in rows if r["name"] == name), None)
            if not target:
                print(f"   {name}: row not found, next server")
                continue
            print(f"   trying {name} ...")
            click_row(*target)
            link, ref = wait_media(page)
            if DEBUG:
                dump_debug(page, name)
            if link:
                SUCCESS[name] += 1
                record("megamax", name, True)
                results.append({"host": name, "url": link, "referer": ref, "kind": KINDS.get(link)})
                print(f"      OK ({DURATIONS.get(link, 0) / 60:.1f} min)  {link}")
                if not want_all:
                    break
            else:
                record("megamax", name, False)
                print("      nothing usable, next server")
        except Exception as e:
            record("megamax", name, False)
            print(f"      {name} failed ({str(e).splitlines()[0]}), next server")
    return results


def go_back(page, fr):
    # "Back" inside the Megamax player returns to its host list
    for pat in (r"^\s*(?:←\s*)?back\s*$", r"رجوع"):
        try:
            loc = fr.get_by_text(re.compile(pat, re.I)).first
            if loc.count():
                loc.click(timeout=2500)
                page.wait_for_timeout(1200)
                return True
        except Exception:
            continue
    return False


def rows_frame(page, seconds=0):
    # the nested frame (if any) that shows a list of video hosts - found by its CONTENT, whatever its URL is
    end = time.time() + seconds
    while True:
        for fr in page.frames:
            if fr == page.main_frame:
                continue
            try:
                if len(fr.evaluate(JS_ROWS, HOST_RX)) >= 2:
                    return fr
            except Exception:
                continue
        if time.time() >= end:
            return None
        page.wait_for_timeout(700)


def megamax_frame(page, seconds=15):
    # The window is found by its CONTENT first (a host list), then by its address (host name / "/iframe/<id>" path - never by the query
    # string, a platform's own player may mention "megamax" in its parameters)
    end = time.time() + seconds
    while time.time() < end:
        fr = rows_frame(page, 0)
        if fr is not None:
            return fr
        for fr in page.frames:
            if fr == page.main_frame:
                continue
            u = urlparse(fr.url)
            if any(k in u.netloc for k in MEGAMAX_HOSTS) or re.search(r"/iframe/[A-Za-z0-9]{8,}/?$", u.path):
                return fr
        page.wait_for_timeout(700)
    return None


def grab_inpage(page, skip_hosts=()):
    # Megamax window embedded in the page (AnimeZid, EgyDead...): pick a host, click the player's play button, catch the stream,
    # press Back, try the next host.  -> None: no usable window (caller opens it alone) | []: every host failed | [rec]: success
    fr = megamax_frame(page)
    if fr is None:
        return None
    rows = get_rows(page, [fr])
    if not rows:
        return None
    all_names = [n for n in dict.fromkeys(r["name"] for _, r in rows) if n not in skip_hosts]
    skipped = [n for n in all_names if avoided(n)]
    if skipped:
        print("   avoiding:", ", ".join(skipped))
    names = rank_names("megamax", [n for n in all_names if n not in skipped])
    print("   hosts (trying order):", ", ".join(names) or "(none left)")
    for name in names:
        try:
            CAUGHT.clear()
            BAD.clear()
            rows = wait_rows(page, 6, [fr])
            target = next(((f, r["idx"]) for f, r in rows if r["name"] == name), None)
            if not target:
                print(f"   {name}: row not found, next server")
                continue
            print(f"   trying {name} ...")
            click_row(*target)
            link, ref = wait_media(page, 28, fr)
            if link:
                SUCCESS[name] += 1
                record("megamax", name, True)
                print(f"      OK ({DURATIONS.get(link, 0) / 60:.1f} min, {KINDS.get(link)})  {link}")
                return [{"host": name, "url": link, "referer": ref, "kind": KINDS.get(link)}]
            record("megamax", name, False)
            if isinstance(skip_hosts, set):
                skip_hosts.add(name)
            print("      nothing usable, next server")
        except Exception as e:
            record("megamax", name, False)
            print(f"      {name} failed ({str(e).splitlines()[0]}), next server")
        go_back(page, fr)
    return []


# ---------------------------------------------------------------- jobs / IO
def read_jobs(path):
    jobs = []
    with open(path, encoding="utf-8-sig") as f:
        for ln in f:
            for u in re.findall(r"https?://[^\s,]+", ln):
                if any(k in urlparse(u).netloc.lower() for k in MEGAMAX_HOSTS):
                    label = ln.split(" , ")[0].strip() or f"job{len(jobs) + 1}"
                    jobs.append((label, u))
                    break
    return jobs


def done_labels(path):
    if not os.path.exists(path):
        return set()
    with open(path, encoding="utf-8-sig") as f:
        return {ln.replace("\ufeff", "").split(" , ")[0].strip() for ln in f if " , " in ln}


def safe_name(s):
    return re.sub(r"[^\w\-]+", "_", s, flags=re.UNICODE).strip("_") or "video"


def launch(p):
    global UA, CTX, BROWSER_THREAD
    profile = os.path.join(os.path.dirname(os.path.abspath(__file__)), "megamax_profile")
    try:
        ctx = p.chromium.launch_persistent_context(profile, channel="chrome", headless=HEADLESS,
                                                args=["--disable-blink-features=AutomationControlled"],
                                                ignore_default_args=["--enable-automation"])
    except Exception:
        ctx = p.chromium.launch_persistent_context(profile, headless=HEADLESS,
                                                   args=["--disable-blink-features=AutomationControlled"],
                                                   ignore_default_args=["--enable-automation"])
    page = ctx.pages[0] if ctx.pages else ctx.new_page()
    ctx.add_init_script(INIT_JS)
    CTX, BROWSER_THREAD = ctx, threading.current_thread()
    try:
        UA = page.evaluate("navigator.userAgent") or UA   # same identity for the scripted checks and downloads
    except Exception:
        pass

    def route(r):
        req = r.request
        host = urlparse(req.url).netloc.lower()
        ad = any(k in host for k in BLOCK_HOSTS)
        try:
            if ad and req.is_navigation_request() and req.frame.parent_frame is None:
                return r.fulfill(status=204, body="")  # an ad tried to take over the tab: stay on the page
        except Exception:
            pass
        if ad and BLOCK_ADS:
            return r.abort()
        return r.continue_()
    ctx.route("**/*", route)

    def on_request(rq):
        try:
            if DEBUG and rq.resource_type not in ("image", "font", "stylesheet"):
                DEBUG_REQS.append(f"{rq.resource_type} {rq.url}")
            if is_media(rq.url):
                ref = rq.headers.get("referer") or rq.frame.url
                CAUGHT.setdefault(rq.url, {"referer": ref})
        except Exception:
            pass

    def on_response(resp):
        # Like a download extension: any playlist / video the page receives, whatever its URL or Content-Type says
        try:
            rq = resp.request
            ct = (resp.headers.get("content-type") or "").lower()
            ref = rq.frame.url
            if rq.resource_type in ("image", "font", "stylesheet") or ct.startswith(("image/", "font/", "audio/mp2t", "video/mp2t")):
                return
            if ct.startswith(("video/mp4", "video/webm", "video/x-matroska")) or rq.resource_type == "media":
                CAUGHT.setdefault(resp.url, {"referer": ref})
                return
            if int(resp.headers.get("content-length") or 0) > 600_000:
                return
            if ct and not any(k in ct for k in ("text", "json", "javascript", "octet", "xml", "mpegurl", "x-")):
                return
            body = resp.text()
            if body.lstrip().startswith("#EXTM3U"):
                CAUGHT.setdefault(resp.url, {"referer": ref})["body"] = body[:300000]
                return
            for u in find_media(body, resp.url):
                if is_media(u):
                    CAUGHT.setdefault(u, {"referer": ref})
        except Exception:
            pass

    def on_new_page(pg):
        if pg is not page:  # close ad popups
            try:
                pg.close()
            except Exception:
                pass

    ctx.on("request", on_request)
    ctx.on("response", on_response)
    ctx.on("page", on_new_page)
    page.on("dialog", lambda d: d.dismiss())
    return ctx, page


def parse_urls(text):
    # Links may be separated by commas, spaces or new lines
    return [u for u in re.split(r"[,\s]+", text.strip()) if u.lower().startswith("http")]


def write_lines(path, label, results):
    enc = "utf-8" if os.path.exists(path) else "utf-8-sig"  # BOM only once, at the top
    with open(path, "a", encoding=enc) as f:
        for r in results:
            f.write(f"{label} , {r['host']} , {r['url']}\n")


def dl_task(job, best):
    t0 = time.time()
    print(f"   [{job['label']}] downloading from {best['host']} ...")
    ok = download(best["url"], best["referer"], job["dest"], show=(PARALLEL == 1), kind=best.get("kind"))
    if ok:
        mb = os.path.getsize(job["dest"]) / 1e6
        dt = max(time.time() - t0, 0.001)
        print(f"   [{job['label']}] done: {mb:.0f} MB in {dt:.0f}s ({mb / dt:.1f} MB/s) -> {job['dest']}")
    else:
        print(f"   [{job['label']}] download from {best['host']} failed")
    return ok


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    want_all = "--all" in sys.argv
    raw = " ".join(args).strip() if args else input("Megamax URL(s) separated by comma (or a txt file): ").strip()
    if not raw:
        return

    batch = os.path.isfile(raw)
    if batch:
        jobs = read_jobs(raw)
        out_path = os.path.splitext(raw)[0] + "_m3u8.txt"
        default_prefix = safe_name(os.path.splitext(os.path.basename(raw))[0])
    else:
        start = opt("start", 1)
        jobs = [(f"حلقة {start + i}", u) for i, u in enumerate(parse_urls(raw))]
        out_path, default_prefix = "megamax_links.txt", "video"
    if not jobs:
        sys.exit("No Megamax/share4max links found.")

    do_dl = "--download" in sys.argv
    if not do_dl and "--no-download" not in sys.argv:
        do_dl = input("Download the episodes as MP4 too? [y/N]: ").strip().lower() == "y"
    prefix = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--name=")), None)
    if do_dl and prefix is None:
        prefix = safe_name(input(f"File name prefix [{default_prefix}]: ").strip() or default_prefix)

    skip = done_labels(out_path) if batch else set()
    queue = []
    for label, url in jobs:
        if label in skip:
            print(f"{label}: already saved, skipping")
            continue
        dest = None
        if do_dl:
            fname = f"{prefix}.mp4" if len(jobs) == 1 and not batch else f"{prefix}_{safe_name(label)}.mp4"
            dest = os.path.join("downloads", fname)
            if os.path.exists(dest) and os.path.getsize(dest) > 0:
                print(f"{label}: {dest} already exists, skipping")
                continue
        queue.append({"label": label, "url": url, "dest": dest, "tried": set()})

    boost_system()
    summary = {"ok": [], "no_link": [], "dl_failed": []}
    all_results = []
    with sync_playwright() as p:
        ctx, page = launch(p)
        pool = ThreadPoolExecutor(max_workers=PARALLEL) if do_dl else None
        try:
            for rnd in range(1, MAX_ROUNDS + 1):
                if not queue:
                    break
                if rnd > 1:
                    print(f"\n=== Retry round {rnd}: {len(queue)} job(s), using other servers ===")
                futures = []
                for job in queue:
                    print(f"\n{job['label']}: {job['url']}")
                    res = grab(page, job["url"], want_all, job["tried"])
                    if not res:
                        print("   no link captured")
                        summary["no_link"].append(job["label"])
                        continue
                    for r in res:
                        r["label"] = job["label"]
                    all_results += res
                    if not do_dl:
                        write_lines(out_path, job["label"], res)
                        summary["ok"].append(job["label"])
                    else:  # download runs in the background while the next episode is being captured
                        futures.append((job, res, pool.submit(dl_task, job, res[0])))
                queue = []
                for job, res, fut in futures:
                    if fut.result():
                        write_lines(out_path, job["label"], res[:1])
                        summary["ok"].append(job["label"])
                    else:
                        job["tried"].add(res[0]["host"])
                        queue.append(job)
            summary["dl_failed"] = [j["label"] for j in queue]
        except KeyboardInterrupt:
            print("\nStopped.")
        finally:
            if pool:
                pool.shutdown(wait=False, cancel_futures=True)
            ctx.close()

    print("\n==== Summary ====")
    print("OK:", ", ".join(summary["ok"]) or "-")
    if summary["no_link"]:
        print("No link captured:", ", ".join(summary["no_link"]))
    if summary["dl_failed"]:
        print("Download failed on every server:", ", ".join(summary["dl_failed"]))
    if all_results:
        with open(out_path + ".json", "w", encoding="utf-8") as f:
            json.dump(all_results, f, ensure_ascii=False, indent=1)
        print(f"Links saved to {out_path} (referers in {out_path}.json)")


if __name__ == "__main__":
    main()
