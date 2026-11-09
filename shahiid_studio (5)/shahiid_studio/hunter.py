# hunter.py - ONE standalone tool for Shahiid / EgyDead / AnimeZid / TopCinema / Animerco (+ movie categories)
# Paste ANY link (home / series / seasons / season / episode / movies category). Output: downloads/<prefix>/<season>/<episode>.mp4
# Usage: py hunter.py [URL] [--download] [--name=Prefix] [--seasons=1,3] [--from=N] [--to=M] [--skip=3,7-9] [--prefer=megamax] [--avoid=mixdrop,dood]
#                      [--out=downloads] [--workers=64] [--parallel=2] [--min-minutes=18] [--debug] [--block-ads]
# Needs: pip install requests playwright  +  py -m playwright install chromium  +  ffmpeg in PATH
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
from urllib.parse import parse_qs, unquote, urljoin, urlparse

try:
    import requests
except ImportError:
    sys.exit("pip install requests")
try:
    from playwright.sync_api import sync_playwright
except ImportError:
    sys.exit("Run first:  py -m pip install requests playwright   then   py -m playwright install chromium")

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



# ---------------------------------------------------------------- hunter engine
EMBEDS = []   # sub-frame document requests seen after a server click (fed by feed())
AD_HOSTS = BLOCK_HOSTS + ("facebook.com", "twitter.com", "t.me", "instagram.com", "youtube.com", "tiktok.com")
SERVER_RX = (r"megamax|vidtube|yourupload|videa|sendvid|streamlare|mega\b|sibnet|vidmoly|4meplayer|michi|google|\bok\b|kraken|streamhg|turbovid|vidhls|leech|earnvids|streamruby|"
             r"mixdrop|dood|uqload|voe|filemoon|streamwish|vidhide|lulustream|streamtape|mp4upload|okru|ok\.ru|vidoza|upstream|hgcloud|vkvideo")
SITE_NAMES = ("كرتوني", "ايجي ديد", "إيجي ديد", "توب سينما", "أنمي زد", "انمي زد", "Shahiid Anime", "Animerco", "AnimeZid", "EgyDead", "TopCinema")

JS_LINKS = r"""() => {
  const n = s => (s || '').trim().replace(/\s+/g, ' ');
  return [...document.querySelectorAll('a[href]')].map(a => {
    const h = a.querySelector('h1,h2,h3,h4,h5,h6,strong,b'), img = a.querySelector('img');
    return {href: a.href, raw: a.getAttribute('href') || '', text: n(a.innerText), title: n(a.title),
            head: h ? n(h.innerText) : '', alt: img ? n(img.alt) : '', hasimg: !!img};
  });
}"""
# "مواسم المسلسل" block only (EgyDead): the other seasons of THIS series, not the related-series list that follows it
JS_SERIES = r"""() => {
  const heads = [...document.querySelectorAll('h1,h2,h3,h4,h5,h6')];
  const h = heads.find(x => (x.textContent || '').includes('مواسم المسلسل'));
  if (!h) return null;
  const nxt = heads.find(x => x !== h && (h.compareDocumentPosition(x) & Node.DOCUMENT_POSITION_FOLLOWING));
  const n = s => (s || '').trim().replace(/\s+/g, ' ');
  return [...document.querySelectorAll('a[href]')].filter(a => (h.compareDocumentPosition(a) & Node.DOCUMENT_POSITION_FOLLOWING) &&
    (!nxt || (nxt.compareDocumentPosition(a) & Node.DOCUMENT_POSITION_PRECEDING)))
    .map(a => ({href: a.href, raw: a.getAttribute('href') || '', text: n(a.innerText), title: n(a.title), head: '', alt: '', hasimg: false}));
}"""
# Server buttons of the WATCH area: explicit server containers first, then short labels that are known host names.
JS_SERVERS = r"""(a) => {
  const re = new RegExp(a.rx, 'i'), bad = /جارٍ|loading|اختر|السيرفر الحالي|select|choose|تحميل|download|share|مشاركة|إبلاغ|report|login|تسجيل/i;
  const qual = /^[\w.\-]+\s+(?:FHD|HD|SD|4K|1080p?|720p?|480p?|360p?)$/i;
  document.querySelectorAll('[data-hx]').forEach(e => { delete e.dataset.hx; });
  const n = s => (s || '').trim().replace(/\s+/g, ' ');
  const first = el => n((el.innerText || '').split('\n')[0]);
  const dl = [...document.querySelectorAll('h1,h2,h3,h4,h5')].find(h => /سيرفرات التحميل|روابط التحميل/.test(h.textContent || ''));
  const clickable = el => !!el.closest('li, a, button, [role="tab"], [onclick], [tabindex]') || getComputedStyle(el).cursor === 'pointer';
  const rows = new Map();
  const add = (el, name) => {
    const row = el.closest('li, a, button, [role="tab"]') || el, r = row.getBoundingClientRect();
    if (!name || name.length > 30 || bad.test(name) || row.closest('nav, header, footer') || !(r.width > 0 && r.height > 0)) return;
    if (dl && (dl.compareDocumentPosition(row) & Node.DOCUMENT_POSITION_FOLLOWING)) return;
    const key = name.toLowerCase(), c = clickable(el), old = rows.get(key);
    if (!old || (c && !old.c)) rows.set(key, {row, name, c});   // a clickable button beats a plain label with the same name
  };
  document.querySelectorAll('[data-server],[data-embed],[class*="server" i] li,[class*="server" i] a,[class*="server" i] button,[id*="server" i] li,[id*="server" i] a,[id*="server" i] button')
    .forEach(el => add(el, first(el) || n(el.getAttribute('data-name') || el.title)));
  document.querySelectorAll('body *').forEach(el => {
    const t = first(el);
    if (!t || t.length > 30 || [...el.children].some(c => first(c) === t)) return;
    if ((re.test(t) && t.length <= 25) || qual.test(t)) add(el, t);
  });
  return [...rows.values()].map((r, i) => { r.row.dataset.hx = String(i); return {idx: i, name: r.name}; });
}"""
JS_IFRAMES = r"""() => [...document.querySelectorAll('iframe')].map(f => f.src || f.getAttribute('data-src') || '').filter(Boolean)"""


# ---------------------------------------------------------------- small helpers
def safe_eval(page, js, default=None, arg=None, tries=6):
    # Retry because the page may redirect/reload while we evaluate
    for _ in range(tries):
        try:
            return page.evaluate(js, arg) if arg is not None else page.evaluate(js)
        except Exception as e:
            if "context was destroyed" in str(e) or "navigation" in str(e).lower():
                page.wait_for_timeout(1500)
                continue
            raise
    return default


def norm_url(u):
    import html as _h
    u = _h.unescape(u or "").strip()
    return "https:" + u if u.startswith("//") else u


def is_embed(u):
    if not u or u.startswith(("about:", "javascript:", "data:", "blob:", "chrome")):
        return False
    host = urlparse(u).netloc.lower()
    if not host or any(k in host for k in AD_HOSTS):
        return False
    return "recaptcha" not in u and "disqus" not in u


def safe_filename(name, limit=150):
    s = re.sub(r'[<>:"/\\|?*\x00-\x1f]', " ", name or "")
    s = re.sub(r"\s+", " ", s).strip(" .")
    return s[:limit].rstrip(" .") or "video"


def clean_title(t):
    t = re.split(r"\s[-|–—]\s", t or "")[0]
    m = re.search(r"(?:الحلقة|حلقة)\s*\d+\s*من\s+(.+)$", t)   # "الحلقة 1 من دكتور ستون"
    t = m.group(1) if m else t
    t = re.sub(r"^\s*شاهد\s+", "", t)
    for s in SITE_NAMES:
        t = t.replace(s, "")
    t = re.sub(r"\b(?:مدبلج[ةا]?|مترجم[ةا]?|كامل[ةا]?|اونلاين|فيديوهات|مشاهدة|تحميل)\b", " ", t)
    t = re.sub(r"\s*(?:الحلقة|حلقة|episode)\s*\d+.*$", "", t, flags=re.I)
    t = re.sub(r"^\s*(?:انمي|أنمي|مسلسل|فيلم)\s+", "", t)
    return re.sub(r"\s+", " ", t).strip() or "video"


ORDINALS = {"الاول": 1, "الأول": 1, "الثاني": 2, "الثالث": 3, "الرابع": 4, "الخامس": 5, "السادس": 6, "السابع": 7, "الثامن": 8, "التاسع": 9, "العاشر": 10}


def explicit_season(text):
    # "الموسم 2" / "موسم 2" / "الجزء الثاني" / "Season 2" / "/season/2" / "-s02-" -> "الموسم 2"; None when the text says nothing
    t = unquote(text or "")
    m = re.search(r"(?:الموسم|موسم|الجزء|جزء|season|part)[\s\-_/]*(\d+)", t, re.I) or re.search(r"-s(\d{1,2})(?:-|/|$)", t, re.I)
    if m:
        return f"الموسم {int(m.group(1))}"
    m = re.search(r"(?:الموسم|موسم|الجزء|جزء)[\s\-_]+(" + "|".join(ORDINALS) + ")", t)
    return f"الموسم {ORDINALS[m.group(1)]}" if m else None


def season_label(text, idx=1):
    return explicit_season(text) or f"الموسم {idx}"


def mv_dur(text):
    # "1:53:10" / "07:02" even when the page glues it to the title ("فيلم موانا1:53:10")
    m = re.search(r"(?<![\d:])(\d{1,2}):(\d{2}):(\d{2})(?![\d:])", text or "")
    if m:
        return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + int(m.group(3))
    m = re.search(r"(?<![\d:])(\d{1,2}):(\d{2})(?![\d:])", text or "")
    return int(m.group(1)) * 60 + int(m.group(2)) if m else 0


def dump_page(page, tag):
    # Always leave evidence when something could not be understood
    try:
        with open(f"debug_{tag}.html", "w", encoding="utf-8") as f:
            f.write(f"<!-- tab: {page.url} -->\n")
            for i, fr in enumerate(page.frames):
                f.write(f"\n<!-- FRAME {i}: {fr.url} -->\n{fr.content()}\n")
        print(f"   (saved debug_{tag}.html - tab: {page.url})")
    except Exception:
        pass


def page_key(u):
    pu = urlparse(u)
    path = re.sub(r"/page/\d+/?$", "", pu.path).rstrip("/")
    q = tuple(sorted((k, tuple(v)) for k, v in parse_qs(pu.query).items() if k not in ("page", "paged", "epp", "order", "sortby")))
    return (pu.netloc, path, q)


def collect_pages(page, parse, pager, extra=()):
    # parse(page) on the current page and on every further page (/page/N, ?page=N, ?epp=N, a /list/ page ...)
    orig = page.url
    items = parse(page)
    if not items and not extra:
        return items
    seen, visited, base, queue = {i["href"] for i in items}, {orig}, page_key(orig), list(extra)
    for _ in range(100):
        if not queue:
            queue = [h for h in (r["href"].split("#")[0] for r in (safe_eval(page, JS_LINKS, []) or []))
                     if pager.search(h) and page_key(h) == base and h not in visited][:1]
        if not queue:
            break
        u = queue.pop(0)
        if u in visited:
            continue
        visited.add(u)
        open_page(page, u)
        if u in extra:
            base = page_key(page.url)
        for i in parse(page):
            if i["href"] not in seen:
                seen.add(i["href"])
                items.append(i)
        print(f"   page {len(visited) - 1}: {len(items)} items so far")
    if len(visited) > 1:
        open_page(page, orig)
    return items


# ---------------------------------------------------------------- site adapters
class Site:
    key, hosts = "site", ()
    pager = re.compile(r"/page/\d+|[?&](?:page|paged|epp)=\d+")
    ep_num = re.compile(r"(?:الحلقة|حلقة|الحلقه|حلقه|episode|ep)[\s\-]*(\d+(?:\.\d+)?)", re.I)

    def match(self, url):
        return any(h in urlparse(url).netloc.lower() for h in self.hosts)

    def kind(self, url):
        return "unknown"

    def ep_candidate(self, r):
        return None

    def season_candidate(self, r):
        return None

    def card(self, r):
        return None

    def extra_pages(self, page):
        return []

    def series_link(self, page):
        return None

    def watch_urls(self, ep):
        return [ep["href"]]

    def pre_servers(self, page):
        return None

    def rows(self, page):
        return [r for r in (safe_eval(page, JS_LINKS, []) or []) if not r["raw"].startswith(("#", "javascript"))]

    def episodes(self, page):
        out, seen = [], set()
        for r in self.rows(page):
            c = self.ep_candidate(r)
            if c and c["href"] not in seen:
                seen.add(c["href"])
                out.append(c)
        return out

    def all_episodes(self, page):
        eps = collect_pages(page, self.episodes, self.pager, self.extra_pages(page))
        eps.sort(key=lambda e: float(e["num"]))
        return eps

    def seasons(self, page, rows=None):
        best = {}
        for r in (rows if rows is not None else self.rows(page)):
            c = self.season_candidate(r)
            if c and len(c["text"]) >= len(best.get(c["href"], {"text": ""})["text"]):
                best[c["href"]] = c
        return list(best.values())

    def listing(self, page):
        def parse(pg):
            out, seen = [], set()
            for r in self.rows(pg):
                c = self.card(r) if r["hasimg"] else None
                if c and c["href"] not in seen:
                    seen.add(c["href"])
                    out.append(c)
            return out
        return collect_pages(page, parse, self.pager)


class Shahiid(Site):
    key, hosts = "shahiid", ("shahiid-anime",)

    def kind(self, url):
        pu = urlparse(url)
        p = unquote(pu.path).rstrip("/")
        if re.search(r"/seasons\w*$", p) and "serie=" in pu.query:
            return "series"
        if re.search(r"/seasons\w*/[^/]+$", p):
            return "season"
        if re.search(r"/episodes\w*/[^/]+$", p):
            return "episode"
        return "series" if re.search(r"/series\w*/[^/]+$", p) else "list"

    def ep_candidate(self, r):
        if not re.search(r"/episodes\w*/[^/]+/?$", unquote(urlparse(r["href"]).path)) or r["text"].startswith(("مشاهدة", "تحميل")):
            return None
        m = self.ep_num.search(r["text"]) or self.ep_num.search(r["title"])
        return {"href": r["href"].split("#")[0], "title": r["text"][:80], "num": m.group(1)} if m else None

    def season_candidate(self, r):
        p = unquote(urlparse(r["href"]).path).rstrip("/")
        t = r["title"] or r["text"]
        if re.search(r"/seasons\w*/[^/]+$", p) and t and not t.isdigit():
            return {"href": r["href"].split("#")[0].split("?")[0], "text": t[:80]}
        return None

    def card(self, r):
        p = unquote(urlparse(r["href"]).path).rstrip("/")
        t = r["head"] or r["title"] or r["alt"] or r["text"]
        if t and re.search(r"/(?:series|seasons)\w*/[^/]+$", p):
            return {"href": r["href"].split("#")[0], "title": t[:150], "kind": "series"}
        return None

    def pre_servers(self, page):
        # servers sit under the "HTML" heading of the episode page
        try:
            loc = page.locator("xpath=//*[self::h2 or self::h3 or self::h4 or self::h5 or self::h6][normalize-space()='HTML']/following::ul[1]/li")
            out = []
            for i in range(loc.count()):
                name = loc.nth(i).inner_text(timeout=2000).strip().replace("\n", " ")
                if name and len(name) < 40:
                    out.append((loc.nth(i), name))
            return out
        except Exception:
            return None


class EgyDead(Site):
    key, hosts = "egydead", ("egydead",)
    reserved = {"category", "tag", "page", "seasons", "episodes", "series", "serie", "wp-content", "wp-json", "author", "feed", "genre",
                "year", "search", "login", "register", "contact", "dmca", "privacy", "movies", "animes"}

    def kind(self, url):
        p = unquote(urlparse(url).path).rstrip("/")
        if re.fullmatch(r"/seasons/[^/]+", p):
            return "season"
        if re.fullmatch(r"/episodes/[^/]+(?:/watch)?", p):
            return "episode"
        if re.fullmatch(r"/(?:serie|series)/[^/]+", p):
            return "series"
        if not p or p.startswith("/category"):
            return "list"
        return "movie" if p.count("/") == 1 else "unknown"

    def ep_candidate(self, r):
        m = re.fullmatch(r"(?:حلقه|حلقة|الحلقة)\s*(\d+(?:\.\d+)?)", r["text"])
        if not m or "/episodes/" not in urlparse(r["href"]).path:
            return None
        return {"href": re.sub(r"/watch/?$", "/", r["href"].split("#")[0]), "title": r["title"] or r["text"], "num": m.group(1)}

    def season_candidate(self, r):
        if re.fullmatch(r"/seasons/[^/]+", urlparse(r["href"]).path.rstrip("/")) and (r["title"] or r["text"]):
            return {"href": r["href"].split("#")[0], "text": (r["title"] or r["text"])[:80]}
        return None

    def seasons(self, page, rows=None):
        scoped = safe_eval(page, JS_SERIES, None)
        return Site.seasons(self, page, [r for r in scoped if not r["raw"].startswith("#")] if scoped is not None else None)

    def card(self, r):
        u = urlparse(r["href"])
        segs = [unquote(x) for x in u.path.strip("/").split("/") if x]
        t = r["head"] or r["title"] or r["alt"] or r["text"]
        if not t or u.netloc != "" and "egydead" not in u.netloc:
            return None
        href = r["href"].split("#")[0].split("?")[0]
        if len(segs) == 2 and segs[0] in ("seasons", "serie", "series"):
            return {"href": href, "title": t[:150], "kind": "series"}
        if len(segs) == 1 and segs[0] not in self.reserved:
            return {"href": href, "title": t[:150], "kind": "movie", "dur": mv_dur(r["text"])}
        return None

    def watch_urls(self, ep):
        return [ep["href"].rstrip("/") + "/watch/", ep["href"]]


class AnimeZid(Site):
    key, hosts = "animezid", ("animezid",)
    pager = re.compile(r"[?&]page=\d+")

    @staticmethod
    def vid(href):
        return (parse_qs(urlparse(href).query).get("vid") or [""])[0]

    def kind(self, url):
        pu = urlparse(url)
        p = unquote(pu.path).rstrip("/")
        if "watch.php" in p or "play.php" in p:
            return "episode"
        if re.fullmatch(r"/series/[^/]+/season/\d+", p):
            return "season"
        return "series" if re.fullmatch(r"/series/[^/]+", p) else "list"

    def ep_candidate(self, r):
        u, vid = urlparse(r["href"]), self.vid(r["href"])
        if "watch.php" not in u.path or not vid or "التالية" in r["text"] or "السابقة" in r["text"]:
            return None
        m = self.ep_num.search(r["text"]) or self.ep_num.search(r["title"])
        return {"href": f"{u.scheme}://{u.netloc}/watch.php?vid={vid}", "title": r["title"] or r["text"][:60], "num": m.group(1)} if m else None

    def season_candidate(self, r):
        href = r["href"].split("?")[0].split("#")[0]
        m = re.fullmatch(r"/series/[^/]+/season/(\d+)", unquote(urlparse(href).path).rstrip("/"))
        return {"href": href, "text": (r["text"] or r["title"])[:80], "n": int(m.group(1))} if m and (r["text"] or r["title"]) else None

    def card(self, r):
        u, vid = urlparse(r["href"]), self.vid(r["href"])
        t = r["head"] or r["alt"] or r["title"]
        if not t:
            return None
        if "watch.php" in u.path and vid:
            return {"href": f"{u.scheme}://{u.netloc}/watch.php?vid={vid}", "title": t[:150], "kind": "movie", "dur": mv_dur(r["text"])}
        if re.fullmatch(r"/series/[^/]+", unquote(u.path).rstrip("/")):
            return {"href": r["href"].split("#")[0], "title": t[:150], "kind": "series"}
        return None

    def watch_urls(self, ep):
        u = urlparse(ep["href"])
        return [f"{u.scheme}://{u.netloc}/play.php?vid={self.vid(ep['href'])}"]


AZ_CATS = [("كل الأفلام", "movies"), ("أحدث الأفلام المضافة", "new-movies"), ("ديزني بالمصري", "disney-masr"), ("أفلام انيميشن مدبلجة", "dubbed-animation"),
           ("أفلام انيميشن مترجمة", "subbed-animation"), ("أفلام أجنبية", "english-movies"), ("أفلام لايف اكشن مدبلجة", "dubbed-movies"),
           ("ديزني بالعربية الفصحى", "disney-arabic"), ("أفلام رأس السنة", "new-year-movies")]


class Cartoony(Site):
    # cartoony.net: /watch/<series> lists EVERY episode on one page (no seasons); /watch/<series>/<episode> plays it with the site's
    # own player (no server list). The pages are rendered by JavaScript, so lists are polled until they appear.
    key, hosts = "cartoony", ("cartoony",)

    @staticmethod
    def segs(url):
        return [x for x in urlparse(url).path.strip("/").split("/") if x]

    def kind(self, url):
        s = self.segs(url)
        if s[:1] == ["watch"] and len(s) == 2:
            return "season"
        return "episode" if s[:1] == ["watch"] and len(s) == 3 else "list"

    def ep_candidate(self, r):
        s = self.segs(r["href"])
        if len(s) != 3 or s[0] != "watch" or not s[1].isdigit() or not s[2].isdigit():
            return None
        m = re.match(r"\s*(\d+)\s*[.\-)]", r["text"]) or re.search(r"(?:الحلقة|حلقة)\s*(\d+)", r["title"] or r["text"])
        title = re.sub(r"^\s*\d+\s*[.\-)]\s*", "", r["text"]) or r["title"]
        return {"href": r["href"].split("#")[0].split("?")[0], "title": title[:80], "num": m.group(1) if m else None}

    def episodes(self, page):
        end = time.time() + 8
        while True:
            out = Site.episodes(self, page)
            if out or time.time() >= end:
                break
            page.wait_for_timeout(700)
        for i, e in enumerate(out, 1):   # the list is in order: use the position when the number is not printed
            if not e["num"]:
                e["num"] = str(i)
        return out

    def card(self, r):
        s = self.segs(r["href"])
        t = r["head"] or r["title"] or r["alt"] or r["text"]
        if len(s) == 2 and s[0] == "watch" and s[1].isdigit() and t:
            return {"href": r["href"].split("#")[0], "title": t[:150], "kind": "series"}
        return None

    def series_link(self, page):
        # an episode page links back to "جميع حلقات <series>"
        for r in self.rows(page):
            s = self.segs(r["href"])
            if len(s) == 2 and s[0] == "watch" and s[1].isdigit():
                return r["href"].split("#")[0]
        return None


class TopCinema(Site):
    key, hosts = "topcinema", ("topcinema",)
    ep_path = re.compile(r"(?:الحلقة|حلقة)[\s\-]*(\d+(?:\.\d+)?)")

    def kind(self, url):
        segs = [unquote(x) for x in urlparse(url).path.strip("/").split("/") if x]
        if segs[-1:] in (["watch"], ["download"]):
            return "episode"
        if segs[:1] == ["series"] and len(segs) >= 2:
            return "season"
        if len(segs) == 1 and "الحلقة" in segs[0]:
            return "episode"
        return "movie" if len(segs) == 1 and "فيلم" in segs[0] else "list"

    def ep_candidate(self, r):
        path = unquote(urlparse(r["href"]).path)
        if path.startswith("/series/") or "الحلقة" not in path:
            return None
        m = self.ep_path.search(path) or self.ep_path.search(r["title"]) or self.ep_path.search(r["text"])
        href = re.sub(r"/(?:watch|download)/?$", "/", r["href"].split("#")[0])
        return {"href": href, "title": r["title"] or r["text"][:60], "num": m.group(1)} if m else None

    def season_candidate(self, r):
        if urlparse(r["href"]).path.startswith("/series/") and re.match(r"^\s*الموسم\s*\d", r["text"]):
            return {"href": r["href"].split("#")[0], "text": r["text"][:80]}
        return None

    def card(self, r):
        path = unquote(urlparse(r["href"]).path)
        segs = [x for x in path.strip("/").split("/") if x]
        t = r["head"] or r["title"] or r["alt"] or r["text"]
        if not t:
            return None
        if segs[:1] == ["series"] and len(segs) == 2:
            return {"href": r["href"].split("#")[0], "title": t[:150], "kind": "series"}
        if len(segs) == 1 and "فيلم" in segs[0]:
            return {"href": r["href"].split("#")[0], "title": t[:150], "kind": "movie", "dur": mv_dur(r["text"])}
        return None

    def extra_pages(self, page):
        return [r["href"] for r in self.rows(page) if urlparse(r["href"]).path.rstrip("/").endswith("/list")][:1]

    def watch_urls(self, ep):
        return [ep["href"].rstrip("/") + "/watch/", ep["href"]]


class Animerco(Site):
    key, hosts = "animerco", ("animerco",)

    def kind(self, url):
        p = unquote(urlparse(url).path).rstrip("/")
        if re.fullmatch(r"/animes/[^/]+", p):
            return "series"
        if re.fullmatch(r"/seasons?/[^/]+", p):
            return "season"
        if re.fullmatch(r"/episodes?/[^/]+", p):
            return "episode"
        return "movie" if re.fullmatch(r"/movies?/[^/]+", p) else "list"

    @staticmethod
    def num(text, title, href):
        for src in (title, text):
            m = Site.ep_num.search(src or "")
            if m:
                return m.group(1)
        m = re.search(r"(?:episode-|ep-|-|x)(\d+(?:\.\d+)?)/?$", unquote(urlparse(href).path), re.I)
        return m.group(1) if m else None

    def ep_candidate(self, r):
        href = r["href"].split("#")[0]
        if not re.fullmatch(r"/episodes?/[^/]+", unquote(urlparse(href).path).rstrip("/")):
            return None
        n = self.num(r["text"], r["title"], href)
        return {"href": href, "title": r["title"] or r["text"][:60], "num": n} if n else None

    def season_candidate(self, r):
        href = r["href"].split("#")[0].split("?")[0]
        if re.fullmatch(r"/seasons?/[^/]+", unquote(urlparse(href).path).rstrip("/")) and (r["text"] or r["title"]):
            return {"href": href, "text": (r["title"] or r["text"])[:80]}
        return None

    def card(self, r):
        p = unquote(urlparse(r["href"]).path).rstrip("/")
        t = r["head"] or r["title"] or r["alt"] or r["text"]
        if t and re.fullmatch(r"/animes/[^/]+", p):
            return {"href": r["href"].split("#")[0], "title": t[:150], "kind": "series"}
        if t and re.fullmatch(r"/movies?/[^/]+", p):
            return {"href": r["href"].split("#")[0], "title": t[:150], "kind": "movie", "dur": mv_dur(r["text"])}
        return None


SITES = [Shahiid(), EgyDead(), AnimeZid(), TopCinema(), Animerco(), Cartoony()]


def site_for(url):
    return next((s for s in SITES if s.match(url)), None)


# ---------------------------------------------------------------- universal page understanding
def load(page, url, hint=None, idx=1):
    # -> {"kind": "episodes"|"seasons"|"list"|"movies"|"unknown", "items": [...], "siblings": [...], "name", "season", "url", "site"}
    open_page(page, url)
    site = site_for(page.url) or site_for(url)
    out = {"kind": "unknown", "items": [], "siblings": [], "name": clean_title(page.title()), "season": "", "url": page.url,
           "site": site.key if site else None}
    if not site:
        print("   this site is not supported (Shahiid, EgyDead, AnimeZid, TopCinema, Animerco)")
        return out
    kind = site.kind(page.url)
    if site.key == "animezid" and urlparse(page.url).path.rstrip("/").endswith("category.php") and "cat=" not in page.url:
        o = urlparse(page.url)
        out.update(kind="list", items=[{"href": f"{o.scheme}://{o.netloc}/category.php?cat={c}", "title": n, "kind": "series"} for n, c in AZ_CATS])
        return finish(out)
    if kind == "list":
        cards = site.listing(page)
        if cards:
            series = [c for c in cards if c["kind"] == "series"]
            movies = [c for c in cards if c["kind"] == "movie"]
            out.update(kind="list" if series else "movies", items=series or movies)
            if not series:
                for n, m in enumerate(movies, 1):
                    m["num"] = str(n)
            return finish(out)
    sibs = site.seasons(page)
    if kind == "series" and sibs:  # a series page lists its seasons (its "latest episodes" box is not the season)
        out.update(kind="seasons", items=sibs)
        return finish(out)
    eps = site.all_episodes(page) if kind != "movie" else []
    if eps:
        cur = urlparse(page.url).path.rstrip("/")
        mine = next((s["text"] for s in sibs if urlparse(s["href"]).path.rstrip("/") == cur and len(s["text"]) > 2), "")
        out.update(kind="episodes", items=eps, season=(explicit_season(hint) or explicit_season(urlparse(page.url).path) or explicit_season(mine)
                                                        or explicit_season(page.title()) or f"الموسم {idx}"),
                   siblings=[s for s in sibs if urlparse(s["href"]).path.rstrip("/") != cur])
        return finish(out)
    if kind == "episode":
        up = site.series_link(page)
        if up and up.rstrip("/") != page.url.rstrip("/"):
            return load(page, up, hint, idx)
    if kind in ("episode", "movie"):
        out.update(kind="movies" if kind == "movie" else "episodes", season="" if kind == "movie" else season_label(hint or page.title(), idx),
                   items=[{"href": re.sub(r"/(?:watch|download)/?$", "/", page.url.split("#")[0]), "title": clean_title(page.title()), "num": "1", "dur": 0}])
        return finish(out)
    if sibs:
        out.update(kind="seasons", items=sibs)
        return finish(out)
    cards = site.listing(page)
    if cards:
        out.update(kind="list" if any(c["kind"] == "series" for c in cards) else "movies", items=cards)
        for n, m in enumerate(out["items"], 1):
            m["num"] = str(n)
        return finish(out)
    if safe_eval(page, "() => !!document.querySelector('video, .jwplayer, .video-js, .plyr, iframe')", False):
        out.update(kind="movies", items=[{"href": page.url.split("#")[0], "title": clean_title(page.title()), "num": "1", "dur": 0}])
        return finish(out)   # nothing but a player: one video
    print("   could not understand this page")
    dump_page(page, "page")
    return out


def finish(out):
    print(f"   understood: {out['kind']} ({len(out['items'])} item(s)) on {out['site']}")
    return out


# ---------------------------------------------------------------- servers of ONE episode
def feed(r):  # request listener: sub-frame documents (embed pages) are remembered
    try:
        if r.resource_type == "document" and r.frame.parent_frame is not None:
            EMBEDS.append(r.url)
    except Exception:
        pass


def generic_servers(page):
    try:
        found = page.evaluate(JS_SERVERS, {"rx": SERVER_RX})
    except Exception:
        return []
    uniq = {}
    for r in found:
        uniq.setdefault(r["name"].lower(), r)
    return [(page.locator(f'[data-hx="{r["idx"]}"]').first, r["name"]) for r in uniq.values()]


def find_servers(page, seconds=10, pre=None):
    end = time.time() + seconds
    while True:
        items = (pre(page) if pre else None) or generic_servers(page)
        if items or time.time() >= end:
            return items
        page.wait_for_timeout(700)


def press_overlay(page):
    # Many players show a big "click to play" cover and only then load the server list
    for pat in (r"اضغط هنا لتشغيل", r"تشغيل الحلقة", r"^\s*▶", r"^\s*(?:play|شغل|شاهد الآن|مشاهدة الآن)\s*$"):
        try:
            loc = page.get_by_text(re.compile(pat, re.I)).first
            if loc.count() == 0:
                continue
            try:
                loc.click(timeout=2500)
            except Exception:
                loc.dispatch_event("click")
            return True
        except Exception:
            continue
    for sel in (".vjs-big-play-button", ".jw-icon-display", ".plyr__control--overlaid", '[class*="play-btn" i]', '[class*="playbtn" i]', "#play"):
        try:
            loc = page.locator(sel).first
            if loc.count():
                loc.click(timeout=2000)
                return True
        except Exception:
            pass
    return False


def own_player(page):
    return bool(safe_eval(page, "() => !!document.querySelector('video, .jwplayer, .video-js, .plyr')", False))


def servers_on(page, pre=None):
    # list -> the page's own player -> press the cover/play button and look again -> an embedded player without a list ("auto")
    items = find_servers(page, 4, pre)
    if items:
        return items
    if own_player(page):
        return [(None, "page")]
    for _ in range(2):
        if press_overlay(page):
            page.wait_for_timeout(1500)
        items = find_servers(page, 8, pre)
        if items:
            return items
    if own_player(page):
        return [(None, "page")]
    ifr = [norm_url(x) for x in (safe_eval(page, JS_IFRAMES, []) or [])]
    return [(None, "auto")] if any(is_embed(x) for x in ifr) else []


def open_episode(page, site, ep):
    items = []
    for u in site.watch_urls(ep):
        open_page(page, u)
        items = servers_on(page, site.pre_servers)
        if items:
            return items
    try:  # last resort: the page's own "watch" button
        page.locator('a[href$="/watch/"], a[href*="play.php"], a:has-text("المشاهده"), a:has-text("مشاهدة")').first.click(timeout=4000)
        page.wait_for_timeout(1500)
        items = servers_on(page, site.pre_servers)
    except Exception:
        pass
    if not items:
        print("   no servers found on the watch page")
        dump_page(page, "servers")
    return items


def capture_embed(page, item, prev):
    # Press a server button and return the embed (iframe) URL that appears; press play once more if nothing shows
    before = {norm_url(s) for s in (safe_eval(page, JS_IFRAMES, []) or [])}
    EMBEDS.clear()
    if item is not None:
        try:
            item.click(timeout=6000)
        except Exception:
            try:   # something sits on top of the button (an overlay/ad): force it, then fire the event on the element itself
                item.click(force=True, timeout=3000)
            except Exception:
                try:
                    item.dispatch_event("click")
                except Exception as e:
                    print("      click failed:", str(e).splitlines()[0])
                    return None
    t0, cur = time.time(), None
    while time.time() - t0 < 12:
        page.wait_for_timeout(600)
        srcs = [norm_url(s) for s in (safe_eval(page, JS_IFRAMES, []) or [])]
        srcs = [s for s in srcs if is_embed(s)]
        changed = [s for s in srcs if s not in before and s != prev]
        if changed:
            return changed[0]
        net = [norm_url(u) for u in list(EMBEDS) if is_embed(norm_url(u)) and norm_url(u) != prev]
        if net:
            return net[0]
        cur = srcs[0] if srcs else cur
        if (prev is None or item is None) and cur and time.time() - t0 > 2.5:
            return cur  # the first server was already auto-loaded
    for _ in range(3):
        for fr in page.frames:
            try:
                fr.evaluate(JS_NUDGE)
            except Exception:
                pass
        page.wait_for_timeout(1500)
        srcs = [norm_url(x) for x in (safe_eval(page, JS_IFRAMES, []) or [])]
        srcs = [x for x in srcs if is_embed(x) and x != prev]
        if srcs:
            return srcs[0]
    return cur


def reg_domain(host):
    p = (host or "").lower().split(":")[0].split(".")
    return ".".join(p[-2:]) if len(p) >= 2 else ".".join(p)


def is_wrapper(embed, ep_href):
    # the platform's OWN player page (same site, or carrying a one-time signature): never open it on its own - work inside the page
    u = urlparse(embed)
    q = parse_qs(u.query)
    return reg_domain(u.netloc) == reg_domain(urlparse(ep_href).netloc) or any(k in q for k in ("pnonce", "sig", "exp", "token", "signature"))


def is_megamax(name, embed):
    return ("megamax" in name.lower() or any(k in embed for k in MEGAMAX_HOSTS)
            or bool(re.search(r"/iframe/[A-Za-z0-9]{8,}/?$", urlparse(embed).path)))


def resolve_episode(page, site, job, prefer=("megamax",), avoid=None):
    # Every episode has its own servers. Try them in preference/reliability order; ANY failure moves on to the next server.
    scope = f"outer:{site.key}"
    items = open_episode(page, site, job["ep"])
    names = [n for _, n in items]
    if not names:
        return None
    order = [n for n in rank_names(scope, names, tuple(prefer), avoid) if n not in job["bad"]]
    gone = [n for n in dict.fromkeys(names) if n not in order and n not in job["bad"]]
    if gone:
        print("   avoiding:", ", ".join(gone))
    print("   servers (trying order):", ", ".join(order) or "(none)")
    prev, dirty = None, False
    for name in order:
        try:
            if dirty:
                items, dirty = open_episode(page, site, job["ep"]), False
            loc = next((l for l, n in items if n == name), "x")
            if loc == "x":
                continue
            print(f"   server: {name}")
            CAUGHT.clear()
            BAD.clear()
            if name == "page":  # no server list: the page's own player
                press_overlay(page)
                link, ref = wait_media(page, 25)
                dirty = True
                rec, embed = ({"host": "page", "url": link, "referer": ref, "kind": KINDS.get(link)} if link else None), page.url
            else:
                embed = capture_embed(page, loc, prev)
                if not embed:
                    record(scope, name, False)
                    print("      no embed captured, next server")
                    continue
                prev = embed
                print(f"      embed: {embed}")
                wrapper, rec, res = is_wrapper(embed, job["ep"]["href"]), None, None
                if wrapper:
                    print("      (the platform's own player: working inside this page, not opening it)")
                dirty = True
                if is_megamax(name, embed) or rows_frame(page, 4) is not None:  # host list: pick a host, press play, Back, next host
                    res = grab_inpage(page, job["tried"])
                    if res is None and not wrapper:   # no usable window in the page: open a third-party Megamax window on its own
                        res = grab(page, embed, False, job["tried"])
                    rec = res[0] if res else None
                if rec is None and res != []:   # [] = every Megamax host already failed: do not wait again
                    link, ref = wait_media(page, 28)   # real play clicks inside the player, then whatever the page requests
                    if not link and not wrapper and not is_megamax(name, embed):
                        CAUGHT.clear()
                        BAD.clear()
                        open_page(page, embed)   # a third-party embed page may also work on its own
                        link, ref = wait_media(page, 25)
                    rec = {"host": name.lower(), "url": link, "referer": ref, "kind": KINDS.get(link)} if link else None
            if rec:
                record(scope, name, True)
                rec.update(server=name, embed=embed)
                return rec
            record(scope, name, False)
            print("      no usable m3u8 here, next server")
        except Exception as e:
            dirty = True
            record(scope, name, False)
            print(f"      {name} failed ({str(e).splitlines()[0]}), next server")
    return None


# ---------------------------------------------------------------- jobs, folders, rounds
def build_jobs(groups, prefix, root="downloads", do_dl=True, done=None, log=print):
    # groups: [{"season": "الموسم 1", "movies": False, "episodes": [{href,title,num,(dur)}]}]
    jobs = []
    for g in groups:
        season, movies, eps = g.get("season") or "", bool(g.get("movies")), g["episodes"]
        width = max([2] + [len(str(e["num"]).split(".")[0]) for e in eps])
        for e in eps:
            num = str(e["num"])
            if movies:
                label, fname, sub = e["title"], safe_filename(e["title"]), ()
            else:
                n = num.split(".")[0].zfill(width) + ("." + num.split(".")[1] if "." in num else "")
                label, fname, sub = f"{season} حلقة {num}".strip(), f"حلقة {n}", ((safe_filename(season),) if season else ())
            dest = os.path.join(root, safe_filename(prefix), *sub, fname + ".mp4") if do_dl else None
            if dest and os.path.exists(dest) and os.path.getsize(dest) > 0:
                log(f"{label}: already downloaded, skipping")
                continue
            if not do_dl and done and label in done:
                continue
            dur = e.get("dur") or 0
            jobs.append({"label": label, "ep": {"href": e["href"], "title": e.get("title", ""), "num": num}, "dest": dest,
                         "tried": set(), "bad": set(), "nolink": 0,
                         "min_seconds": max(90, 0.6 * dur) if movies and dur else None})
    return jobs


def run_jobs(page, jobs, slug, pool, prefer=("megamax",), avoid=None, cancel=lambda: False, on_result=None, dl=None):
    # Round 1 finds an m3u8 for every episode (downloads start in the background as links arrive). Anything that failed - no link,
    # a corrupt playlist, a broken download - goes back to its episode page and tries other servers in the next round.
    out_path, dl, lost = f"{slug}_m3u8.txt", dl or dl_task, []

    def ok(j, rec):
        write_lines(out_path, j["label"], [rec])
        if on_result:
            on_result(j, rec)

    for rnd in range(1, MAX_ROUNDS + 2):
        if not jobs or cancel():
            break
        if rnd > 1:
            print(f"\n=== Retry round {rnd}: {len(jobs)} item(s), other servers first ===")
        futs, failed = [], []
        for j in jobs:
            if cancel():
                break
            site = site_for(j["ep"]["href"])
            print(f"\n{j['label']}: {j['ep']['title']}")
            old = set_min_seconds(j["min_seconds"]) if j.get("min_seconds") else None
            try:
                rec = resolve_episode(page, site, j, prefer, avoid)
            finally:
                if old is not None:
                    set_min_seconds(old)
            if not rec:
                j["nolink"] += 1
                print("   no m3u8 from any server" + (" (will retry once more)" if j["nolink"] < 2 else ""))
                (failed if j["nolink"] < 2 else lost).append(j)
                continue
            write_lines(f"{slug}_embed.txt", j["label"], [{"host": rec["server"], "url": rec["embed"]}])
            if pool:
                futs.append((j, rec, pool.submit(dl, j, rec)))
            else:
                ok(j, rec)
                print(f"   saved: {rec['url']}")
        for j, rec, fut in futs:
            if fut.result():
                ok(j, rec)
            else:
                site = site_for(j["ep"]["href"])
                if is_megamax(rec["server"], rec["embed"]):
                    j["tried"].add(rec["host"])
                    record("megamax", rec["host"], False)
                else:
                    j["bad"].add(rec["server"])
                    record(f"outer:{site.key}", rec["server"], False)
                failed.append(j)
        jobs = failed
    return jobs + lost


# ---------------------------------------------------------------- terminal flow
def select_nums(nums, lo=None, hi=None, text=""):
    text = (text or "").strip().lower()
    if text and text != "all":
        want = set()
        for tok in re.split(r"[,\s]+", text):
            if re.fullmatch(r"\d+(\.\d+)?", tok):
                want.add(tok)
            elif re.fullmatch(r"\d+-\d+", tok):
                a, b = map(int, tok.split("-"))
                want.update(str(n) for n in range(a, b + 1))
        return [n for n in nums if n in want]
    return [n for n in nums if (lo is None or float(n) >= lo) and (hi is None or float(n) <= hi)]


def pick_many(count, text):
    text = (text or "").strip().lower()
    if not text or text == "all":
        return list(range(1, count + 1))
    out = []
    for tok in re.split(r"[,\s]+", text):
        m = re.fullmatch(r"(\d+)-(\d+)", tok)
        out += list(range(int(m.group(1)), int(m.group(2)) + 1)) if m else ([int(tok)] if tok.isdigit() else [])
    return [n for n in dict.fromkeys(out) if 1 <= n <= count]


def split_opt(name, default):
    raw = next((a.split("=", 1)[1] for a in sys.argv if a.startswith(f"--{name}=")), None)
    return [x.strip().lower() for x in (raw if raw is not None else default).split(",") if x.strip()]


def run_cli(page, url, do_dl, pool):
    prefer, avoid = split_opt("prefer", "megamax"), split_opt("avoid", ",".join(AVOID))
    AVOID[:] = avoid
    root = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--out=")), "downloads")
    lo, hi = opt("from", None), opt("to", None)
    skip_arg = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--skip=")), None)
    res = load(page, url)
    while res["kind"] == "list":  # a home/category page full of series: pick one
        print(f"\n{len(res['items'])} item(s):")
        for i, it in enumerate(res["items"], 1):
            print(f"  [{i:>3}] {it['title']}")
        raw = input("Choose a number: ").strip()
        if not (raw.isdigit() and 1 <= int(raw) <= len(res["items"])):
            return
        res = load(page, res["items"][int(raw) - 1]["href"])
    if res["kind"] == "unknown" or not res["items"]:
        print("Nothing to download from this page (see the debug_*.html file if one was saved).")
        return
    groups = []
    if res["kind"] == "seasons":
        print(f"\n{len(res['items'])} season(s):")
        for i, s in enumerate(res["items"], 1):
            print(f"  [{i}] {s['text']}")
        raw = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--seasons=")), None) or input("Seasons to download (all / 1,3 / 2-4) [all]: ")
        for n in pick_many(len(res["items"]), raw):
            s = res["items"][n - 1]
            r = load(page, s["href"], hint=s["text"], idx=n)
            if r["kind"] == "episodes":
                groups.append({"season": r["season"], "movies": False, "episodes": r["items"]})
        name = res["name"]
    else:
        movies = res["kind"] == "movies"
        groups.append({"season": res["season"], "movies": movies, "episodes": res["items"]})
        name = res["name"]
        if res["siblings"] and not movies:
            print("\nOther seasons of this series:")
            for i, s in enumerate(res["siblings"], 1):
                print(f"  [{i}] {s['text']}")
            raw = input("More seasons to include (all / 1,3 / Enter = none): ").strip()
            for n in pick_many(len(res["siblings"]), raw) if raw else []:
                s = res["siblings"][n - 1]
                r = load(page, s["href"], hint=s["text"], idx=n)
                if r["kind"] == "episodes":
                    groups.append({"season": r["season"], "movies": False, "episodes": r["items"]})
    for g in groups:  # episode range per season
        nums = [e["num"] for e in g["episodes"]]
        if g.get("movies"):
            for e in g["episodes"]:
                d = e.get("dur", 0)
                print(f"  [{e['num']:>3}] {e['title']}" + (f"   ({d // 3600}:{d % 3600 // 60:02d}:{d % 60:02d})" if d else ""))
        if lo is not None or hi is not None or skip_arg is not None:
            chosen = select_nums(nums, lo, hi)
        else:
            tag = g.get("season") or "movies"
            chosen = select_nums(nums, text=input(f"[{tag}] {len(nums)} item(s): choose (all / 1-5 / 2,4,7) [all]: "))
        raw = skip_arg if skip_arg is not None else input(f"[{g.get('season') or 'movies'}] skip numbers (e.g. 3,7-9, Enter = none): ")
        skip = set(select_nums(nums, text=raw)) if raw.strip() else set()
        g["episodes"] = [e for e in g["episodes"] if e["num"] in chosen and e["num"] not in skip]
    prefix = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--name=")), None)
    if prefix is None:
        prefix = input(f"Folder / file prefix [{name}]: ").strip() or name if do_dl else name
    slug = safe_filename(prefix)
    jobs = build_jobs(groups, prefix, root, do_dl, done_labels(f"{slug}_m3u8.txt"))
    print(f"\n{len(jobs)} item(s) to process" + (f" -> {os.path.join(root, slug)}" if do_dl else ""))
    left = run_jobs(page, jobs, slug, pool, tuple(prefer), avoid)
    if left:
        print("\nNo working server found for:", ", ".join(j["label"] for j in left))
    print(f"\nLinks saved to {slug}_m3u8.txt (server reliability learned in {SCORE_FILE})")


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    url = args[0] if args else input("Link (home / series / seasons / season / episode / movies category of any supported site): ").strip()
    if not url:
        return
    pu = urlparse(url)
    globals()['DEFAULT_REFERER'] = f"{pu.scheme}://{pu.netloc}/"
    do_dl = "--download" in sys.argv
    if not do_dl and "--no-download" not in sys.argv:
        do_dl = input("Download as MP4 too? [Y/n]: ").strip().lower() != "n"
    boost_system()
    with sync_playwright() as p:
        ctx, page = launch(p)
        ctx.on("request", feed)
        pool = ThreadPoolExecutor(max_workers=PARALLEL) if do_dl else None
        try:
            run_cli(page, url, do_dl, pool)
        except KeyboardInterrupt:
            print("\nStopped.")
        finally:
            if pool:
                pool.shutdown(wait=False, cancel_futures=True)
            ctx.close()


if __name__ == "__main__":
    main()
