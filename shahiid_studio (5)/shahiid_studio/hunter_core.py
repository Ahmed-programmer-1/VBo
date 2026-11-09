# hunter_core: ONE engine for Shahiid / EgyDead / AnimeZid / TopCinema / Animerco (series, seasons, episodes and movie categories)
#  - understands any page of these sites (list / series / seasons / season / episode / movie) and reacts accordingly
#  - per episode: its own servers -> preferred server first -> verified m3u8 (long enough, not a decoy) -> next server on ANY failure
#  - learns which servers work (megamax_grab.record) and orders them by reliability next time
#  - folders: <out>/<prefix>/<season>/<episode>.mp4  ;  movies: <out>/<prefix>/<movie title>.mp4
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import parse_qs, unquote, urlparse

from playwright.sync_api import sync_playwright

import megamax_grab as mg

EMBEDS = []   # sub-frame document requests seen after a server click (fed by feed())
AD_HOSTS = mg.BLOCK_HOSTS + ("facebook.com", "twitter.com", "t.me", "instagram.com", "youtube.com", "tiktok.com")
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
        mg.open_page(page, u)
        if u in extra:
            base = page_key(page.url)
        for i in parse(page):
            if i["href"] not in seen:
                seen.add(i["href"])
                items.append(i)
        print(f"   page {len(visited) - 1}: {len(items)} items so far")
    if len(visited) > 1:
        mg.open_page(page, orig)
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
    mg.open_page(page, url)
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
        mg.open_page(page, u)
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
                fr.evaluate(mg.JS_NUDGE)
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
    return ("megamax" in name.lower() or any(k in embed for k in mg.MEGAMAX_HOSTS)
            or bool(re.search(r"/iframe/[A-Za-z0-9]{8,}/?$", urlparse(embed).path)))


def resolve_episode(page, site, job, prefer=("megamax",), avoid=None):
    # Every episode has its own servers. Try them in preference/reliability order; ANY failure moves on to the next server.
    scope = f"outer:{site.key}"
    items = open_episode(page, site, job["ep"])
    names = [n for _, n in items]
    if not names:
        return None
    order = [n for n in mg.rank_names(scope, names, tuple(prefer), avoid) if n not in job["bad"]]
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
            mg.CAUGHT.clear()
            mg.BAD.clear()
            if name == "page":  # no server list: the page's own player
                press_overlay(page)
                link, ref = mg.wait_media(page, 25)
                dirty = True
                rec, embed = ({"host": "page", "url": link, "referer": ref, "kind": mg.KINDS.get(link)} if link else None), page.url
            else:
                embed = capture_embed(page, loc, prev)
                if not embed:
                    mg.record(scope, name, False)
                    print("      no embed captured, next server")
                    continue
                prev = embed
                print(f"      embed: {embed}")
                wrapper, rec, res = is_wrapper(embed, job["ep"]["href"]), None, None
                if wrapper:
                    print("      (the platform's own player: working inside this page, not opening it)")
                dirty = True
                if is_megamax(name, embed) or mg.rows_frame(page, 4) is not None:  # host list: pick a host, press play, Back, next host
                    res = mg.grab_inpage(page, job["tried"])
                    if res is None and not wrapper:   # no usable window in the page: open a third-party Megamax window on its own
                        res = mg.grab(page, embed, False, job["tried"])
                    rec = res[0] if res else None
                if rec is None and res != []:   # [] = every Megamax host already failed: do not wait again
                    link, ref = mg.wait_media(page, 28)   # real play clicks inside the player, then whatever the page requests
                    if not link and not wrapper and not is_megamax(name, embed):
                        mg.CAUGHT.clear()
                        mg.BAD.clear()
                        mg.open_page(page, embed)   # a third-party embed page may also work on its own
                        link, ref = mg.wait_media(page, 25)
                    rec = {"host": name.lower(), "url": link, "referer": ref, "kind": mg.KINDS.get(link)} if link else None
            if rec:
                mg.record(scope, name, True)
                rec.update(server=name, embed=embed)
                return rec
            mg.record(scope, name, False)
            print("      no usable m3u8 here, next server")
        except Exception as e:
            dirty = True
            mg.record(scope, name, False)
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
    out_path, dl, lost = f"{slug}_m3u8.txt", dl or mg.dl_task, []

    def ok(j, rec):
        mg.write_lines(out_path, j["label"], [rec])
        if on_result:
            on_result(j, rec)

    for rnd in range(1, mg.MAX_ROUNDS + 2):
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
            old = mg.set_min_seconds(j["min_seconds"]) if j.get("min_seconds") else None
            try:
                rec = resolve_episode(page, site, j, prefer, avoid)
            finally:
                if old is not None:
                    mg.set_min_seconds(old)
            if not rec:
                j["nolink"] += 1
                print("   no m3u8 from any server" + (" (will retry once more)" if j["nolink"] < 2 else ""))
                (failed if j["nolink"] < 2 else lost).append(j)
                continue
            mg.write_lines(f"{slug}_embed.txt", j["label"], [{"host": rec["server"], "url": rec["embed"]}])
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
                    mg.record("megamax", rec["host"], False)
                else:
                    j["bad"].add(rec["server"])
                    mg.record(f"outer:{site.key}", rec["server"], False)
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
    prefer, avoid = split_opt("prefer", "megamax"), split_opt("avoid", ",".join(mg.AVOID))
    mg.AVOID[:] = avoid
    root = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--out=")), "downloads")
    lo, hi = mg.opt("from", None), mg.opt("to", None)
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
    jobs = build_jobs(groups, prefix, root, do_dl, mg.done_labels(f"{slug}_m3u8.txt"))
    print(f"\n{len(jobs)} item(s) to process" + (f" -> {os.path.join(root, slug)}" if do_dl else ""))
    left = run_jobs(page, jobs, slug, pool, tuple(prefer), avoid)
    if left:
        print("\nNo working server found for:", ", ".join(j["label"] for j in left))
    print(f"\nLinks saved to {slug}_m3u8.txt (server reliability learned in {mg.SCORE_FILE})")


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
    mg.DEFAULT_REFERER = f"{pu.scheme}://{pu.netloc}/"
    do_dl = "--download" in sys.argv
    if not do_dl and "--no-download" not in sys.argv:
        do_dl = input("Download as MP4 too? [Y/n]: ").strip().lower() != "n"
    mg.boost_system()
    with sync_playwright() as p:
        ctx, page = mg.launch(p)
        ctx.on("request", feed)
        pool = ThreadPoolExecutor(max_workers=mg.PARALLEL) if do_dl else None
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
