# Shahiid Studio - local web GUI (index.html) that drives shahiid_links.py + megamax_grab.py
# Usage:  py shahiid_studio.py install    (one time)   |   py shahiid_studio.py start [--port=8765] [--host=127.0.0.1] [--reset-login]
import hashlib, hmac, json, os, queue, re, secrets, shutil, subprocess, sys, threading, time, webbrowser
from concurrent.futures import ThreadPoolExecutor
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
sys.path.insert(0, HERE)


def arg(name, default):
    for a in sys.argv:
        if a.startswith(f"--{name}="):
            return a.split("=", 1)[1]
    return default


PORT, BIND = int(arg("port", 8765)), arg("host", "127.0.0.1")
MULTI = "--multi" in sys.argv          # default: the credentials work for ONE login session
TTL = int(arg("ttl", 86400))            # ...and everything expires after 24 hours
LOGIN = {}
SESSIONS, FAILS, JOBS, TASKS = {}, {}, {}, queue.Queue()
tl, LOCK = threading.local(), threading.Lock()


# ------------------------------------------------------------ install / login
def install():
    py = sys.executable
    subprocess.call([py, "-m", "pip", "install", "--upgrade", "requests", "playwright"])
    subprocess.call([py, "-m", "playwright", "install", "chromium"])
    print("ffmpeg:", "found" if shutil.which("ffmpeg") else "NOT FOUND - install it from https://ffmpeg.org and add it to PATH")
    for f in ("index.html", "hunter_core.py", "megamax_grab.py"):
        print(f, "OK" if os.path.exists(os.path.join(HERE, f)) else "MISSING - put it in this folder")
    if sys.platform == "win32":
        with open(os.path.join(HERE, "start_studio.bat"), "w") as f:
            f.write('@echo off\r\ncd /d "%~dp0"\r\npy shahiid_studio.py start\r\npause\r\n')
        print("Created start_studio.bat - double-click it to launch the studio.")
    print("Done. Start it with:  py shahiid_studio.py start")


def make_login(ttl):
    # New random credentials on EVERY start; kept in memory only (nothing is written to disk)
    user = "user_" + secrets.token_hex(3)
    pw = "".join(secrets.choice("ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789") for _ in range(14))
    salt = secrets.token_bytes(16)
    LOGIN.update(user=user, salt=salt, hash=hashlib.pbkdf2_hmac("sha256", pw.encode(), salt, 200000),
                 expires=time.time() + ttl, used=False)
    mode = "re-login allowed until then" if MULTI else "single login session"
    print("=" * 56 + f"\n  Username: {user}\n  Password: {pw}\n"
          f"  Valid for {ttl / 3600:g} hour(s), {mode}\n" + "=" * 56)


def check_login(u, p):
    # -> "ok" | "bad" | "expired" | "used"
    if time.time() > LOGIN["expires"]:
        return "expired"
    h = hashlib.pbkdf2_hmac("sha256", p.encode(), LOGIN["salt"], 200000)
    if not (hmac.compare_digest(u.encode(), LOGIN["user"].encode()) & hmac.compare_digest(h, LOGIN["hash"])):
        return "bad"
    if LOGIN["used"] and not MULTI:
        return "used"
    LOGIN["used"] = True
    return "ok"


# ------------------------------------------------------------ jobs + log capture
class Tee:
    # Mirrors stdout; inside a job thread, lines go to the job log and "\r" updates become the progress text
    encoding = "utf-8"

    def __init__(self, real):
        self.real = real

    def write(self, s):
        self.real.write(s)
        job = getattr(tl, "job", None)
        if job is not None:
            with LOCK:
                parts = re.split(r"([\r\n])", job["_buf"] + s)
                job["_buf"] = parts.pop()
                for i in range(0, len(parts) - 1, 2):
                    text, sep = parts[i], parts[i + 1]
                    if sep == "\r":
                        job["progress"] = text.strip()
                    elif text.strip():
                        job["log"].append(text.rstrip())
                        job["progress"] = ""
        return len(s)

    def flush(self):
        self.real.flush()

    def isatty(self):
        return False


def new_job(kind):
    j = {"id": secrets.token_hex(4), "kind": kind, "status": "queued", "log": [], "progress": "",
         "result": None, "partial": [], "cancel": False, "_buf": ""}
    JOBS[j["id"]] = j
    for k in list(JOBS)[:-40]:
        JOBS.pop(k, None)
    return j


class Match:
    def __init__(self, fn):
        self.fn = fn

    def __contains__(self, n):
        return self.fn(n)


# ------------------------------------------------------------ browser tasks (run in ONE worker thread)
def set_ref(mg, d):
    u = d.get("url") or (((d.get("groups") or [{}])[0].get("episodes") or [{}])[0].get("href")) or ""
    pu = urlparse(u)
    if pu.netloc:
        mg.DEFAULT_REFERER = f"{pu.scheme}://{pu.netloc}/"


def split_list(v, default):
    return [x.strip().lower() for x in str(default if v is None else v).split(",") if x.strip()]


def h_load(page, mg, hc, job, d):
    # ONE task understands any page of any supported site: list / series / seasons / season / episode / movies category
    return hc.load(page, d["url"], hint=d.get("hint"), idx=int(d.get("idx") or 1))


def h_capture(page, mg, hc, job, d):
    groups = [g for g in d.get("groups", []) if g.get("episodes")]
    prefix = str(d.get("prefix") or d.get("name") or "downloads").strip()
    slug, do_dl = hc.safe_filename(prefix), bool(d.get("download"))
    prefer, avoid = split_list(d.get("prefer"), "megamax"), split_list(d.get("avoid"), "mixdrop,doodstream")
    mg.AVOID[:] = avoid
    mg.MIN_SECONDS = float(d.get("min_minutes") or 18) * 60
    mg.WORKERS = int(d.get("workers") or 64)
    par = mg.PARALLEL = int(d.get("parallel") or 2)
    out, cancel = job["partial"], (lambda: job["cancel"])
    jobs = hc.build_jobs(groups, prefix, "downloads", do_dl, mg.done_labels(f"{slug}_m3u8.txt"))
    print(f"{len(jobs)} item(s) to process" + (f" -> downloads/{slug}/" if do_dl else ""))
    pool = ThreadPoolExecutor(max_workers=par) if do_dl else None

    def dl(j, rec):
        tl.job = job
        return mg.dl_task(j, rec)

    def on_result(j, rec):
        out.append({"ep": j["label"], "server": f"{rec['server']}/{rec['host']}", "kind": "m3u8", "url": rec["url"],
                    "file": j["dest"] or ""})

    left = hc.run_jobs(page, jobs, slug, pool, tuple(prefer), avoid, cancel, on_result, dl)
    if pool:
        pool.shutdown(wait=True)
    if left:
        print("No working server found for:", ", ".join(j["label"] for j in left))
    print("Cancelled." if cancel() else "Finished.")
    return {"count": len(out), "failed": [j["label"] for j in left]}


TASK_FUNCS = {"load": h_load, "seasons": h_load, "episodes": h_load, "capture": h_capture}
_wt = None


def worker():
    import hunter_core as hc
    import megamax_grab as mg
    from playwright.sync_api import sync_playwright
    with sync_playwright() as p:
        ctx = page = None
        while True:
            job, fn = TASKS.get()
            tl.job, job["status"] = job, "running"
            try:
                if page is None or page.is_closed():
                    try:
                        ctx and ctx.close()
                    except Exception:
                        pass
                    ctx, page = mg.launch(p)
                    ctx.on("request", hc.feed)
                job["result"] = fn(page, mg, hc, job)
                job["status"] = "done"
            except Exception as e:
                print("ERROR:", str(e).splitlines()[0] if str(e) else repr(e))
                job["status"] = "error"
            tl.job = None


def ensure_worker():
    global _wt
    if _wt is None or not _wt.is_alive():
        _wt = threading.Thread(target=worker, daemon=True)
        _wt.start()


# ------------------------------------------------------------ HTTP
class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code, body, ctype="application/json", extra=()):
        if not isinstance(body, bytes):
            body = (body if isinstance(body, str) else json.dumps(body, ensure_ascii=False)).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype + "; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        for k, v in extra:
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def host_ok(self):  # blocks DNS-rebinding style requests when bound to localhost
        return BIND != "127.0.0.1" or (self.headers.get("Host") or "").split(":")[0] in ("127.0.0.1", "localhost")

    def sid(self):
        m = SimpleCookie(self.headers.get("Cookie", "")).get("sid")
        return m.value if m else ""

    def authed(self):
        return SESSIONS.get(self.sid(), 0) > time.time()

    def do_GET(self):
        if not self.host_ok():
            return self.send(403, {"error": "host"})
        u = urlparse(self.path)
        q = parse_qs(u.query)
        if u.path in ("/", "/index.html"):
            with open(os.path.join(HERE, "index.html"), "rb") as f:
                return self.send(200, f.read(), "text/html")
        if u.path == "/api/me":
            return self.send(200, {"ok": self.authed()})
        if not self.authed():
            return self.send(401, {"error": "auth"})
        if u.path == "/api/job":
            j = JOBS.get(q.get("id", [""])[0])
            if not j:
                return self.send(404, {"error": "no such job"})
            since = int(q.get("since", ["0"])[0] or 0)
            with LOCK:
                return self.send(200, {"status": j["status"], "log": j["log"][since:], "next": len(j["log"]),
                                       "progress": j["progress"], "result": j["result"], "partial": list(j["partial"])})
        self.send(404, {"error": "not found"})

    def do_POST(self):
        if not self.host_ok():
            return self.send(403, {"error": "host"})
        try:
            n = int(self.headers.get("Content-Length") or 0)
            d = json.loads(self.rfile.read(min(n, 2000000)) or b"{}")
        except Exception:
            return self.send(400, {"error": "bad json"})
        p = urlparse(self.path).path
        if p == "/api/login":
            ip = self.client_address[0]
            cnt, until = FAILS.get(ip, (0, 0))
            if until > time.time():
                return self.send(429, {"error": "too many attempts, wait a minute"})
            if until:
                cnt = 0
            res = check_login(str(d.get("user", "")), str(d.get("pass", "")))
            if res == "ok":
                FAILS.pop(ip, None)
                sid = secrets.token_urlsafe(32)
                SESSIONS[sid] = LOGIN["expires"]  # the session dies with the credentials
                return self.send(200, {"ok": True}, extra=[("Set-Cookie", f"sid={sid}; HttpOnly; SameSite=Strict; Path=/; Max-Age={int(LOGIN['expires'] - time.time())}")])
            if res == "expired":
                return self.send(403, {"error": "these credentials expired - restart the studio for new ones"})
            if res == "used":
                return self.send(403, {"error": "these credentials were already used - restart the studio for new ones"})
            cnt += 1
            FAILS[ip] = (cnt, time.time() + 60 if cnt >= 5 else 0)
            return self.send(401, {"error": "wrong username or password"})
        if not self.authed():
            return self.send(401, {"error": "auth"})
        if p == "/api/logout":
            SESSIONS.pop(self.sid(), None)
            return self.send(200, {"ok": True})
        if p == "/api/cancel":
            j = JOBS.get(str(d.get("id")))
            if j:
                j["cancel"] = True
            return self.send(200, {"ok": True})
        if p == "/api/task":
            fn = TASK_FUNCS.get(str(d.get("kind")))
            if not fn:
                return self.send(400, {"error": "unknown task"})
            if d["kind"] != "capture" and not re.match(r"https?://", str(d.get("url", ""))):
                return self.send(400, {"error": "bad url"})
            j = new_job(d["kind"])
            ensure_worker()
            TASKS.put((j, lambda page, mg, sl, job: (set_ref(mg, d), fn(page, mg, sl, job, d))[1]))
            return self.send(200, {"id": j["id"]})
        self.send(404, {"error": "not found"})


def main():
    cmd = next((a for a in sys.argv[1:] if not a.startswith("--")), "start")
    if cmd == "install":
        return install()
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    sys.stdout = Tee(sys.stdout)
    make_login(TTL)
    if not os.path.exists(os.path.join(HERE, "index.html")):
        sys.exit("index.html is missing next to this script")
    srv = ThreadingHTTPServer((BIND, PORT), H)
    url = f"http://127.0.0.1:{PORT}/"
    print(f"Shahiid Studio running at {url}   (Ctrl+C to stop)")
    if BIND != "127.0.0.1":
        print("WARNING: reachable from your network - keep the password private")
    threading.Timer(1, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("Stopped.")


if __name__ == "__main__":
    main()
