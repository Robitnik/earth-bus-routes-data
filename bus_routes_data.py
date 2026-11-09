#!/usr/bin/env python3
"""Earth Bus Routes data service.

The game's Lua sandbox only lets a mod talk to this computer (127.0.0.1), so the add-on cannot ask OpenStreetMap
itself. This small program does it for the mod: it listens on 127.0.0.1 only, asks the public Overpass servers for the
bus stops and bus routes the mod wants, keeps the answers on disk and hands them over as they are.

  GET /v1/info                          {"api": 1, "app": "earth-bus-routes-data", "version": ...}
  GET /v1/nearby?lat=..&lon=..          stops and the routes calling at them around a point
  GET /v1/route?id=..                   one route relation with its geometry and its stops' tags
  GET /v1/status                        what it did lately (for the Add-ons page's log)

Every answer is {"ok": true, "cached": bool, "data": <Overpass JSON>} or {"ok": false, "error": "..."}.
Run it from BeamNG.Earth's Add-ons page (a "companion"), or by hand: python bus_routes_data.py [--port N] [--cache DIR]

Map data (c) OpenStreetMap contributors, ODbL. Standard library only. MIT licence.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

VERSION = "0.1.0"
APP = "earth-bus-routes-data"
PORT = 47630
UA = f"{APP}/{VERSION} (+https://github.com/Robitnik/earth-bus-routes)"   # Overpass refuses clients without one
MIRRORS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.private.coffee/api/interpreter",
    "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
]
TTL_S = 7 * 86400                 # a cached answer is fresh this long
CELL_DEG = 0.002                  # "nearby" answers are shared by every point within ~220 m
RADIUS_M = 650
MIN_GAP_S = 1.0                   # between two requests to the public servers (their usage policy asks for restraint)
BACKOFF_S = (1.0, 3.0, 8.0)
TIMEOUT_S = 45                   # a public server that takes longer is overloaded: try the next one
MAX_BYTES = 12 * 1024 * 1024
MODES = "^(bus|trolleybus|minibus|share_taxi)$"

log_lines = []                    # the last few events, for /v1/status
_lock = threading.Lock()          # one request to the public servers at a time
_last_call = 0.0
_key_locks = {}
_key_locks_guard = threading.Lock()


def say(msg):
    line = time.strftime("%H:%M:%S ") + msg
    print(line, flush=True)
    log_lines.append(line)
    del log_lines[:-40]


# ---- queries (pure) -------------------------------------------------------------------------------------------

def snap(v):
    return round(round(v / CELL_DEG) * CELL_DEG, 6)


def nearby_query(lat, lon, radius=RADIUS_M):
    a = f"around:{int(radius)},{lat:.5f},{lon:.5f}"
    return (f"[out:json][timeout:50];(node[highway=bus_stop]({a});node[public_transport=platform]({a});"
            f"node[public_transport=stop_position]({a});nwr[amenity=bus_station]({a});"
            f"nwr[public_transport=station][bus=yes]({a}););out tags center;"
            f'rel(bn)[type=route][route~"{MODES}"];out body;')


def route_query(rel_id):
    return f"[out:json][timeout:50];rel({int(rel_id)});out body geom;(node(r);way(r););out tags center;"


def nearby_key(lat, lon):
    return f"near2_{snap(lat):.3f}_{snap(lon):.3f}"      # (near_: before the bus stations were asked for)


def route_key(rel_id):
    return f"route_{int(rel_id)}"


def slim_nearby(text):
    """The "nearby" answer without what the mod does not read: a route relation lists every way of its line (hundreds), the
    mod only needs which of the stops around here it calls at. Returns the text of the smaller answer."""
    data = json.loads(text)
    ids = {e["id"] for e in data.get("elements", []) if e.get("type") == "node"}
    for e in data.get("elements", []):
        if e.get("type") == "relation":
            e["members"] = [m for m in e.get("members", []) if m.get("type") == "node" and m.get("ref") in ids]
    return json.dumps(data, separators=(",", ":"), ensure_ascii=False)


def check_answer(data):
    """(ok, why): Overpass sometimes answers 200 with a "remark" (query timed out, out of memory) and no elements."""
    if not isinstance(data, dict) or not isinstance(data.get("elements"), list):
        return False, "no elements in the answer"
    remark = data.get("remark")
    if isinstance(remark, str) and "error" in remark and not data["elements"]:
        return False, remark[:160]
    return True, ""


# ---- cache ----------------------------------------------------------------------------------------------------------

def default_cache_dir():
    base = os.environ.get("LOCALAPPDATA") or os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache")
    return pathlib.Path(base) / "earth-bus-routes" / "cache"


class Cache:
    def __init__(self, directory):
        self.dir = pathlib.Path(directory)
        self.dir.mkdir(parents=True, exist_ok=True)

    def path(self, key):
        return self.dir / (re.sub(r"[^A-Za-z0-9_.-]", "_", key) + ".json")

    def get(self, key):
        """(text, age_s) or (None, None). The file is {"t": epoch, "data": <text of the answer>}."""
        try:
            d = json.loads(self.path(key).read_text(encoding="utf-8"))
            return d["data"], time.time() - float(d["t"])
        except (OSError, ValueError, KeyError, TypeError):
            return None, None

    def put(self, key, text):
        tmp = self.path(key).with_suffix(".tmp")
        tmp.write_text(json.dumps({"t": time.time(), "data": text}), encoding="utf-8")
        os.replace(tmp, self.path(key))


# ---- the public servers ---------------------------------------------------------------------------------------------

def post_overpass(url, query):
    req = urllib.request.Request(url, data=urllib.parse.urlencode({"data": query}).encode(),
                                 headers={"User-Agent": UA, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=TIMEOUT_S) as r:
        body = r.read(MAX_BYTES + 1)
    if len(body) > MAX_BYTES:
        raise ValueError("answer too large")
    return body.decode("utf-8")


def fetch_upstream(query, mirrors=None, sender=None, sleep=time.sleep, clock=time.monotonic):
    """The answer's text from the first mirror that gives a good one; raises RuntimeError with every failure when none."""
    global _last_call
    mirrors = mirrors or MIRRORS
    sender = sender or post_overpass
    errors = []
    with _lock:
        for n, url in enumerate(mirrors * 2):                  # every mirror twice, with a longer wait between
            gap = MIN_GAP_S - (clock() - _last_call)
            if gap > 0:
                sleep(gap)
            try:
                text = sender(url, query)
                _last_call = clock()
                ok, why = check_answer(json.loads(text))
                if ok:
                    return text
                errors.append(f"{urllib.parse.urlsplit(url).hostname}: {why}")
            except urllib.error.HTTPError as e:
                _last_call = clock()
                errors.append(f"{urllib.parse.urlsplit(url).hostname}: HTTP {e.code}")
            except (urllib.error.URLError, OSError, ValueError, TimeoutError) as e:
                _last_call = clock()
                errors.append(f"{urllib.parse.urlsplit(url).hostname}: {type(e).__name__}")
            sleep(BACKOFF_S[min(n, len(BACKOFF_S) - 1)])
    raise RuntimeError("; ".join(errors[-4:]) or "no mirror")


class Service:
    def __init__(self, cache, upstream=fetch_upstream, ttl=TTL_S):
        self.cache, self.upstream, self.ttl = cache, upstream, ttl
        self.started = time.time()
        self.served = {"cached": 0, "fetched": 0, "stale": 0, "failed": 0}

    def get(self, key, query, post=None):
        """(text, cached): a fresh cached answer, else a fetched one (kept; `post` shrinks it first), else a stale cached
        one, else RuntimeError. Requests for one key wait for each other: the second finds the first one's answer cached."""
        with _key_locks_guard:
            lock = _key_locks.setdefault(key, threading.Lock())
        with lock:
            text, age = self.cache.get(key)
            if text is not None and age is not None and age < self.ttl:
                self.served["cached"] += 1
                return text, True
            try:
                fresh = self.upstream(query)
            except RuntimeError as e:
                if text is not None:
                    self.served["stale"] += 1
                    say(f"{key}: {e}; the cached copy is {age / 86400:.1f} days old, using it")
                    return text, True
                self.served["failed"] += 1
                say(f"{key}: failed: {e}")
                raise
            if post:
                fresh = post(fresh)
            self.cache.put(key, fresh)
            self.served["fetched"] += 1
            say(f"{key}: fetched {len(fresh) // 1024} KB")
            return fresh, False


# ---- HTTP -----------------------------------------------------------------------------------------------------------

def host_ok(host_header, port):
    """Only requests naming this computer (a web page whose name points at 127.0.0.1 cannot read the answers)."""
    return (host_header or "") in (f"127.0.0.1:{port}", f"localhost:{port}", "127.0.0.1", "localhost")


def make_handler(service, port):
    class Handler(BaseHTTPRequestHandler):
        server_version = f"{APP}/{VERSION}"
        protocol_version = "HTTP/1.1"

        def log_message(self, *a):
            pass

        def send_json(self, code, raw):
            body = raw if isinstance(raw, bytes) else raw.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()
            self.wfile.write(body)

        def fail(self, code, msg):
            self.send_json(code, json.dumps({"ok": False, "error": msg}))

        def do_GET(self):
            if not host_ok(self.headers.get("Host"), port):
                return self.fail(403, "wrong Host")
            u = urllib.parse.urlsplit(self.path)
            q = urllib.parse.parse_qs(u.query)
            try:
                if u.path == "/v1/info":
                    return self.send_json(200, json.dumps({"ok": True, "api": 1, "app": APP, "version": VERSION}))
                if u.path == "/v1/status":
                    return self.send_json(200, json.dumps({
                        "ok": True, "version": VERSION, "uptime": time.time() - service.started,
                        "served": service.served, "log": log_lines[-20:], "cache": str(service.cache.dir)}))
                if u.path == "/v1/nearby":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    slat, slon = snap(lat), snap(lon)
                    text, cached = service.get(nearby_key(lat, lon), nearby_query(slat, slon), post=slim_nearby)
                elif u.path == "/v1/route":
                    rid = int(q["id"][0])
                    if not 0 < rid < 10 ** 12:
                        return self.fail(400, "id out of range")
                    text, cached = service.get(route_key(rid), route_query(rid))
                else:
                    return self.fail(404, "unknown path")
            except (KeyError, IndexError, ValueError):
                return self.fail(400, "bad parameters")
            except RuntimeError as e:
                return self.fail(502, str(e)[:300])
            self.send_json(200, b'{"ok":true,"cached":' + (b"true" if cached else b"false") + b',"data":' + text.encode("utf-8") + b"}")

    return Handler


def serve(port=PORT, cache_dir=None, service=None):
    service = service or Service(Cache(cache_dir or default_cache_dir()))
    httpd = ThreadingHTTPServer(("127.0.0.1", port), make_handler(service, port))
    httpd.daemon_threads = True
    say(f"{APP} {VERSION} listening on 127.0.0.1:{port}, cache {service.cache.dir}")
    return httpd, service


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--port", type=int, default=int(os.environ.get("BNE_BUSDATA_PORT") or PORT))
    ap.add_argument("--cache", default=None, help="folder for cached answers")
    a = ap.parse_args(argv)
    httpd, _ = serve(a.port, a.cache)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
