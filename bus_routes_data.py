#!/usr/bin/env python3
"""Earth Bus Routes data service.

The game's Lua sandbox only lets a mod talk to this computer (127.0.0.1), so the add-on cannot ask OpenStreetMap
itself. This small program does it for the mod: it listens on 127.0.0.1 only, asks the public Overpass servers for the
bus stops and bus routes the mod wants, keeps the answers on disk and hands them over as they are.

  GET /v1/info                          {"api": 1, "app": "earth-bus-routes-data", "version": ...}
  GET /v1/nearby?lat=..&lon=..          stops and the routes calling at them around a point
  GET /v1/route?id=..                   one route relation with its geometry and its stops' tags
  GET /v1/path?pts=lat,lon;lat,lon;..   the road route through 2..25 points (OSRM): {points, legs, dist, dur, source}
  GET /v1/along?pts=...                 the bus stops within 30 m of that road route
  GET /v1/stations?lat=..&lon=..        the bus stations within 25 km of a point
  GET /v1/search?q=..&lat=..&lon=..     towns ("places") and stations / stops by name (&local=1: only what is on this
                                        computer, answered in milliseconds; else the geocoder too, ~1 s)
  GET /v1/towns?lat=..&lon=..           the cities, towns and villages within 40 km of a point (for the map; from GeoNames
                                        files kept on this computer, else Overpass)
  GET /v1/gtfs?lat=..&lon=..            the state of the national timetables (downloads them in the background the first time)
  GET /v1/mapstops?lat=..&lon=..&r=..   the stations and stops within r metres (at most 30 km) for the map: name, place, kind
                                        (station / stop) and the line numbers calling there; from this computer only
  GET /v1/progress                      what the service is waiting for right now (for a progress bar)
  GET /v1/lines?ref=..&lat=..&lon=..    the bus lines with this number within 40 km (&local=1 likewise)
  GET /v1/shift?pid=..&start=..&day=..&mins=..   a shift: the trip of timetable pattern `pid` leaving at `start` (s from
                                        midnight), then the trips that follow it for `mins` minutes (chained at the termini)
  GET /v1/depot?lat=..&lon=..           the bus depot within 10 km of a point, else the nearest bus station: {"depot": {..} | null}
  GET /v1/status                        what it did lately (for the Add-ons page's log)
  GET /v1/db                            the state of the route database (lines and stops prepared in advance, see below)
  GET /v1/connections?sid=..|lat=..&lon=..&t=..&day=..&win=8[&ref=..]
                                        the lines arriving at a stop (and the stops within 150 m of it) within +-win minutes of
                                        t (seconds from midnight) on weekday day (1 Monday .. 7 Sunday), for transfers; the
                                        line `ref` itself is left out. From the timetables on this computer only.
  GET /v1/departures?lat=..&lon=..&t=..&day=..[&r=3000&mins=30]
                                        the trips of the timetables that call at a stop within r metres between t - 5 min and
                                        t + mins (t in seconds from midnight of weekday day): {"patterns": [{pid, id (for
                                        /v1/route), ref, head, from, to, offs}], "trips": [{pid, start}]}. Timetables only.

Every answer is {"ok": true, "cached": bool, "data": <Overpass JSON>} or {"ok": false, "error": "..."}.

The route database (github.com/Robitnik/earth-bus-routes-db-eu, JSON files on GitHub, ODbL) holds the bus lines and stops of whole
countries prepared in advance, with the timetables' times of a typical day. Where it has a place, /v1/nearby and /v1/route answer
from it (one small file each, no map server asked, no timetables downloaded). Elsewhere, and with BNE_BUSDATA_LIVE=1, the old way
(Overpass, timetables, routing servers) is used. BNE_BUSDATA_DB=0 turns the database off; BNE_BUSDATA_DB=<folder or URL>[;..]
points to another copy (a folder on this computer for hand-edited data).
Run it from BeamNG.Earth's Add-ons page (a "companion"), or by hand: python bus_routes_data.py [--port N] [--cache DIR]

Map data (c) OpenStreetMap contributors, ODbL. Towns (c) GeoNames, CC BY 4.0. Standard library only. MIT licence.
"""
import argparse
import array
import concurrent.futures
import hashlib
import io
import math
import json
import os
import pathlib
import platform
import datetime
import re
import select
import shutil
import socket
import subprocess
import sys
import tarfile
import threading
import unicodedata
import time
import urllib.error
import urllib.parse
import urllib.request
import wave
import zipfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

VERSION = "0.13.0"
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
BUDGET_S = 90                    # one request to the public servers, its wait in the queue included, never takes longer
LEASE_S = 25                     # a map answer fetched for nobody in particular (the partial nearby) goes on this long after
                                 # the last time somebody asked for it (the open menu asks again every 10 s)
MAX_BYTES = 12 * 1024 * 1024
MODES = "^(bus|trolleybus|minibus|share_taxi)$"
PHOTON = "https://photon.komoot.io/api/"
PHOTON_TIMEOUT_S = 8
PHOTON_COOLDOWN_S = 60          # after a failure the geocoder is left alone this long (searches go on without it)
_photon_down_until = 0.0
PLACE_KINDS = {"city": 5, "town": 4, "municipality": 3, "village": 3, "borough": 2, "suburb": 2, "hamlet": 2, "quarter": 1,
               "neighbourhood": 1, "locality": 1}
FEATURES = ["path", "along", "search", "stations", "local", "lines", "places", "progress", "towns", "gazetteer", "gtfs", "mapstops", "limits"]
STATIONS_M = 25000
STATIONS_CELL_DEG = 0.05
OSRM = ["https://router.project-osrm.org", "https://routing.openstreetmap.de/routed-car"]
OSRM_TIMEOUT_S = 25
MAX_WAYPOINTS = 25
MAX_LEG_M = 60000
MAX_PATH_POINTS = 2000
ALONG_M = 30
SEARCH_M = 40000
STRAIGHT_MS = 40 / 3.6            # speed assumed on a straight fallback leg

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
    # the relation with its geometry, its members, and the bus stops within 30 m of its ways: the platform of the other side of
    # the road is not a member (a stop is listed once, for one direction), but the other direction's bus stops there
    return (f"[out:json][timeout:60];rel({int(rel_id)})->.r;.r out body geom;(node(r.r);way(r.r););out tags center;"
            f"way(r.r)->.w;(node[highway=bus_stop](around.w:30);node[public_transport=platform](around.w:30););out tags center;")


def nearby_key(lat, lon):
    return f"near3_{snap(lat):.3f}_{snap(lon):.3f}"      # (near_: before the bus stations; near2_: before the stops had their number in the route)


def route_query_basic(rel_id):
    """The route without the bus stops near its road: the fallback when a server does not take the longer query."""
    return f"[out:json][timeout:50];rel({int(rel_id)});out body geom;(node(r);way(r););out tags center;"


def route_key(rel_id):
    return f"route2_{int(rel_id)}"          # (route_: before the bus stops near the road were asked for)


def stop_sequence(members):
    """The members of a route relation that are its stops, in the order listed: the platforms, else the stop positions, else
    any nodes. Returns the list of refs (a stop listed twice, as a loop does at its ends, is listed twice)."""
    nodes = [m for m in members if m.get("type") == "node"]
    for prefix in ("platform", "stop"):
        seq = [m["ref"] for m in nodes if (m.get("role") or "").startswith(prefix)]
        if len(seq) >= 2:
            return seq
    return [m["ref"] for m in nodes]


def slim_nearby(text):
    """The "nearby" answer without what the mod does not read: a route relation lists every way of its line (hundreds), the
    mod only needs which of the stops around here it calls at and where in the route they are: each kept member gets `i`, its
    place (1 = first stop) among the route's stops, and the relation gets `n` (how many stops) and `ordered` (the tags promise
    the order: public_transport:version 2). Returns the text of the smaller answer."""
    data = json.loads(text)
    ids = {e["id"] for e in data.get("elements", []) if e.get("type") == "node"}
    for e in data.get("elements", []):
        if e.get("type") == "relation":
            full = e.get("members", [])
            seq = stop_sequence(full)
            places = {}
            for i, ref in enumerate(seq, 1):
                places.setdefault(ref, []).append(i)
            kept = []
            for m in full:
                if m.get("type") == "node" and m.get("ref") in ids:
                    kept.append(m)
            for m in kept:
                if m["ref"] in places:
                    m["i"] = places[m["ref"]][0]
                    if len(places[m["ref"]]) > 1:
                        m["j"] = places[m["ref"]][-1]           # a stop listed twice (a loop's first and last)
            e["members"] = kept
            e["n"] = len(seq)
            e["ordered"] = (e.get("tags") or {}).get("public_transport:version") == "2"
    return json.dumps(data, separators=(",", ":"), ensure_ascii=False)


def check_answer(data):
    """(ok, why): Overpass sometimes answers 200 with a "remark" (query timed out, out of memory) and no elements."""
    if not isinstance(data, dict) or not isinstance(data.get("elements"), list):
        return False, "no elements in the answer"
    remark = data.get("remark")
    if isinstance(remark, str) and "error" in remark and not data["elements"]:
        return False, remark[:160]
    return True, ""


# ---- paths and searches (pure) ------------------------------------------------------------------------------------

def parse_pts(text, lo=2, hi=MAX_WAYPOINTS):
    """[(lat, lon), ...] of "lat,lon;lat,lon;..." or raises ValueError."""
    out = []
    for part in (text or "").split(";"):
        a, b = part.split(",")
        lat, lon = float(a), float(b)
        if not (-85 <= lat <= 85 and -180 <= lon <= 180):      # (also false for nan)
            raise ValueError("point out of range")
        out.append((round(lat, 6), round(lon, 6)))
    if not lo <= len(out) <= hi:
        raise ValueError(f"{lo}..{hi} points wanted")
    return out


def hav(a, b):
    r = 6371008.8
    p1, p2 = math.radians(a[0]), math.radians(b[0])
    dp, dl = p2 - p1, math.radians(b[1] - a[1])
    h = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(min(1.0, math.sqrt(h)))


def simplify(points, tol_m):
    """Douglas-Peucker on a local flat projection (iterative: a route has thousands of points)."""
    n = len(points)
    if n < 3:
        return list(points)
    lat0 = math.radians(points[0][0])
    xy = [((p[1] - points[0][1]) * 111320 * math.cos(lat0), (p[0] - points[0][0]) * 110574) for p in points]
    keep = [False] * n
    keep[0] = keep[-1] = True
    stack = [(0, n - 1)]
    while stack:
        i, j = stack.pop()
        ax, ay = xy[i]
        bx, by = xy[j]
        dx, dy = bx - ax, by - ay
        L2 = dx * dx + dy * dy
        best, k = -1.0, -1
        for m in range(i + 1, j):
            px, py = xy[m]
            if L2 == 0:
                d = math.hypot(px - ax, py - ay)
            else:
                t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / L2))
                d = math.hypot(px - ax - t * dx, py - ay - t * dy)
            if d > best:
                best, k = d, m
        if best > tol_m:
            keep[k] = True
            stack += [(i, k), (k, j)]
    return [p for p, f in zip(points, keep) if f]


def osrm_url(base, pts):
    coords = ";".join(f"{lon:.6f},{lat:.6f}" for lat, lon in pts)
    return f"{base}/route/v1/driving/{coords}?overview=full&geometries=geojson&steps=false"


def parse_osrm(data):
    """{points, legs:[{dist, dur}], dist, dur, source:"osrm"} of an OSRM answer, or ValueError."""
    if not isinstance(data, dict) or data.get("code") != "Ok" or not data.get("routes"):
        raise ValueError(f"no route ({data.get('code') if isinstance(data, dict) else 'bad answer'})")
    r = data["routes"][0]
    pts = [(float(c[1]), float(c[0])) for c in r["geometry"]["coordinates"]]
    tol = 3.0
    pts = simplify(pts, tol)
    while len(pts) > MAX_PATH_POINTS:
        tol *= 2
        pts = simplify(pts, tol)
    legs = [{"dist": round(float(l.get("distance") or 0)), "dur": round(float(l.get("duration") or 0))} for l in r.get("legs", [])]
    return {"points": [[round(a, 6), round(b, 6)] for a, b in pts], "legs": legs, "dist": round(float(r.get("distance") or 0)),
            "dur": round(float(r.get("duration") or 0)), "source": "osrm"}


def straight_path(pts):
    """The stations joined by straight lines: what the mod gets while no routing server answers (never cached)."""
    legs = []
    for a, b in zip(pts, pts[1:]):
        d = hav(a, b)
        legs.append({"dist": round(d), "dur": round(d / STRAIGHT_MS)})
    return {"points": [[a, b] for a, b in pts], "legs": legs, "dist": sum(l["dist"] for l in legs),
            "dur": sum(l["dur"] for l in legs), "source": "straight"}


def check_legs(pts):
    for a, b in zip(pts, pts[1:]):
        if hav(a, b) > MAX_LEG_M:
            raise ValueError("a leg is longer than 60 km")


def _hash(prefix, pts):
    return prefix + hashlib.sha1(";".join(f"{a:.5f},{b:.5f}" for a, b in pts).encode()).hexdigest()[:20]


def path_key(pts):
    return _hash("path_", pts)


def along_key(pts):
    return _hash("along_", pts)


TILE_LAT, TILE_LON = 0.02, 0.03       # the boxes the stops along a road are asked for (about 2.2 x 2.1 km)
ALONG_STATION_M = 150                 # a bus station is "on" the road this near (it is a whole yard)
MAX_TILES = 90


def path_tiles(points):
    """The set of (i, j) tiles a road passes through, found by walking it in steps well under a tile."""
    tiles = set()
    for a, b in zip(points, points[1:]):
        n = max(1, int(hav(a, b) / 400))
        for k in range(n + 1):
            lat = a[0] + (b[0] - a[0]) * k / n
            lon = a[1] + (b[1] - a[1]) * k / n
            tiles.add((math.floor(lat / TILE_LAT), math.floor(lon / TILE_LON)))
    if len(points) == 1:
        tiles.add((math.floor(points[0][0] / TILE_LAT), math.floor(points[0][1] / TILE_LON)))
    return tiles


def along_query(points):
    """One query for the stops in every tile the road passes through (a small box around each: much less than the box of
    the whole road). The answer is cut down to the stops on the road by filter_along."""
    tiles = sorted(path_tiles([tuple(p) for p in points]))
    if len(tiles) > MAX_TILES:
        raise ValueError("the road is too long")
    pad = 0.0004
    parts = []
    for i, j in tiles:
        box = f"{i * TILE_LAT - pad:.4f},{j * TILE_LON - pad:.4f},{(i + 1) * TILE_LAT + pad:.4f},{(j + 1) * TILE_LON + pad:.4f}"
        parts.append(f"node[highway=bus_stop]({box});node[public_transport=platform]({box});"
                     f"node[public_transport=stop_position]({box});nwr[amenity=bus_station]({box});")
    return f"[out:json][timeout:90];({''.join(parts)});out tags center;"


def dist_to_path(lat, lon, path):
    """Metres from a point to a polyline [(lat, lon), ...] (local flat projection)."""
    k = math.cos(math.radians(lat)) * 111320
    best = float("inf")
    for (la, lo), (lb, lb2) in zip(path, path[1:]):
        ax, ay = (lo - lon) * k, (la - lat) * 110574
        bx, by = (lb2 - lon) * k, (lb - lat) * 110574
        dx, dy = bx - ax, by - ay
        L2 = dx * dx + dy * dy
        t = 0.0 if L2 == 0 else max(0.0, min(1.0, -(ax * dx + ay * dy) / L2))
        d = math.hypot(ax + t * dx, ay + t * dy)
        if d < best:
            best = d
    return best


def filter_along(text, points, radius=ALONG_M):
    """The answer of along_query without the stops that are not on the road ('points' = [[lat, lon], ...])."""
    path = [tuple(p) for p in points]
    data = json.loads(text)
    keep = []
    for e in data.get("elements", []):
        tags = e.get("tags") or {}
        lat, lon = e.get("lat"), e.get("lon")
        if lat is None and e.get("center"):
            lat, lon = e["center"].get("lat"), e["center"].get("lon")
        if lat is None or lon is None:
            continue
        limit = ALONG_STATION_M if tags.get("amenity") == "bus_station" else radius
        if dist_to_path(lat, lon, path) <= limit:
            keep.append(e)
    data["elements"] = keep
    return json.dumps(data, separators=(",", ":"), ensure_ascii=False)


FOLD = {"a": "a\u00e1\u00e0\u00e4\u00e2", "c": "c\u010d", "d": "d\u010f", "e": "e\u00e9\u011b\u00eb\u00e8", "i": "i\u00ed\u00ee",
        "l": "l\u013e\u013a\u0142", "n": "n\u0148\u0144", "o": "o\u00f3\u00f6\u00f4", "r": "r\u0159", "s": "s\u0161\u015b",
        "t": "t\u0165", "u": "u\u00fa\u016f\u00fc\u00fb", "y": "y\u00fd", "z": "z\u017e\u017a"}


def name_regex(text):
    """A case-insensitive Overpass regex for what the player typed: plain letters also match their accented forms;
    everything else is matched literally. None when there is too little to search for."""
    t = " ".join((text or "").split())[:40]
    if len(t) < 2:
        return None
    out = []
    for ch in t:
        lo = ch.lower()
        if lo in FOLD:
            out.append("[" + FOLD[lo] + "]")
        elif ch.isalnum() or ch in " -":
            out.append(ch)
        else:
            out.append(".")
    return "".join(out)


def search_query(text, lat, lon, radius=SEARCH_M):
    rx = name_regex(text)
    if rx is None:
        raise ValueError("search text too short")
    a = f"around:{int(radius)},{lat:.4f},{lon:.4f}"
    n = f'[name~"{rx}",i]'
    return (f"[out:json][timeout:50];(nwr[amenity=bus_station]{n}({a});node[highway=bus_stop]{n}({a});"
            f"node[public_transport=platform]{n}({a}););out tags center 120;")


TOWNS_M = 40000
TOWNS_CELL_DEG = 0.25
TOWN_RANK = {"city": 3, "town": 2, "village": 1}


def towns_query(lat, lon, radius=TOWNS_M):
    return (f'[out:json][timeout:50];node[place~"^(city|town|village)$"][name]'
            f"(around:{int(radius)},{lat:.4f},{lon:.4f});out tags;")


def towns_key(lat, lon):
    snap = lambda v: round(round(v / TOWNS_CELL_DEG) * TOWNS_CELL_DEG, 2)
    return f"towns_{snap(lat):.2f}_{snap(lon):.2f}"


def slim_towns(text):
    """[{name, lat, lon, kind, population}] of a towns answer, the biggest places first."""
    out = []
    for e in json.loads(text).get("elements", []):
        tg = e.get("tags") or {}
        kind = tg.get("place")
        if kind not in TOWN_RANK or not tg.get("name") or e.get("lat") is None:
            continue
        try:
            pop = int(str(tg.get("population", "0")).replace(" ", "").split(";")[0])
        except ValueError:
            pop = 0
        out.append({"name": tg["name"], "lat": e["lat"], "lon": e["lon"], "kind": kind, "population": pop})
    out.sort(key=lambda p: (-TOWN_RANK[p["kind"]], -p["population"], p["name"]))
    return json.dumps({"towns": out}, separators=(",", ":"), ensure_ascii=False)


def stations_query(lat, lon, radius=STATIONS_M):
    a = f"around:{int(radius)},{lat:.4f},{lon:.4f}"
    return (f"[out:json][timeout:50];(nwr[amenity=bus_station]({a});nwr[public_transport=station][bus=yes]({a}););"
            "out tags center 400;")


def stations_key(lat, lon):
    snap5 = lambda v: round(round(v / STATIONS_CELL_DEG) * STATIONS_CELL_DEG, 4)
    return f"stations_{snap5(lat):.2f}_{snap5(lon):.2f}"


def search_key(text, lat, lon):
    h = hashlib.sha1(f"{' '.join(text.lower().split())}|{lat:.1f}|{lon:.1f}".encode()).hexdigest()[:20]
    return "search_" + h


# ---- the index of everything seen so far (instant searches) ---------------------------------------------------------------

_FOLD_EXTRA = str.maketrans({"\u0142": "l", "\u0141": "l", "\u0111": "d", "\u0110": "d", "\u00f8": "o", "\u00d8": "o", "\u00df": "ss",
                             "\u0131": "i", "\u00e6": "ae", "\u0153": "oe"})


def fold(text):
    """Lower case without accents: "N\u00e1chod" and "nachod" are the same."""
    t = unicodedata.normalize("NFKD", str(text or "")).translate(_FOLD_EXTRA)
    return "".join(c for c in t if not unicodedata.combining(c)).casefold()


def anchor_of(key):
    """(lat, lon) a cache key names ("near3_50.216_15.814", "lines_305_50.4_16.2"), else None."""
    m = re.search(r"_(-?\d+\.\d+)_(-?\d+\.\d+)(?:\.json)?$", key)
    return (float(m.group(1)), float(m.group(2))) if m else None


def _near(lat, lon, la, lo, radius_m):
    k = math.cos(math.radians(lat)) * 111320
    return math.hypot((lo - lon) * k, (la - lat) * 110574) <= radius_m


class StopIndex:
    """The stops, stations and lines of every answer this service has fetched or kept, in memory. A name or a line number is
    found at once, even offline; the public servers are only asked for what is not known yet."""

    LINE_TAGS = ("ref", "name", "from", "to", "network", "operator", "colour", "route", "public_transport:version")

    def __init__(self):
        self.stops = {}               # (type, id) -> {id, lat, lon, name, tags}
        self.lines = {}               # relation id -> {id, tags, anchor}
        self._lock = threading.Lock()

    def add(self, text, anchor=None):
        try:
            data = json.loads(text) if isinstance(text, str) else text
            elements = data.get("elements", [])
        except (ValueError, AttributeError):
            return 0
        n = 0
        with self._lock:
            for e in elements:
                tags = e.get("tags") or {}
                t = e.get("type")
                if t == "relation":
                    if tags.get("type") == "route" and tags.get("ref") and e.get("id") is not None:
                        old = self.lines.get(e["id"])
                        self.lines[e["id"]] = {"id": e["id"], "tags": {k: tags[k] for k in self.LINE_TAGS if k in tags},
                                               "anchor": anchor or (old or {}).get("anchor")}
                        n += 1
                    continue
                name = tags.get("name")
                kind = tags.get("amenity") == "bus_station" or tags.get("highway") == "bus_stop" or tags.get("public_transport") in ("platform", "station")
                if not (name and kind and e.get("id") is not None):
                    continue
                lat, lon = e.get("lat"), e.get("lon")
                if lat is None and e.get("center"):
                    lat, lon = e["center"].get("lat"), e["center"].get("lon")
                if lat is None or lon is None:
                    continue
                self.stops[(t, e["id"])] = {"id": e["id"], "lat": lat, "lon": lon, "name": name,
                                            "tags": {k: tags[k] for k in ("name", "amenity", "highway", "public_transport", "bus") if k in tags}}
                n += 1
        return n

    def load(self, directory):
        """Everything in the cache folder (files {"t", "data"}); returns how many entries were indexed."""
        n = 0
        for f in pathlib.Path(directory).glob("*.json"):
            try:
                d = json.loads(f.read_text(encoding="utf-8"))
                n += self.add(d["data"], anchor_of(f.stem))
            except (OSError, ValueError, KeyError, TypeError):
                continue
        return n

    def search(self, text, lat, lon, radius=SEARCH_M, limit=120):
        """Elements (Overpass-like nodes) whose name holds every word of `text`, nearest to (lat, lon) first."""
        words = [w for w in fold(text).split() if w]
        if not words:
            return []
        out = []
        with self._lock:
            items = list(self.stops.values())
        for it in items:
            nm = fold(it["name"])
            if all(w in nm for w in words) and _near(lat, lon, it["lat"], it["lon"], radius):
                k = math.cos(math.radians(lat)) * 111320
                d = math.hypot((it["lon"] - lon) * k, (it["lat"] - lat) * 110574)
                out.append((d, {"type": "node", "id": it["id"], "lat": it["lat"], "lon": it["lon"], "tags": it["tags"]}))
        out.sort(key=lambda x: x[0])
        return [e for _, e in out[:limit]]

    def find_lines(self, ref, lat, lon, radius=SEARCH_M):
        """Relation heads whose number is `ref` (any case), known to be near (lat, lon) or of unknown place."""
        want = fold(ref).strip()
        if not want:
            return []
        out = []
        with self._lock:
            items = list(self.lines.values())
        for it in items:
            if fold(it["tags"].get("ref")) != want:
                continue
            a = it.get("anchor")
            if a is not None and not _near(lat, lon, a[0], a[1], radius + 5000):
                continue
            out.append({"type": "relation", "id": it["id"], "tags": it["tags"], "members": []})
        return out


def clean_ref(text):
    """The line number as typed, or None when it is not one (letters, digits, - and / only, at most 8, with a digit)."""
    t = (text or "").strip()
    return t if re.fullmatch(r"[A-Za-z0-9/-]{1,8}", t) and re.search(r"\d", t) else None


def lines_query(ref, lat, lon, radius=SEARCH_M):
    r = clean_ref(ref)
    if r is None:
        raise ValueError("not a line number")
    return (f'[out:json][timeout:50];rel[type=route][route~"{MODES}"][ref="{r}"](around:{int(radius)},{lat:.4f},{lon:.4f});out tags;')


def lines_key(ref, lat, lon):
    return f"lines_{re.sub(r'[^A-Za-z0-9]', '', fold(ref))}_{round(lat, 1):.1f}_{round(lon, 1):.1f}"


# ---- what the service is doing (for the progress bar) -----------------------------------------------------------------

class Activity:
    """The slow things in flight: {id, what, label, state, mirror, of, since}. The mod asks /v1/progress about once a second
    while it waits, and shows it."""

    def __init__(self):
        self._lock = threading.Lock()
        self._items = {}
        self._n = 0

    def begin(self, what, label=""):
        with self._lock:
            self._n += 1
            self._items[self._n] = {"id": self._n, "what": what, "label": label, "state": "waiting", "mirror": 0, "of": 0,
                                    "since": time.monotonic()}
            return self._n

    def update(self, token, **kw):
        with self._lock:
            if token in self._items:
                self._items[token].update(kw)

    def end(self, token):
        with self._lock:
            self._items.pop(token, None)

    def snapshot(self):
        now = time.monotonic()
        with self._lock:
            items = [dict(i, elapsed=round(now - i["since"], 1)) for i in self._items.values()]
        for i in items:
            i.pop("since", None)
        items.sort(key=lambda i: i["id"])
        return {"busy": items, "waiting": sum(1 for i in items if i["state"] == "waiting")}


ACTIVITY = Activity()
CURRENT = threading.local()                  # the cache key of the request this thread is serving: the label of its progress;
                                             # .wanted: does the game still wait for this thread's answer (its connection)


class Abandoned(RuntimeError):
    """Nobody waits for the answer any more (the game closed the connection, the menu was closed): no new request is sent."""


class Interest:
    """The keys somebody asked for lately (a lease of LEASE_S): a fetch nobody waits for directly (the partial nearby) goes on
    while the open menu keeps asking, and stops when it does not."""

    def __init__(self, clock=time.monotonic):
        self._lock = threading.Lock()
        self._until = {}
        self.clock = clock

    def touch(self, key, seconds=None):
        with self._lock:
            self._until[key] = self.clock() + (LEASE_S if seconds is None else seconds)

    def alive(self, key):
        with self._lock:
            return self._until.get(key, 0) > self.clock()


INTEREST = Interest()


def client_gone(sock):
    """Has the other end closed this connection? (A GET sends nothing more after its headers: readable means closed.)"""
    try:
        r, _, _ = select.select([sock], [], [], 0)
        if not r:
            return False
        return sock.recv(1, socket.MSG_PEEK) == b""
    except (OSError, ValueError):
        return True


def still_wanted():
    """For the public-server loops: False once nobody waits for this thread's answer (no check outside a request: True)."""
    w = getattr(CURRENT, "check", None)
    if w is None:
        return True
    try:
        return bool(w())
    except Exception:
        return True


def label_of(key):
    """"near3_50.2_15.8" -> "stops nearby", "route2_7185111" -> "route", ..."""
    kind = re.sub(r"[_\d].*$", "", key or "")
    return {"near": "stops nearby", "route": "route", "stations": "bus stations", "search": "search", "lines": "lines",
            "along": "stops along the road", "path": "road", "geo": "search"}.get(kind, kind)


# ---- the geocoder: names of places and stops, fast ----------------------------------------------------------------------

def photon_url(q, lat, lon, tags, limit):
    """tags: one "key:value" filter or a list of them (Photon ORs them): places and stops come in one answer."""
    tags = [tags] if isinstance(tags, str) else list(tags)
    qs = urllib.parse.urlencode([("q", q), ("lat", f"{lat:.4f}"), ("lon", f"{lon:.4f}"), ("limit", limit)] +
                                [("osm_tag", t) for t in tags])
    return f"{PHOTON}?{qs}"


def parse_photon(data, want):
    """[{id, name, lat, lon, kind, state, country, osm_key, osm_value}] of a Photon answer; want: "place" | "stop"."""
    out, seen = [], set()
    for f in (data or {}).get("features", []):
        pr = f.get("properties") or {}
        try:
            lon, lat = f["geometry"]["coordinates"][:2]
        except (KeyError, TypeError, ValueError):
            continue
        name = pr.get("name")
        if not name:
            continue
        key, val = pr.get("osm_key"), pr.get("osm_value")
        if want == "place":
            if key != "place" or val not in PLACE_KINDS:
                continue
        elif not (val in ("bus_station", "bus_stop") or (key == "public_transport" and val in ("platform", "station"))):
            continue
        sig = (name, round(lat, 3), round(lon, 3))
        if sig in seen:
            continue
        seen.add(sig)
        out.append({"id": pr.get("osm_id"), "name": name, "lat": lat, "lon": lon, "kind": val, "state": pr.get("state"),
                    "country": pr.get("countrycode"), "osm_key": key, "osm_value": val})
    return out


def photon_get(url):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=PHOTON_TIMEOUT_S) as r:
        return json.loads(r.read(MAX_BYTES).decode("utf-8"))


PHOTON_TAGS = ("place", "amenity:bus_station", "highway:bus_stop")


def geo_search(q, lat, lon, getter=None, clock=time.monotonic):
    """Places and bus stops named like `q`, near (lat, lon): {"elements": [Overpass-like nodes of the stops], "places": [...],
    "source": "photon"}; RuntimeError when the geocoder does not answer (and for a minute after, without trying again: it is
    a free public service, and a search must not wait for its timeout every time). One request (~0.7 s): places and stops
    together."""
    global _photon_down_until
    if getter is None and clock() < _photon_down_until:
        raise RuntimeError("photon: resting after a failure")
    getter = getter or photon_get
    try:
        data = getter(photon_url(q, lat, lon, PHOTON_TAGS, 30))
    except (urllib.error.URLError, OSError, ValueError, TimeoutError) as e:
        _photon_down_until = clock() + PHOTON_COOLDOWN_S
        raise RuntimeError(f"photon: {type(e).__name__}")
    places = parse_photon(data, "place")
    places.sort(key=lambda p: -PLACE_KINDS.get(p["kind"], 0))
    stops = parse_photon(data, "stop")
    stops.sort(key=lambda it: it["osm_value"] != "bus_station")          # bus stations first
    elements = []
    for it in stops:
        tags = {"name": it["name"]}
        tags["amenity" if it["osm_value"] == "bus_station" else "highway"] = it["osm_value"]
        elements.append({"type": "node", "id": it["id"], "lat": it["lat"], "lon": it["lon"], "tags": tags})
    return {"elements": elements, "places": [{k: p[k] for k in ("name", "lat", "lon", "kind", "state", "country")} for p in places],
            "source": "photon"}


def geo_key(q, lat, lon):
    h = hashlib.sha1(f"{' '.join(fold(q).split())}|{lat:.1f}|{lon:.1f}".encode()).hexdigest()[:20]
    return "geo_" + h


# ---- cache ----------------------------------------------------------------------------------------------------------

# ---- towns from this computer: GeoNames (the towns of the countries round the player, downloaded once) ---------------------

GEONAMES = "https://download.geonames.org/export/dump/"
GEONAMES_BASE = "cities15000"         # every town of 15 000 people or more in the world: which countries are round a point
GEONAMES_MAX_BYTES = 100 * 1024 * 1024
GEONAMES_REFRESH_S = 30 * 86400
COUNTRY_NEAR_M = 60000                # the countries of the big towns this near a point are loaded
PLACE_SKIP = {"PPLX", "PPLH", "PPLQ", "PPLW", "PPLCH"}     # parts of towns, historical, abandoned, destroyed


def place_kind(code, pop):
    if code == "PPLC" or pop >= 50000:
        return "city"
    if code in ("PPLA", "PPLA2") or pop >= 3000:
        return "town"
    return "village"


def parse_geonames(lines, keep_alt=False):
    """{geonameid: (name, folded names, lat, lon, kind, population, country, folded other names)} of the populated places of
    a GeoNames dump (other names, "Prague" for Praha, only with keep_alt)."""
    out = {}
    for line in lines:
        f = line.rstrip("\n").split("\t")
        if len(f) < 15 or f[6] != "P" or f[7] in PLACE_SKIP:
            continue
        try:
            lat, lon, pop = float(f[4]), float(f[5]), int(f[14] or 0)
        except ValueError:
            continue
        names = {n for n in (fold(f[1]), fold(f[2])) if n}
        alt = {fold(a) for a in f[3].split(",") if a} - names if keep_alt else ()
        out[f[0]] = (f[1], tuple(names), lat, lon, place_kind(f[7], pop), pop, f[8], tuple(n for n in alt if n))
    return out


def download_file(url, dest, max_bytes=GEONAMES_MAX_BYTES, progress=None):
    """Download to dest (through dest.part); progress(done, total) about every megabyte."""
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=60) as r:
        size = int(r.headers.get("Content-Length") or 0)
        if size > max_bytes:
            raise ValueError(f"{size // 1048576} MB is too big")
        tmp = dest.with_suffix(".part")
        with open(tmp, "wb") as f:
            got = 0
            while True:
                b = r.read(65536)
                if not b:
                    break
                got += len(b)
                if got > max_bytes:
                    raise ValueError("too big")
                f.write(b)
                if progress and got // 1048576 != (got - len(b)) // 1048576:
                    progress(got, size)
    os.replace(tmp, dest)


def _dist_m(lat, lon, la, lo):
    k = math.cos(math.radians(lat)) * 111320
    return math.hypot((lo - lon) * k, (la - lat) * 110574)


class Gazetteer:
    """Cities, towns and villages known on this computer: a name is found in milliseconds and the map of towns needs no
    public server. The world's big towns (GeoNames cities15000, 3 MB) tell which countries are round the player; those
    countries' files (Czechia 1.6 MB) come once, in the background, and are refreshed monthly. Data (c) GeoNames, CC BY 4.0.
    Without a folder it knows nothing (and downloads nothing)."""

    def __init__(self, directory=None, fetch=download_file, clock=time.time):
        self.dir = pathlib.Path(directory) if directory else None
        self.fetch, self.clock = fetch, clock
        self.places = {}              # geonameid -> tuple (parse_geonames)
        self.base = {}
        self.countries = set()        # loaded
        self.failed = {}              # country -> when it failed (not tried again for an hour)
        self._lock = threading.Lock()
        self._busy = threading.Lock()
        self._grid = {}
        self._near = {}
        self._words = {}
        self.after = None             # called with (lat, lon) when the countries round a point are loaded

    @property
    def enabled(self):
        return self.dir is not None

    def _file(self, name):
        """The local copy of a GeoNames file (downloaded when missing or a month old); None when it cannot be had."""
        dest = self.dir / f"{name}.zip"
        fresh = dest.is_file() and self.clock() - dest.stat().st_mtime < GEONAMES_REFRESH_S
        if not fresh:
            token = ACTIVITY.begin("geonames", f"towns ({name})")
            try:
                ACTIVITY.update(token, state="running", mirror=1, of=1)
                self.dir.mkdir(parents=True, exist_ok=True)
                self.fetch(GEONAMES + f"{name}.zip", dest)
                say(f"towns: downloaded {name}.zip ({dest.stat().st_size // 1024} KB)")
            except (urllib.error.URLError, OSError, ValueError, TimeoutError) as e:
                say(f"towns: {name}.zip: {type(e).__name__} {str(e)[:80]}")
                if not dest.is_file():
                    return None                                   # an old copy is better than none
            finally:
                ACTIVITY.end(token)
        return dest

    def _read(self, name, keep_alt=False):
        path = self._file(name)
        if path is None:
            return None
        try:
            with zipfile.ZipFile(path) as z:
                with z.open(f"{name}.txt") as f:
                    return parse_geonames(io.TextIOWrapper(f, encoding="utf-8"), keep_alt)
        except (OSError, KeyError, ValueError, zipfile.BadZipFile) as e:
            say(f"towns: {name}.zip unreadable: {e}")
            return None

    def _add(self, rows):
        with self._lock:
            places = dict(self.places)
            for gid, p in rows.items():
                old = places.get(gid)
                if old and old[7] and not p[7]:
                    p = p[:7] + (old[7],)                 # a country's row keeps the other names the world file gave
                places[gid] = p
            grid, words = {}, {}
            for gid, p in places.items():
                grid.setdefault((int(p[2] // 0.5), int(p[3] // 0.5)), []).append(gid)
                for n in p[1] + p[7]:
                    for w in n.split():
                        words.setdefault(w[:2], set()).add(gid)
            self.places, self._grid, self._words = places, grid, words

    def countries_near(self, lat, lon):
        key = (round(lat, 1), round(lon, 1), len(self.base))
        if key not in self._near:
            self._near[key] = self._countries_near(lat, lon)
        return self._near[key]

    def _countries_near(self, lat, lon):
        out = []
        for p in sorted(self.base.values(), key=lambda p: _dist_m(lat, lon, p[2], p[3]))[:40]:
            if (_dist_m(lat, lon, p[2], p[3]) <= COUNTRY_NEAR_M or not out) and p[6] and p[6] not in out:
                out.append(p[6])
        return out[:3]

    def ensure(self, lat, lon):
        """Load (download when needed) the base file and the countries round (lat, lon). Blocking; one at a time."""
        if not self.enabled:
            return False
        with self._busy:
            if not self.base:
                base = self._read(GEONAMES_BASE, keep_alt=True)
                if base is None:
                    return False
                self.base = base
                self._add(base)
            for cc in self.countries_near(lat, lon):
                if cc in self.countries or self.clock() - self.failed.get(cc, -1e9) < 3600:
                    continue
                rows = self._read(cc)
                if rows is None:
                    self.failed[cc] = self.clock()
                    continue
                self.countries.add(cc)
                self._add(rows)
                say(f"towns: {cc} loaded, {len(rows)} places")
        if self.after:
            self.after(lat, lon)
        return True

    def preload(self):
        """At start: the base file and every country file already here (no download but a stale base)."""
        if not self.enabled or not self.dir.is_dir():
            return
        with self._busy:
            if not self.base:
                self.base = self._read(GEONAMES_BASE, keep_alt=True) or {}
                self._add(self.base)
            for f in sorted(self.dir.glob("??.zip")):
                cc = f.stem
                if cc not in self.countries:
                    rows = self._read(cc)
                    if rows:
                        self.countries.add(cc)
                        self._add(rows)
        if self.places:
            say(f"towns: {len(self.places)} places on this computer ({', '.join(sorted(self.countries)) or 'big towns only'})")

    def want(self, lat, lon):
        """ensure() in the background (a search answers with what is loaded now)."""
        if self.enabled and not self._busy.locked() and not self.ready(lat, lon):
            threading.Thread(target=self.ensure, args=(lat, lon), daemon=True).start()
        elif self.after and self.base:
            self.after(lat, lon)

    def ready(self, lat, lon):
        return bool(self.base) and all(cc in self.countries for cc in self.countries_near(lat, lon))

    @staticmethod
    def _row(p, dist):
        return {"name": p[0], "lat": p[2], "lon": p[3], "kind": p[4], "population": p[5], "country": p[6], "dist": round(dist)}

    # how well a name answers what was typed: the name itself, a name starting with it, words starting with the words;
    # another language's name a little less; then nearer and bigger (25 km weigh as much as ten times the people)
    MATCH_COST = {"exact": 0.0, "start": 0.5, "words": 1.0}
    OTHER_NAME_COST = 1.5

    @staticmethod
    def _match(q, words, names):
        best = None
        for n in names:
            if n == q:
                return "exact"
            if n.startswith(q):
                best = "start"
            elif best is None:
                parts = n.split()
                if all(any(pt.startswith(w) for pt in parts) for w in words):
                    best = "words"
        return best

    def search(self, text, lat, lon, limit=8):
        """Places whose name's words start with the words typed ("suchy d" finds Suchý Důl), the best first (see MATCH_COST)."""
        q = " ".join(fold(text).split())
        words = q.split()
        if not words:
            return []
        with self._lock:
            places, index = self.places, self._words
        cands = None
        for w in words:
            got = index.get(w[:2], set()) if len(w) >= 2 else None
            if got is None:
                continue
            cands = set(got) if cands is None else cands & got
        if cands is None:
            return []
        hits = []
        for gid in cands:
            p = places[gid]
            m = self._match(q, words, p[1])
            cost = self.MATCH_COST[m] if m else None
            if cost is None:
                m = self._match(q, words, p[7])
                if not m:
                    continue
                cost = self.MATCH_COST[m] + self.OTHER_NAME_COST
            d = _dist_m(lat, lon, p[2], p[3])
            hits.append((cost + d / 25000 - math.log10(p[5] + 10), p, d))
        hits.sort(key=lambda h: h[0])
        out, seen = [], set()
        for _, p, d in hits:
            sig = (p[0], round(p[2], 2), round(p[3], 2))
            if sig in seen:
                continue
            seen.add(sig)
            out.append(self._row(p, d))
            if len(out) >= limit:
                break
        return out

    def in_box(self, box):
        """The places (rows of parse_geonames) inside (lat0, lon0, lat1, lon1)."""
        with self._lock:
            grid, places = self._grid, self.places
        out = []
        for gy in range(int(box[0] // 0.5), int(box[2] // 0.5) + 1):
            for gx in range(int(box[1] // 0.5), int(box[3] // 0.5) + 1):
                for gid in grid.get((gy, gx), ()):
                    p = places[gid]
                    if box[0] <= p[2] <= box[2] and box[1] <= p[3] <= box[3]:
                        out.append(p)
        return out

    def towns(self, lat, lon, radius=TOWNS_M):
        """The places within `radius`, the biggest first (as slim_towns)."""
        with self._lock:
            grid, places = self._grid, self.places
        out, cy, cx = [], int(lat // 0.5), int(lon // 0.5)
        for gy in range(cy - 1, cy + 2):
            for gx in range(cx - 2, cx + 3):          # a degree of longitude is shorter
                for gid in grid.get((gy, gx), ()):
                    p = places[gid]
                    d = _dist_m(lat, lon, p[2], p[3])
                    if d <= radius:
                        out.append(self._row(p, d))
        out.sort(key=lambda t: (-TOWN_RANK[t["kind"]], -t["population"], t["name"]))
        return out


# ---- speed limits: the towns round a road (the mod works out "built-up" from them) -------------------------------------------

TOWN_RADII = ((100000, 3000), (30000, 2400), (10000, 2000), (3000, 1600), (500, 1200))     # population -> built-up radius, m
TOWN_RADIUS_MIN_M = 1000
TOWN_RADIUS_MAX_M = 3000
LIMIT_STEP_M = 400                 # the road is looked at this often (a longer road: a longer step, at most LIMIT_SAMPLES points)
LIMIT_SAMPLES = 1500


def town_radius(population):
    """How far from its centre a town's built-up area is taken to reach: 1 km for a hamlet, 3 km for a big city."""
    for pop, radius in TOWN_RADII:
        if population >= pop:
            return radius
    return TOWN_RADIUS_MIN_M


def road_samples(road, step=LIMIT_STEP_M, cap=LIMIT_SAMPLES):
    """Points along a road [(lat, lon) ...] at most `step` metres apart (more apart on a very long road, `cap` points at most)."""
    legs = [hav(a, b) for a, b in zip(road, road[1:])]
    step = max(step, sum(legs) / cap) if legs else step
    out = list(road[:1])
    for a, b, d in zip(road, road[1:], legs):
        n = int(d // step)
        for k in range(1, n + 1):
            f = k * step / d
            out.append((a[0] + (b[0] - a[0]) * f, a[1] + (b[1] - a[1]) * f))
        out.append(b)
    return out


def road_limits(places, road):
    """What the mod needs to know the speed limit where the map does not say: {"cc": "CZ", "towns": [[lat, lon, radius_m]]}
    for the towns whose built-up area (town_radius) the road touches; the country is the nearest town's. None for no data."""
    if not places or len(road) < 2:
        return None
    samples = road_samples(road)
    lats, lons = [p[0] for p in samples], [p[1] for p in samples]
    margin = 0.06                                         # degrees: a bit over the biggest radius
    box = (min(lats) - margin, min(lons) - margin, max(lats) + margin, max(lons) + margin)
    # the road's points on a grid of cells as big as the biggest town radius: a town looks only at the 3 x 3 cells round it
    # (a city line: 12 000 places x 2 600 points were 32 million distances, 7 s for each opening of a Berlin line)
    kx = math.cos(math.radians(samples[0][0])) * 111320
    cell = float(TOWN_RADIUS_MAX_M)
    grid = {}
    for la, lo in samples:
        grid.setdefault((int(la * 110574 // cell), int(lo * kx // cell)), []).append((la, lo))
    probe = samples[::max(1, len(samples) // 16)] + samples[-1:]      # (the country: the nearest town also when it is farther)
    towns, nearest = [], None
    for p in places(box):
        cy, cx = int(p[2] * 110574 // cell), int(p[3] * kx // cell)
        best = float("inf")
        for dy in (-1, 0, 1):
            for dx in (-1, 0, 1):
                for la, lo in grid.get((cy + dy, cx + dx), ()):
                    d = _dist_m(p[2], p[3], la, lo)
                    if d < best:
                        best = d
        if best > cell:
            best = min(_dist_m(p[2], p[3], la, lo) for la, lo in probe)
        if nearest is None or best < nearest[0]:
            nearest = (best, p[6])
        if best <= town_radius(p[5]):
            towns.append([round(p[2], 5), round(p[3], 5), town_radius(p[5])])
    cc = nearest[1] if nearest and nearest[0] <= 10000 and nearest[1] else None
    return {"cc": cc, "towns": towns}


# ---- timetables from this computer: GTFS (every line of a country with its real timetable, downloaded once) ----------------

GTFS_FEEDS = {
    # country -> its national feed. CZ: every bus line except Prague (PID), Brno (IDS JMK), Flixbus and Plzeň, made from the
    # state's timetable register (CIS JR) by the JrUtil project; the data of CIS JR carry no conditions, stop positions come
    # from OpenStreetMap (ODbL) and open data of towns (CC BY / CC BY-SA / CC0).
    "CZ": {"url": "https://data.jr.ggu.cz/results/latest/JDF_merged_GTFS.zip", "label": "CIS JR (JrUtil)", "mb": 130},
}
GTFS_SCHEMA = "2"                    # the index's layout: an index of another layout is built again
GTFS_DAYS = 28                       # the days from the build day that the index knows the running trips of
GTFS_REFRESH_S = 7 * 86400
GTFS_MAX_BYTES = 600 * 1024 * 1024
GTFS_ROUTE = 10 ** 12                # relation ids of lines made from GTFS: GTFS_ROUTE + pattern
GTFS_NODE = 2 * 10 ** 12             # node ids of stops that OpenStreetMap does not have: GTFS_NODE + stop
GTFS_SAME_STOP_M = 40                # a GTFS stop this near an OpenStreetMap bus stop is that stop
GTFS_VARIANTS = 5                    # lines of one number shown at a place (most trips first)
BUS_ROUTE_TYPES = ("", "3", "11")


def gtfs_secs(t):
    """Seconds of "07:05:00" (hours may pass 24: a trip after midnight), None when empty."""
    try:
        h, m, s = t.strip().split(":")
        return int(h) * 3600 + int(m) * 60 + int(s)
    except (ValueError, AttributeError):
        return None


def _bus_route(t):
    """Buses, trolleybuses, coaches: route_type 3, 11 and the extended 200s (coach), 700s (bus), 800s (trolleybus)."""
    t = (t or "").strip()
    return t in BUS_ROUTE_TYPES or (t.isdigit() and (200 <= int(t) < 300 or 700 <= int(t) < 900))


def gtfs_ref(short, long_name):
    """The number the public knows a line by. A national JDF feed has a 6-digit register code as the short name (641361) and
    the number first in the long name ("361 Police n.Met.-Machov"); when the name has none, the last three digits of the code
    ("000512" is line 512). Other feeds' short names are the numbers."""
    short, long_name = (short or "").strip(), (long_name or "").strip()
    first = long_name.split()[0].rstrip(":") if long_name else ""
    if short.isdigit() and len(short) >= 6:
        if first and re.fullmatch(r"[\w/\-]{1,8}", first) and re.search(r"\d", first):
            return first
        return short[-3:].lstrip("0") or short
    return short or first


def fold_words(text):
    """"Police n.Met.,aut.st." -> "police n met aut st": the folded words, one space between."""
    return " ".join(re.findall(r"\w+", fold(text)))


def build_gtfs_index(zip_path, db_path, today, days=GTFS_DAYS, progress=None, ref_fn=None):
    """Index a GTFS zip into an sqlite file: stops, the patterns (one line's one way of going: its stops with their times
    from the start) with how many trips run on the next `days` days from `today` (a datetime.date), and the departures with a
    bit per day. Streams the files: stop_times.txt is a gigabyte for a country. Returns {stops, patterns, trips}.
    `ref_fn(route_short_name, route_long_name)` gives the number of a line (default gtfs_ref: made for the Czech national feed)."""
    import csv
    import datetime
    import sqlite3
    say_p = progress or (lambda *_: None)
    z = zipfile.ZipFile(zip_path)

    def reader(name):
        f = io.TextIOWrapper(z.open(name), encoding="utf-8-sig", newline="")
        r = csv.reader(f)
        head = next(r, [])
        return r, {h.strip(): i for i, h in enumerate(head)}

    def col(idx, row, name, default=""):
        i = idx.get(name)
        return row[i] if i is not None and i < len(row) else default

    agencies = {}
    if "agency.txt" in z.namelist():
        r, ix = reader("agency.txt")
        for row in r:
            agencies[col(ix, row, "agency_id")] = col(ix, row, "agency_name")
    say_p("routes", 0.02)
    routes = {}
    r, ix = reader("routes.txt")
    for row in r:
        if _bus_route(col(ix, row, "route_type")):
            ref = (ref_fn or gtfs_ref)(col(ix, row, "route_short_name"), col(ix, row, "route_long_name"))
            routes[col(ix, row, "route_id")] = (ref, col(ix, row, "route_long_name"), agencies.get(col(ix, row, "agency_id"), ""))
    say_p("trips", 0.04)
    trips, services = {}, set()
    r, ix = reader("trips.txt")
    for row in r:
        rid = col(ix, row, "route_id")
        if rid in routes:
            sid = col(ix, row, "service_id")
            trips[col(ix, row, "trip_id")] = (rid, sys.intern(sid), col(ix, row, "trip_headsign"))
            services.add(sid)
    say_p("calendar", 0.08)
    dates = [today + datetime.timedelta(days=i) for i in range(days)]
    keys = [d.strftime("%Y%m%d") for d in dates]
    mask = {}
    if "calendar.txt" in z.namelist():
        r, ix = reader("calendar.txt")
        wd = ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]
        for row in r:
            sid = col(ix, row, "service_id")
            if sid not in services:
                continue
            a, b = col(ix, row, "start_date"), col(ix, row, "end_date")
            m = 0
            for i, d in enumerate(dates):
                if a <= keys[i] <= b and col(ix, row, wd[d.weekday()]) == "1":
                    m |= 1 << i
            if m:
                mask[sid] = m
    if "calendar_dates.txt" in z.namelist():
        r, ix = reader("calendar_dates.txt")
        where = {k: i for i, k in enumerate(keys)}
        for row in r:
            sid = col(ix, row, "service_id")
            i = where.get(col(ix, row, "date"))
            if i is None or sid not in services:
                continue
            if col(ix, row, "exception_type") == "1":
                mask[sid] = mask.get(sid, 0) | (1 << i)
            elif col(ix, row, "exception_type") == "2" and sid in mask:
                mask[sid] &= ~(1 << i)
    trips = {t: v for t, v in trips.items() if mask.get(v[1])}
    say_p("times", 0.12)

    patterns, deps = {}, []                # (route, stops) -> [pid, offsets]; (pid, start, mask)
    counts = {}
    n_trips = 0

    def finish(tid, rows):
        nonlocal n_trips
        t = trips.get(tid)
        if t is None or len(rows) < 2:
            return
        if any(rows[i][0] > rows[i + 1][0] for i in range(len(rows) - 1)):
            rows.sort(key=lambda x: x[0])
        times = [x[2] if x[2] is not None else x[3] for x in rows]
        if times[0] is None:
            return
        t0 = times[0]
        offs, last = [], 0
        for tm in times:
            tm = last if tm is None else tm - t0
            last = max(last, tm)
            offs.append(last)
        key = (t[0], tuple(x[1] for x in rows))
        p = patterns.get(key)
        if p is None:
            p = patterns[key] = [len(patterns) + 1, offs, t[2]]
        deps.append((p[0], t0, mask[t[1]]))
        counts[p[0]] = counts.get(p[0], 0) + 1
        n_trips += 1

    size = max(1, sum(i.file_size for i in z.infolist() if i.filename == "stop_times.txt"))
    r, ix = reader("stop_times.txt")
    i_t, i_s, i_a, i_d, i_q = (ix.get(n, -1) for n in ("trip_id", "stop_id", "arrival_time", "departure_time", "stop_sequence"))
    cur, rows, nrow = None, [], 0
    for row in r:
        tid = row[i_t]
        if tid != cur:
            if cur is not None:
                finish(cur, rows)
            cur, rows = tid, []
        try:
            seq = int(row[i_q])
        except (ValueError, IndexError):
            seq = len(rows)
        rows.append((seq, row[i_s], gtfs_secs(row[i_a]) if i_a >= 0 else None, gtfs_secs(row[i_d]) if i_d >= 0 else None))
        nrow += 1
        if nrow % 500000 == 0:
            say_p("times", 0.12 + 0.7 * min(1.0, nrow * 85 / size))
    if cur is not None:
        finish(cur, rows)
    say_p("writing", 0.85)

    tmp = pathlib.Path(str(db_path) + ".part")
    if tmp.exists():
        tmp.unlink()
    db = sqlite3.connect(str(tmp))
    db.executescript("""
        CREATE TABLE stops(sid TEXT PRIMARY KEY, name TEXT, fname TEXT, lat REAL, lon REAL, refs TEXT);
        CREATE TABLE patterns(pid INTEGER PRIMARY KEY, ref TEXT, name TEXT, agency TEXT, head TEXT, n INTEGER,
                              stops TEXT, offs TEXT, trips INTEGER);
        CREATE TABLE sp(sid TEXT, pid INTEGER, pos INTEGER);
        CREATE TABLE deps(pid INTEGER, start INTEGER, mask INTEGER);
        CREATE TABLE meta(k TEXT PRIMARY KEY, v TEXT);
    """)
    used = {}                                      # stop -> the line numbers calling there
    for (rid, stops), (pid, offs, head) in patterns.items():
        ref, lname, agency = routes[rid]
        for st in stops:
            used.setdefault(st, set()).add(ref)
        db.execute("INSERT INTO patterns VALUES (?,?,?,?,?,?,?,?,?)",
                   (pid, ref, lname, agency, head, len(stops), ",".join(stops), ",".join(map(str, offs)), counts.get(pid, 0)))
        db.executemany("INSERT INTO sp VALUES (?,?,?)", [(s, pid, k) for k, s in enumerate(stops)])
    db.executemany("INSERT INTO deps VALUES (?,?,?)", deps)
    r, ix = reader("stops.txt")
    n_stops = 0
    for row in r:
        sid = col(ix, row, "stop_id")
        if sid not in used:
            continue
        try:
            lat, lon = float(col(ix, row, "stop_lat")), float(col(ix, row, "stop_lon"))
        except ValueError:
            continue
        name = col(ix, row, "stop_name")
        db.execute("INSERT INTO stops VALUES (?,?,?,?,?,?)", (sid, name, fold_words(name), lat, lon, ",".join(sorted(used[sid]))))
        n_stops += 1
    db.executescript("CREATE INDEX stops_lat ON stops(lat); CREATE INDEX sp_sid ON sp(sid); CREATE INDEX sp_pid ON sp(pid);"
                     "CREATE INDEX deps_pid ON deps(pid); CREATE INDEX patterns_ref ON patterns(ref);")
    db.execute("INSERT INTO meta VALUES ('today', ?)", (today.strftime("%Y%m%d"),))
    db.execute("INSERT INTO meta VALUES ('days', ?)", (str(days),))
    db.execute("INSERT INTO meta VALUES ('schema', ?)", (GTFS_SCHEMA,))
    db.commit()
    db.close()
    os.replace(tmp, db_path)
    say_p("ready", 1.0)
    return {"stops": n_stops, "patterns": len(patterns), "trips": n_trips}


class Gtfs:
    """The national timetables on this computer: lines near a place (made to look like OpenStreetMap's route relations, so
    the mod needs nothing new), stops by name, the departures of a line. Each country's feed is downloaded once (130 MB for
    Czechia), indexed in a few minutes in the background (progress shown in the menu) and refreshed weekly. Without a folder
    it knows nothing and downloads nothing."""

    def __init__(self, directory=None, fetch=download_file, clock=time.time, feeds=None, today=None):
        import datetime
        self.dir = pathlib.Path(directory) if directory else None
        self.fetch, self.clock = fetch, clock
        self.feeds = GTFS_FEEDS if feeds is None else feeds
        self.today = today or datetime.date.today
        self.dbs = {}                        # country -> sqlite connection
        self.state = {}                      # country -> {"state": "downloading|indexing|ready|failed", "pct", "error"}
        self.failed = {}
        self._lock = threading.RLock()       # one reader at a time (the connections are shared), and a rebuild swaps under it
        self._building = set()
        self.old = set()                     # countries whose index has an older layout (built again)

    @property
    def enabled(self):
        return self.dir is not None

    def _path(self, cc):
        return self.dir / f"gtfs_{cc}.db"

    def preload(self):
        if not self.enabled or not self.dir.is_dir():
            return
        for cc in self.feeds:
            if self._path(cc).is_file():
                self._open(cc)

    def _open(self, cc):
        import sqlite3
        with self._lock:
            old = self.dbs.pop(cc, None)
            if old is not None:
                old.close()
            try:
                db = sqlite3.connect(str(self._path(cc)), check_same_thread=False)
                row = db.execute("SELECT v FROM meta WHERE k='schema'").fetchone()
            except sqlite3.Error as e:
                say(f"timetables: {cc} unreadable: {e}")
                return False
            if not row or row[0] != GTFS_SCHEMA:
                db.close()
                self.old.add(cc)
                say(f"timetables: {cc} is of an older layout; it is built again")
                return False
            self.dbs[cc] = db
            self.state[cc] = {"state": "ready", "pct": 1.0}
            say(f"timetables: {cc} ready ({db.execute('SELECT COUNT(*) FROM patterns').fetchone()[0]} lines' ways)")
            return True

    def ready(self, cc=None):
        return bool(self.dbs) if cc is None else cc in self.dbs

    def stale(self, cc):
        p = self._path(cc)
        return cc in self.old or not p.is_file() or self.clock() - p.stat().st_mtime > GTFS_REFRESH_S

    def want(self, countries):
        """Start getting (or refreshing) the feeds of these countries, in the background; those without a feed are skipped."""
        if not self.enabled:
            return
        for cc in countries:
            if cc in self.feeds and self.stale(cc) and cc not in self._building \
                    and self.clock() - self.failed.get(cc, -1e9) > 3600:
                self._building.add(cc)
                threading.Thread(target=self._build, args=(cc,), daemon=True).start()

    def _build(self, cc):
        feed = self.feeds[cc]
        token = ACTIVITY.begin("gtfs", f"timetables {cc}")
        zip_path = self.dir / f"gtfs_{cc}.zip"
        try:
            self.dir.mkdir(parents=True, exist_ok=True)
            self.state[cc] = {"state": "downloading", "pct": 0.0}
            ACTIVITY.update(token, state="running", mirror=1, of=2, label=f"timetables {cc}: downloading {feed.get('mb', '?')} MB")

            def got(done, total):
                pct = (done / total) if total else 0.0
                self.state[cc] = {"state": "downloading", "pct": round(pct, 3)}
                ACTIVITY.update(token, stage="download", done=done // 1048576, total=total // 1048576,
                                label=f"timetables {cc}: downloading {done // 1048576} of {total // 1048576} MB")
            self.fetch(feed["url"], zip_path, GTFS_MAX_BYTES, got)

            def step(what, pct):
                self.state[cc] = {"state": "indexing", "pct": round(pct, 3)}
                ACTIVITY.update(token, mirror=2, stage="index", pct=int(pct * 100),
                                label=f"timetables {cc}: indexing ({what}, {int(pct * 100)} %)")
            fresh = self._path(cc).with_suffix(".new")
            r = build_gtfs_index(zip_path, fresh, self.today(), progress=step)
            say(f"timetables: {cc} indexed: {r['stops']} stops, {r['patterns']} ways, {r['trips']} trips")
            with self._lock:                     # (Windows cannot replace a file that is open: the old index is closed first)
                db = self.dbs.pop(cc, None)
                if db is not None:
                    db.close()
                os.replace(fresh, self._path(cc))
                self.old.discard(cc)
                self._open(cc)
        except (urllib.error.URLError, OSError, ValueError, TimeoutError, zipfile.BadZipFile, KeyError) as e:
            self.failed[cc] = self.clock()
            self.state[cc] = {"state": "failed", "error": f"{type(e).__name__}: {str(e)[:100]}", "pct": 0.0}
            say(f"timetables: {cc} failed: {type(e).__name__} {str(e)[:120]}")
        finally:
            ACTIVITY.end(token)
            self._building.discard(cc)
            try:
                zip_path.unlink()
            except OSError:
                pass

    def status(self):
        return {"countries": sorted(self.feeds), "state": self.state, "ready": sorted(self.dbs)}

    def coming(self, countries):
        """Are the timetables of one of these countries being downloaded or prepared right now?"""
        return any(cc in self._building for cc in countries)

    # -- queries --

    def _stops_near(self, db, lat, lon, radius):
        dlat = radius / 110574.0
        dlon = radius / (111320.0 * max(0.2, math.cos(math.radians(lat))))
        rows = db.execute("SELECT sid, name, lat, lon, rowid FROM stops WHERE lat BETWEEN ? AND ? AND lon BETWEEN ? AND ?",
                          (lat - dlat, lat + dlat, lon - dlon, lon + dlon)).fetchall()
        return [r for r in rows if _dist_m(lat, lon, r[2], r[3]) <= radius]

    def _patterns_at(self, db, sids):
        out = {}
        sids = list(sids)
        for i in range(0, len(sids), 400):
            chunk = sids[i:i + 400]
            q = ("SELECT p.pid, p.ref, p.name, p.agency, p.head, p.n, p.stops, p.trips FROM sp JOIN patterns p USING(pid) "
                 f"WHERE sp.sid IN ({','.join('?' * len(chunk))}) GROUP BY p.pid")
            for r in db.execute(q, chunk):
                out[r[0]] = r
        return list(out.values())

    def _name_of(self, db, sid, cache):
        if sid not in cache:
            r = db.execute("SELECT name FROM stops WHERE sid=?", (sid,)).fetchone()
            cache[sid] = r[0] if r else ""
        return cache[sid]

    def lines_near(self, lat, lon, radius):
        """({"stops": [(sid, name, lat, lon, rowid)], "lines": [relation]}) of the lines calling within `radius` of a point:
        per number and way (first and last stop) the pattern with most trips, at most GTFS_VARIANTS per number."""
        with self._lock:
            out = {"stops": [], "lines": []}
            for cc, db in self.dbs.items():
                near = self._stops_near(db, lat, lon, radius)
                if not near:
                    continue
                by_sid = {s[0]: s for s in near}
                names = {}
                best = {}
                for pid, ref, lname, agency, head, n, stops, trips in self._patterns_at(db, by_sid):
                    sl = stops.split(",")
                    first, last = self._name_of(db, sl[0], names), self._name_of(db, sl[-1], names)
                    k = (fold(ref), first, last)
                    if k not in best or trips > best[k][0]:
                        best[k] = (trips, pid, ref, lname, agency, sl, first, last)
                per_ref = {}
                for k, v in sorted(best.items(), key=lambda kv: -kv[1][0]):
                    per_ref.setdefault(k[0], []).append(v)
                used = set()
                for ref_key, variants in per_ref.items():
                    for trips, pid, ref, lname, agency, sl, first, last in variants[:GTFS_VARIANTS]:
                        members, places = [], {}
                        for pos, sid in enumerate(sl):
                            if sid in by_sid:
                                places.setdefault(sid, []).append(pos + 1)
                        for sid, ps in places.items():
                            m = {"type": "node", "ref": sid, "role": "platform", "i": ps[0]}
                            if len(ps) > 1:
                                m["j"] = ps[-1]
                            members.append(m)
                            used.add(sid)
                        out["lines"].append({
                            "type": "relation", "id": GTFS_ROUTE + pid, "n": len(sl), "ordered": True, "members": members,
                            "tags": {"type": "route", "route": "bus", "ref": ref, "name": f"{ref}: {first} - {last}",
                                     "from": first, "to": last, "operator": agency, "public_transport:version": "2",
                                     "bus_routes:source": "gtfs", "bus_routes:trips": str(trips)}})
                out["stops"] += [by_sid[s] for s in used]
            return out

    def stops_around(self, lat, lon, radius):
        """[(name, lat, lon, {line numbers})] of the stops within `radius` that some line calls at."""
        dlat = radius / 110574.0
        dlon = radius / (111320.0 * max(0.2, math.cos(math.radians(lat))))
        out = []
        with self._lock:
            for db in self.dbs.values():
                rows = db.execute("SELECT name, lat, lon, refs FROM stops WHERE lat BETWEEN ? AND ? AND lon BETWEEN ? AND ?",
                                  (lat - dlat, lat + dlat, lon - dlon, lon + dlon)).fetchall()
                for name, la, lo, refs in rows:
                    if _dist_m(lat, lon, la, lo) <= radius:
                        out.append((name, la, lo, set((refs or "").split(",")) - {""}))
        return out

    def stops_named(self, text, lat, lon, radius=SEARCH_M, limit=40):
        """[(sid, name, lat, lon, rowid)] whose name's words start with the words typed, nearest first."""
        words = fold(text).split()
        if not words:
            return []
        with self._lock:
            out = []
            for db in self.dbs.values():
                dlat = radius / 110574.0
                dlon = radius / (111320.0 * max(0.2, math.cos(math.radians(lat))))
                words = fold_words(text).split() or words
                sql = ("SELECT sid, name, lat, lon, rowid FROM stops WHERE lat BETWEEN ? AND ? AND lon BETWEEN ? AND ?"
                       + "".join(" AND (fname LIKE ? OR fname LIKE ?)" for _ in words))
                args = [lat - dlat, lat + dlat, lon - dlon, lon + dlon]
                for w in words:
                    args += [w + "%", "% " + w + "%"]
                out += db.execute(sql, args).fetchall()
        out = [(r, _dist_m(lat, lon, r[2], r[3])) for r in out]
        out.sort(key=lambda x: x[1])
        return [r for r, d in out if d <= radius][:limit]

    def lines_numbered(self, ref, lat, lon, radius=SEARCH_M):
        """Relation heads of the lines with this number having a stop within `radius` (most trips first, per way)."""
        want = fold(ref).strip()
        if not want:
            return []
        with self._lock:
            out = []
            for db in self.dbs.values():
                dlat = radius / 110574.0
                dlon = radius / (111320.0 * max(0.2, math.cos(math.radians(lat))))
                rows = db.execute(
                    "SELECT DISTINCT p.pid, p.ref, p.agency, p.stops, p.trips FROM patterns p JOIN sp ON sp.pid=p.pid "
                    "JOIN stops s ON s.sid=sp.sid WHERE lower(p.ref)=? AND s.lat BETWEEN ? AND ? AND s.lon BETWEEN ? AND ?",
                    (want, lat - dlat, lat + dlat, lon - dlon, lon + dlon)).fetchall()
                names, best = {}, {}
                for pid, ref, agency, stops, trips in rows:
                    sl = stops.split(",")
                    k = (self._name_of(db, sl[0], names), self._name_of(db, sl[-1], names))
                    if k not in best or trips > best[k][0]:
                        best[k] = (trips, pid, ref, agency, k)
                for trips, pid, ref, agency, (first, last) in sorted(best.values(), key=lambda v: -v[0])[:GTFS_VARIANTS * 2]:
                    out.append({"type": "relation", "id": GTFS_ROUTE + pid, "members": [],
                                "tags": {"type": "route", "route": "bus", "ref": ref, "name": f"{ref}: {first} - {last}",
                                         "from": first, "to": last, "operator": agency, "public_transport:version": "2",
                                         "bus_routes:source": "gtfs"}})
            return out

    def pattern(self, rid):
        """{ref, name, agency, head, stops: [{sid, name, lat, lon, rowid, off}], today: [...], ...} of a GTFS_ROUTE id, or None."""
        pid = rid - GTFS_ROUTE
        with self._lock:
            for db in self.dbs.values():
                p = db.execute("SELECT ref, name, agency, head, stops, offs FROM patterns WHERE pid=?", (pid,)).fetchone()
                if p is None:
                    continue
                sl, offs = p[4].split(","), [int(x) for x in p[5].split(",")]
                got = {}
                for i in range(0, len(sl), 400):
                    chunk = list(dict.fromkeys(sl[i:i + 400]))
                    for r in db.execute(f"SELECT sid, name, lat, lon, rowid FROM stops WHERE sid IN ({','.join('?' * len(chunk))})", chunk):
                        got[r[0]] = r
                stops = [{"sid": s, "name": got[s][1], "lat": got[s][2], "lon": got[s][3], "rowid": got[s][4], "off": offs[k]}
                         for k, s in enumerate(sl) if s in got]
                meta = dict(db.execute("SELECT k, v FROM meta").fetchall())
                starts = self._starts(db, pid, meta)
                return {"ref": p[0], "name": p[1], "agency": p[2], "head": p[3], "stops": stops, "starts": starts}
        return None

    @staticmethod
    def _starts(db, pid, meta):
        """{"1": [start seconds], ... "7": [...]} of a way: its departures on a Monday (1) .. Sunday (7). Of the two such days in
        the next two weeks the busier one (a public holiday runs a Sunday timetable). A start may pass 86400 (after midnight)."""
        import datetime
        day0 = datetime.datetime.strptime(meta.get("today", "19700101"), "%Y%m%d").date()
        bits = {}
        for i in range(min(int(meta.get("days", "0")), 14)):
            bits.setdefault(str((day0 + datetime.timedelta(days=i)).isoweekday()), []).append(i)
        per_day = {}
        for start, mask in db.execute("SELECT start, mask FROM deps WHERE pid=? ORDER BY start", (pid,)):
            for wd, bs in bits.items():
                for b in bs:
                    if mask >> b & 1:
                        per_day.setdefault((wd, b), []).append(start)
        out = {}
        for wd, bs in bits.items():
            best = max((per_day.get((wd, b), []) for b in bs), key=len)
            out[wd] = best
        return out


def gtfs_node(row):
    """An Overpass-like node of a GTFS stop that OpenStreetMap does not have."""
    sid, name, lat, lon, rowid = row
    return {"type": "node", "id": GTFS_NODE + rowid, "lat": lat, "lon": lon,
            "tags": {"name": name, "highway": "bus_stop", "public_transport": "platform", "bus": "yes",
                     "bus_routes:source": "gtfs"}}


NEARBY_WAIT_S = 1.5                  # how long a nearby answer waits for the map server when the timetables have it already


def merge_gtfs(osm_text, found, partial=False):
    """The nearby answer of OpenStreetMap (text, or None when no server answered) with the lines of the timetables: a GTFS
    stop within 40 m of an OpenStreetMap bus stop is that stop (its id is used in the lines), the others are added as stops;
    an OpenStreetMap line whose number the timetables have is dropped (the timetable's line has all its stops, and in the
    right order). Returns the text."""
    data = json.loads(osm_text) if osm_text else {"elements": []}
    elements = data.get("elements", [])
    osm_stops = [e for e in elements if e.get("type") == "node" and e.get("lat") is not None
                 and ((e.get("tags") or {}).get("highway") == "bus_stop" or (e.get("tags") or {}).get("public_transport") == "platform")]
    ref_of = {}
    for sid, name, lat, lon, rowid in found["stops"]:
        hit, best = None, GTFS_SAME_STOP_M
        for e in osm_stops:
            d = _dist_m(lat, lon, e["lat"], e["lon"])
            if d <= best:
                hit, best = e, d
        if hit is not None:
            ref_of[sid] = hit["id"]
        else:
            n = gtfs_node((sid, name, lat, lon, rowid))
            elements.append(n)
            ref_of[sid] = n["id"]
    have = {fold(ln["tags"]["ref"]) for ln in found["lines"]}
    out = [e for e in elements if not (e.get("type") == "relation" and fold((e.get("tags") or {}).get("ref")) in have)]
    for ln in found["lines"]:
        for m in ln["members"]:
            m["ref"] = ref_of.get(m["ref"], m["ref"])
        out.append(ln)
    data["elements"] = out
    if partial:
        data["partial"] = True
    return json.dumps(data, separators=(",", ":"), ensure_ascii=False)


def merge_places(first, more, near_m=3000):
    """`first`, then those of `more` that are not the same town again (one name within 3 km)."""
    out = list(first)
    for p in more:
        if not any(fold(p.get("name")) == fold(o.get("name")) and _dist_m(p["lat"], p["lon"], o["lat"], o["lon"]) <= near_m
                   for o in out):
            out.append(p)
    return out[:10]


def merge_elements(first, more):
    seen = {(e.get("type"), e.get("id")) for e in first}
    return list(first) + [e for e in more if (e.get("type"), e.get("id")) not in seen]


# ---- connections (plan 006 stage C) -----------------------------------------------------------------------------------------

CONN_NEAR_M = 150            # stops this near the asked one are one hub
CONN_MAX = 40                # arrivals returned at most
FEATURES = FEATURES + ["connections"]


def gtfs_connections(gtfs, t, day, win_min=8, sid=None, lat=None, lon=None, ref=None, radius=CONN_NEAR_M):
    """The lines arriving at a hub within +-win_min minutes of `t` (seconds from midnight) on weekday `day`: the hub is the stop
    `sid` (or the point lat, lon) with the stops within `radius` metres. Only buses that go on from the previous stop (a way's
    first stop has no arrivals). `ref` (the line of the bus asking) is left out. Returns {"stops": n, "lines": distinct line
    numbers calling at the hub (ref included), "arrivals": [{ref, to, from, head, at (s from midnight), stop, pid}] by time,
    "source": "gtfs"}; empty arrivals when no timetables are here."""
    win = max(60, min(30, win_min) * 60)
    out = {"stops": 0, "lines": 0, "arrivals": [], "source": "gtfs"}
    skip = fold(ref).strip() if ref else None
    refs, found = set(), []
    with gtfs._lock:
        for db in gtfs.dbs.values():
            if sid is not None:
                row = db.execute("SELECT lat, lon FROM stops WHERE sid=?", (sid,)).fetchone()
                if row is None:
                    continue
                clat, clon = row
            elif lat is not None and lon is not None:
                clat, clon = lat, lon
            else:
                continue
            near = gtfs._stops_near(db, clat, clon, radius)
            if not near:
                continue
            out["stops"] += len(near)
            by_sid = {r[0]: r for r in near}
            meta = dict(db.execute("SELECT k, v FROM meta").fetchall())
            names, starts = {}, {}
            sids = list(by_sid)
            for i in range(0, len(sids), 400):
                chunk = sids[i:i + 400]
                q = ("SELECT sp.sid, sp.pos, p.pid, p.ref, p.head, p.stops, p.offs FROM sp JOIN patterns p USING(pid) "
                     f"WHERE sp.sid IN ({','.join('?' * len(chunk))})")
                for sd, pos, pid, pref, head, stops, offs in db.execute(q, chunk).fetchall():
                    refs.add(fold(pref))
                    if pos == 0 or (skip and fold(pref).strip() == skip):
                        continue
                    if pid not in starts:
                        starts[pid] = Gtfs._starts(db, pid, meta)
                    off = int(offs.split(",")[pos])
                    sl = stops.split(",")
                    for shift, d in ((0, day), (-86400, (day - 2) % 7 + 1)):      # last night's trips run on into today
                        for st in starts[pid].get(str(d), []):
                            at = st + off + shift
                            if abs(at - t) <= win:
                                found.append((at, pid, pref, head, sl[0], sl[-1], by_sid[sd][1], db))
        for at, pid, pref, head, first, last, stop_name, db in found:
            out["arrivals"].append({"ref": pref, "to": gtfs._name_of(db, last, names), "from": gtfs._name_of(db, first, names),
                                    "head": head, "at": at, "stop": stop_name, "pid": pid})
    out["arrivals"].sort(key=lambda a: (a["at"], a["ref"]))
    out["arrivals"] = out["arrivals"][:CONN_MAX]
    out["lines"] = len(refs)
    return out


# ---- departures (plan 007, stage T1) -------------------------------------------------------------------------------------------
# The trips of the timetables that run round a point in the next minutes: the mod's virtual bus network (busnet.lua) puts a moving
# dot on the map for each and a station board from them. A trip is listed when it calls at a stop within the radius at a time in
# [t - DEP_BACK_S, t + mins]. The road of a pattern comes from /v1/route?id=<id> (GTFS_ROUTE + pid), as for any line. No network.
DEP_RADIUS_M = 3000
DEP_BACK_S = 300             # a bus that called at a stop of the area this long ago is still near it
DEP_MAX_TRIPS = 600
DEP_MAX_PATTERNS = 160
FEATURES.append("departures")


def gtfs_departures(gtfs, lat, lon, t, day, radius=DEP_RADIUS_M, mins=30):
    """{"patterns": [{pid, id (relation id for /v1/route), ref, head, from, to, offs: [s from the start, one per stop]}],
    "trips": [{pid, start}] by start, "stops": n stops in the area, "source": "gtfs", "truncated": bool}. `start` is in seconds
    from midnight of weekday `day` (1 Monday .. 7 Sunday) and may be negative (last night's trips that run on past midnight) or
    pass 86400 (tomorrow's first ones). Empty lists when no timetables cover the point."""
    radius = max(200.0, min(10000.0, float(radius)))
    mins = max(1, min(120, int(mins)))
    lo, hi = t - DEP_BACK_S, t + mins * 60
    out = {"patterns": [], "trips": [], "stops": 0, "source": "gtfs", "truncated": False}
    days = ((0, day), (-86400, (day - 2) % 7 + 1), (86400, day % 7 + 1))      # (shift, weekday of the service)
    found = []                                                          # (pid, start)
    info = {}
    with gtfs._lock:
        for db in gtfs.dbs.values():
            near = gtfs._stops_near(db, lat, lon, radius)
            if not near:
                continue
            out["stops"] += len(near)
            meta = dict(db.execute("SELECT k, v FROM meta").fetchall())
            sids = [r[0] for r in near]
            hits = {}
            for i in range(0, len(sids), 400):
                chunk = sids[i:i + 400]
                q = ("SELECT sp.pid, sp.pos, p.ref, p.head, p.stops, p.offs FROM sp JOIN patterns p USING(pid) "
                     f"WHERE sp.sid IN ({','.join('?' * len(chunk))})")
                for pid, pos, ref, head, stops, offs in db.execute(q, chunk).fetchall():
                    h = hits.setdefault(pid, [ref, head, stops, offs, []])
                    h[4].append(pos)
            names = {}
            for pid, (ref, head, stops, offs, poss) in hits.items():
                ol = [int(x) for x in offs.split(",")]
                here = sorted({ol[p] for p in poss if p < len(ol)})
                if not here:
                    continue
                starts = Gtfs._starts(db, pid, meta)
                got = False
                for shift, dd in days:
                    for st in starts.get(str(dd), []):
                        s0 = st + shift
                        if s0 + here[-1] < lo:
                            continue
                        if s0 + here[0] > hi:
                            break
                        if any(lo <= s0 + o <= hi for o in here):
                            found.append((pid, s0))
                            got = True
                if got:
                    sl = stops.split(",")
                    info[pid] = {"pid": pid, "id": GTFS_ROUTE + pid, "ref": ref, "head": head or "",
                                 "from": gtfs._name_of(db, sl[0], names), "to": gtfs._name_of(db, sl[-1], names), "offs": ol}
    found.sort(key=lambda f: (f[1], f[0]))
    if len(found) > DEP_MAX_TRIPS:
        found, out["truncated"] = found[:DEP_MAX_TRIPS], True
    used = []
    for pid, s0 in found:
        out["trips"].append({"pid": pid, "start": s0})
        if pid not in used:
            used.append(pid)
    if len(used) > DEP_MAX_PATTERNS:
        keep = set(used[:DEP_MAX_PATTERNS])
        out["trips"] = [tr for tr in out["trips"] if tr["pid"] in keep]
        used, out["truncated"] = used[:DEP_MAX_PATTERNS], True
    out["patterns"] = [info[pid] for pid in used]
    return out


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


# ---- the route database: lines and stops prepared in advance (github.com/Robitnik/earth-bus-routes-db-eu) ---------------------

DB_REPOS = [["https://raw.githubusercontent.com/Robitnik/earth-bus-routes-db-eu/main",
             "https://cdn.jsdelivr.net/gh/Robitnik/earth-bus-routes-db-eu@main"]]      # a repo = its mirrors, tried in this order
DB_TIMEOUT_S = 10
DB_MAX_BYTES = 8 * 1024 * 1024
DB_MANIFEST_TTL_S = 86400                 # the database is rebuilt monthly: a day is plenty
DB_MANIFEST_RETRY_S = 600                 # after a failure (offline, repo not there) it is left alone this long
DB_FILE_TTL_S = 14 * 86400
DB_TILES_IN_MEMORY = 400                  # (a tile is ~10 KB of JSON: a 25 km map of tiles fits)
DB_FETCH_THREADS = 16                     # the tiles of a cold place are fetched this many at a time
DB_LINES_M = (12000, 30000)               # a line number is looked for this far round the player (the second only when the first finds none)
DB_STATIONS_M = 7000                      # the stations of a town: the menu shows those within 6 km of its centre
DB_HUB_LINES = 3                          # ... and the stops with at least this many lines (a village has no bus station)
DB_HUBS_MAX = 60
DB_NAME_M = 15000                         # a stop name typed in the search: the tiles this near that are already on this computer
DB_ALONG_CELL_DEG = 0.005                 # the grid that finds the bits of the road near a stop
DB_TWIN_M = 30                            # a stop this near the road, not listed by the line, is on the road (the other side)
DB_TWIN_TILES = 6                         # ... looked for when the line spans no more tiles than this
DB_WAY_ID = 7 * 10 ** 12                  # ids of the made-up ways of an answer made from a database line (only used as keys)
SOURCES = ("auto", "db", "live")


def parse_src(q):
    """The source choice of a request (?src=): 'auto' (the database where it has the place, else the live servers), 'db' (only the
    database: a place it lacks stays empty), 'live' (only the live servers and timetables: the old way)."""
    v = (q.get("src") or ["auto"])[0]
    return v if v in SOURCES else "auto"


DB_ROUTE_MIN = 3 * 10 ** 12               # line ids from here up exist only in the database
FEATURES = FEATURES + ["routedb"]


def db_fetch(url):
    """The text of a file of the database, or None when the server says it is not there (404). Other errors raise OSError."""
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Encoding": "identity"})
    try:
        with urllib.request.urlopen(req, timeout=DB_TIMEOUT_S) as r:
            body = r.read(DB_MAX_BYTES + 1)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise OSError(f"HTTP {e.code} from {url}") from e
    except urllib.error.URLError as e:
        raise OSError(str(e.reason)) from e
    if len(body) > DB_MAX_BYTES:
        raise OSError("file too big")
    return body.decode("utf-8")


class DbRepo:
    """One repository of the database: a folder on this computer (for development and for hand-edited copies) or mirrors of
    one on the net. Files of the net are kept in the cache folder and used while they are fresh; a stale copy is used when the
    net does not answer."""

    def __init__(self, mirrors, cache_dir=None, fetch=db_fetch, clock=time.time):
        self.mirrors, self.fetch, self.clock = list(mirrors), fetch, clock
        self.local = [pathlib.Path(m) for m in self.mirrors if not str(m).startswith(("http://", "https://"))]
        self.urls = [m.rstrip("/") for m in self.mirrors if str(m).startswith(("http://", "https://"))]
        tag = hashlib.sha1("|".join(self.mirrors).encode("utf-8")).hexdigest()[:8]
        self.dir = pathlib.Path(cache_dir) / "db" / tag if cache_dir else None
        self.failed_at = 0.0
        self._manifest = None
        self._lock = threading.Lock()

    def read(self, rel, ttl=DB_FILE_TTL_S, online=True):
        """The text of the file `rel` ('data/CZ/tiles/1400_1944.json'), or None. `online` False: this computer only."""
        for d in self.local:
            f = d / rel
            if f.is_file():
                return f.read_text(encoding="utf-8")
        if self.dir is None:
            return None
        f = self.dir / rel
        stale = None
        try:
            age = self.clock() - f.stat().st_mtime
            text = f.read_text(encoding="utf-8")
            if age < ttl:
                return text
            stale = text
        except OSError:
            pass
        if not online or not self.urls:
            return stale
        for base in self.urls:
            try:
                text = self.fetch(f"{base}/{rel}")
            except OSError as e:
                say(f"db: {rel}: {str(e)[:80]}")
                continue
            if text is None:
                return stale
            try:
                f.parent.mkdir(parents=True, exist_ok=True)
                tmp = f.with_name(f.name + ".part")
                tmp.write_text(text, encoding="utf-8")
                os.replace(tmp, f)
            except OSError:
                pass
            return text
        return stale

    def manifest(self, online=True):
        """The repo's manifest.json as a dict, or None (not there / not reachable)."""
        with self._lock:
            if self._manifest is not None and self.clock() - self._manifest[0] < DB_MANIFEST_TTL_S:
                return self._manifest[1]
            if self._manifest is None and self.failed_at and self.clock() - self.failed_at < DB_MANIFEST_RETRY_S:
                return None
            try:
                text = self.read("manifest.json", ttl=DB_MANIFEST_TTL_S, online=online)
                data = json.loads(text) if text else None
            except (ValueError, OSError):
                data = None
            if not isinstance(data, dict) or not isinstance(data.get("countries"), dict):
                if online:
                    self.failed_at = self.clock()
                return self._manifest[1] if self._manifest else None
            self.failed_at = 0.0
            self._manifest = (self.clock(), data)
            return data


def tile_index(lat, lon, deg):
    return int(math.floor((lat + 90) / deg)), int(math.floor((lon + 180) / deg))


def polyline_decode(text):
    """Google polyline (precision 1e-5) -> [(lat, lon), ...]"""
    pts, i, a, o = [], 0, 0, 0
    while i < len(text):
        vals = []
        for _ in range(2):
            shift = result = 0
            while True:
                b = ord(text[i]) - 63
                i += 1
                result |= (b & 0x1F) << shift
                shift += 5
                if b < 0x20:
                    break
            vals.append(~(result >> 1) if result & 1 else result >> 1)
        a, o = a + vals[0], o + vals[1]
        pts.append((a / 1e5, o / 1e5))
    return pts


class RouteDb:
    """Lines and stops prepared in advance, answered in the shape of the Overpass answers the mod already reads (the same
    shape the timetables' lines have): one small file of a tile of 0.1 degrees for "nearby", one file for a line."""

    def __init__(self, repos=None):
        self.repos = list(repos or [])
        self._mem = {}                       # (repo index, country, tile name) -> tile dict (LRU by insertion order)
        self._where = {}                     # line id -> (repo index, country): learnt from the tiles
        self._sets = {}                      # (repo index, country) -> the names of its tiles
        self.last = None                     # (lat, lon) of the last place a nearby answer was made for
        self._lock = threading.RLock()

    @property
    def enabled(self):
        return bool(self.repos)

    def countries(self, online=True):
        """[(repo index, country, manifest entry)]"""
        out = []
        for i, repo in enumerate(self.repos):
            m = repo.manifest(online)
            if m:
                out += [(i, cc, e) for cc, e in sorted(m["countries"].items())]
        return out

    def _have(self, i, cc, e, online=True):
        """The set of the tiles a country has: the manifest's own list (small databases) or its index file (data/<cc>/index.json,
        fetched once and kept). None when the index cannot be had."""
        have = self._sets.get((i, cc))
        if have is not None:
            return have
        names = e.get("tiles")
        if names is None:
            text = self.repos[i].read(e.get("index") or f"data/{cc}/index.json", ttl=DB_MANIFEST_TTL_S, online=online)
            try:
                names = json.loads(text)["tiles"] if text else None
            except (ValueError, KeyError, TypeError):
                names = None
            if names is None:
                return None
        have = self._sets[(i, cc)] = set(names)
        return have

    def _tiles(self, lat0, lon0, lat1, lon1, online=True):
        """[(repo index, cc, tile name)] of the tiles that exist and touch the box. Only the countries whose bounding box touches
        the box are looked into (one index file each, the first time)."""
        out = []
        for i, cc, e in self.countries(online):
            bb = e.get("bbox")
            if bb and (lat1 < bb[0] - 0.1 or lat0 > bb[2] + 0.1 or lon1 < bb[1] - 0.1 or lon0 > bb[3] + 0.1):
                continue
            have = self._have(i, cc, e, online)
            if not have:
                continue
            deg = e.get("tile_deg", 0.1)
            (ya, xa), (yb, xb) = tile_index(lat0, lon0, deg), tile_index(lat1, lon1, deg)
            for y in range(ya, yb + 1):
                for x in range(xa, xb + 1):
                    if f"{y}_{x}" in have:
                        out.append((i, cc, f"{y}_{x}"))
        return out

    def covers(self, lat, lon, online=True):
        """The database knows this place: a tile at it or next to it exists."""
        return bool(self._tiles(lat - 0.1, lon - 0.1, lat + 0.1, lon + 0.1, online))             # (a tile at it or next to it)

    def tile(self, key, online=True):
        with self._lock:
            t = self._mem.pop(key, None)
            if t is not None:
                self._mem[key] = t
                return t
        i, cc, name = key
        text = self.repos[i].read(f"data/{cc}/tiles/{name}.json", online=online)
        if text is None:
            return None
        t = json.loads(text)
        with self._lock:
            self._mem[key] = t
            while len(self._mem) > DB_TILES_IN_MEMORY:
                self._mem.pop(next(iter(self._mem)))
            for r in t.get("routes", ()):
                self._where[r["id"]] = (i, cc)
        return t

    def load(self, keys, online=True):
        """{key: tile} of the tiles of `keys` that exist; the ones not in memory are read at once in parallel (a cold place: one
        round trip to the net, not one per tile)."""
        out, todo = {}, []
        with self._lock:
            for k in keys:
                t = self._mem.get(k)
                if t is None:
                    todo.append(k)
                else:
                    out[k] = t
        if len(todo) == 1:
            t = self.tile(todo[0], online)
            if t is not None:
                out[todo[0]] = t
        elif todo:
            with concurrent.futures.ThreadPoolExecutor(min(DB_FETCH_THREADS, len(todo))) as ex:
                for k, t in zip(todo, ex.map(lambda k: self.tile(k, online), todo)):
                    if t is not None:
                        out[k] = t
        return out

    @staticmethod
    def box(lat, lon, radius):
        """(lat0, lon0, lat1, lon1) of a square round a point."""
        dlat = radius / 110574 + 0.0005
        dlon = radius / (111320 * max(0.2, math.cos(math.radians(lat)))) + 0.0005
        return lat - dlat, lon - dlon, lat + dlat, lon + dlon

    def node(self, st):
        return {"type": "node", "id": st["id"], "lat": st["lat"], "lon": st["lon"], "tags": self.stop_tags(st)}

    def lines_numbered(self, ref, lat, lon, online=True):
        """The text of the lines with this number round a point (the relations' tags: the search lists them, opening one asks for
        its route), or None when the database does not know the place. Nearer first: a second, wider look only when the first
        finds none."""
        want = fold(str(ref))
        found = {}
        for radius in DB_LINES_M:
            keys = self._tiles(*self.box(lat, lon, radius), online)
            if not keys:
                return None
            for t in self.load(keys, online).values():
                for r in t["routes"]:
                    if r["id"] not in found and fold(str(r["t"].get("ref") or "")) == want:
                        tags = dict(r["t"])
                        tags["type"] = "route"
                        tags.setdefault("route", "bus")
                        found[r["id"]] = {"type": "relation", "id": r["id"], "tags": tags, "members": [], "n": r["n"]}
            if found:
                break
        return json.dumps({"elements": [found[k] for k in sorted(found)], "source": "routedb"}, separators=(",", ":"),
                          ensure_ascii=False)

    def stations(self, lat, lon, radius=DB_STATIONS_M, online=True):
        """The text of the bus stations round a point, and the stops most lines call at (a town without a bus station still
        has a main stop), or None when the database does not know the place."""
        keys = self._tiles(*self.box(lat, lon, radius), online)
        if not keys:
            return None
        tiles = self.load(keys, online).values()
        calls = {}
        for t in tiles:
            for r in t["routes"]:
                for item in r["s"]:
                    calls[item[0]] = calls.get(item[0], 0) + 1
        stations, hubs = [], []
        for t in tiles:
            for st in t["stops"]:
                if not st.get("n") or not _near(lat, lon, st["lat"], st["lon"], radius):
                    continue
                if st.get("k") == "s":
                    stations.append(st)
                elif calls.get(st["id"], 0) >= DB_HUB_LINES:
                    hubs.append(st)
        hubs.sort(key=lambda st: -calls[st["id"]])
        elements = [self.node(st) for st in stations + hubs[:DB_HUBS_MAX]]
        return json.dumps({"elements": elements, "source": "routedb"}, separators=(",", ":"), ensure_ascii=False)

    def along(self, road, radius=ALONG_M, online=True):
        """The text of the stops on a road [(lat, lon), ...] (within `radius` metres of it; a bus station within ALONG_STATION_M),
        or None when the database does not know the places of the road."""
        path = simplify([tuple(p) for p in road], 3)
        if len(path) < 2:
            return None
        g, m = DB_ALONG_CELL_DEG, 0.0015                    # (the margin covers ALONG_STATION_M)
        cells, keys = {}, set()
        for i, ((la, lo), (lb, lob)) in enumerate(zip(path, path[1:])):
            y0, y1 = min(la, lb) - m, max(la, lb) + m
            x0, x1 = min(lo, lob) - m, max(lo, lob) + m
            keys.update(self._tiles(y0, x0, y1, x1, online))
            for y in range(int(math.floor(y0 / g)), int(math.floor(y1 / g)) + 1):
                for x in range(int(math.floor(x0 / g)), int(math.floor(x1 / g)) + 1):
                    cells.setdefault((y, x), []).append(i)
        if not keys:
            return None
        out = []
        for t in self.load(sorted(keys), online).values():
            for st in t["stops"]:
                segs = cells.get((int(math.floor(st["lat"] / g)), int(math.floor(st["lon"] / g))))
                if not segs:
                    continue
                limit = ALONG_STATION_M if st.get("k") == "s" else radius
                if min(dist_to_path(st["lat"], st["lon"], path[i:i + 2]) for i in segs) <= limit:
                    out.append(self.node(st))
        return json.dumps({"elements": out, "source": "routedb"}, separators=(",", ":"), ensure_ascii=False)

    def map_places(self, lat, lon, radius, online=True):
        """[[name, lat, lon, {line numbers}, kind]] of the bus stations and of the stops lines call at round a point, for the
        map; None when the database does not know the place."""
        keys = self._tiles(*self.box(lat, lon, radius), online)
        if not keys:
            return None
        tiles = self.load(keys, online).values()
        refs = {}
        for t in tiles:
            for r in t["routes"]:
                ref = str(r["t"].get("ref") or "")
                if ref:
                    for item in r["s"]:
                        refs.setdefault(item[0], set()).add(ref)
        out = []
        for t in tiles:
            for st in t["stops"]:
                if not st.get("n") or not _near(lat, lon, st["lat"], st["lon"], radius):
                    continue
                kind = "station" if st.get("k") == "s" else "stop"
                r = refs.get(st["id"])
                if kind == "stop" and not r:
                    continue                                # a stop no line of the database calls at
                out.append([st["n"], st["lat"], st["lon"], set(r or ()), kind])
        return out

    def named(self, text, lat, lon, radius=DB_NAME_M, limit=40):
        """Stops whose name has `text` in it, round a point, from the tiles already on this computer (no request: the search
        answers in milliseconds), nearest first."""
        want = fold(text).strip()
        if len(want) < 2:
            return []
        keys = self._tiles(*self.box(lat, lon, radius), online=False)
        hits = {}
        for t in self.load(keys, online=False).values():
            for st in t["stops"]:
                if st.get("n") and want in fold(st["n"]) and _near(lat, lon, st["lat"], st["lon"], radius):
                    hits[st["id"]] = st
        best = sorted(hits.values(), key=lambda st: _dist_m(lat, lon, st["lat"], st["lon"]))[:limit]
        return [self.node(st) for st in best]

    @staticmethod
    def stop_tags(st):
        tags = {"name": st["n"]} if st.get("n") else {}
        k = st.get("k", "p")
        if k == "s":
            tags["amenity"] = "bus_station"
        elif k == "x":
            tags.update({"public_transport": "stop_position", "bus": "yes"})
        else:
            tags.update({"highway": "bus_stop", "public_transport": "platform", "bus": "yes"})
        if st.get("ref"):
            tags["ref"] = st["ref"]
        if st.get("q"):
            tags["request_stop"] = "yes"
        if st.get("g"):
            tags["bus_routes:source"] = "gtfs"
        return tags

    def nearby(self, lat, lon, radius=RADIUS_M, online=True):
        """The text of a "nearby" answer (the stops within `radius` metres and the lines calling at them), or None when the
        database does not know the place or a file is missing."""
        dlat = radius / 110574 + 0.0005
        dlon = radius / (111320 * max(0.2, math.cos(math.radians(lat)))) + 0.0005
        keys = self._tiles(lat - dlat, lon - dlon, lat + dlat, lon + dlon, online)
        if not keys:
            return None
        self.last = (lat, lon)
        nodes, rels = {}, {}
        tiles = self.load(keys, online)
        for key in keys:
            t = tiles.get(key)
            if t is None:
                return None
            for st in t["stops"]:
                if st["id"] not in nodes and hav((lat, lon), (st["lat"], st["lon"])) <= radius:
                    nodes[st["id"]] = {"type": "node", "id": st["id"], "lat": st["lat"], "lon": st["lon"], "tags": self.stop_tags(st)}
            for r in t["routes"]:
                e = rels.setdefault(r["id"], {"t": r["t"], "n": r["n"], "m": {}})
                for item in r["s"]:
                    e["m"][item[0]] = item
        elements = list(nodes.values())
        for rid in sorted(rels):
            e = rels[rid]
            members = []
            for sid, item in e["m"].items():
                if sid in nodes:
                    m = {"type": "node", "ref": sid, "role": "", "i": item[1]}
                    if len(item) > 2:
                        m["j"] = item[2]
                    members.append(m)
            if not members:
                continue
            tags = dict(e["t"])
            tags["type"] = "route"
            tags.setdefault("route", "bus")
            elements.append({"type": "relation", "id": rid, "tags": tags, "members": members, "n": e["n"],
                             "ordered": tags.get("public_transport:version") == "2"})
        return json.dumps({"elements": elements, "source": "routedb"}, separators=(",", ":"), ensure_ascii=False)

    def find(self, rid, online=True):
        """(repo index, cc, record) of a line, or None."""
        rel = f"routes/{rid % 1000:03d}/{rid}.json"
        known = self._where.get(rid)
        if known:
            order = [known]                 # a line seen in a tile is in that country
        else:
            # (a line asked for before any place was: the countries round the last place the database answered for, else all
            # of them when there are only a few)
            allc = self.countries(online)
            last = self.last
            near = [(i, cc) for i, cc, e in allc if not e.get("bbox") or last is None
                    or (e["bbox"][0] - 0.2 <= last[0] <= e["bbox"][2] + 0.2 and e["bbox"][1] - 0.2 <= last[1] <= e["bbox"][3] + 0.2)]
            order = near if (last is not None or len(allc) <= 4) else []
        for i, cc in order:
            text = self.repos[i].read(f"data/{cc}/{rel}", online=online)
            if text is not None:
                return i, cc, json.loads(text)
        return None

    def route(self, rid, road_for=None, online=True):
        """The text of a route answer (as the one of Overpass: the relation with its ways' geometry and stops, then the nodes)
        for a line of the database, or None. `road_for(points)` gives the road of a line that has none of its own (the
        routing servers); without it the stops are joined by straight lines."""
        got = self.find(rid, online)
        if got is None:
            return None
        i, cc, rec = got
        stops = rec["stops"]
        members, elements, road, nid = [], [], [], DB_WAY_ID
        for w in rec.get("ways", ()):
            pts = [{"lat": a, "lon": b} for a, b in polyline_decode(w["g"])]
            nid += 1
            members.append({"type": "way", "ref": nid, "role": w.get("r", ""), "geometry": pts})
            road += [(p["lat"], p["lon"]) for p in pts]
            if w.get("t"):
                elements.append({"type": "way", "id": nid, "tags": w["t"]})
        if not rec.get("ways"):
            pts = [(s["la"], s["lo"]) for s in stops]
            road = road_for(pts) if road_for is not None else pts
            nid += 1
            members.append({"type": "way", "ref": nid, "role": "", "geometry": [{"lat": a, "lon": b} for a, b in road]})
        seen = set()
        for s in stops:
            members.append({"type": "node", "ref": s["s"], "role": s.get("r", ""), "lat": s["la"], "lon": s["lo"]})
            if s["s"] not in seen:
                seen.add(s["s"])
                st = {"n": s.get("n"), "k": "p", "q": s.get("q")}
                elements.append({"type": "node", "id": s["s"], "lat": s["la"], "lon": s["lo"], "tags": self.stop_tags(st)})
        tags = dict(rec["t"])
        tags.update({"type": "route", "route": rec.get("mode", "bus"), "bus_routes:source": "routedb"})
        # where the line comes from (the menu shows it): the kinds of source ("osm+gtfs+edit"), the timetable feeds and their licences
        src = rec.get("src") or []
        parts = [k for k in dict.fromkeys(x.get("k") for x in src) if k]
        if parts:
            tags["bus_routes:parts"] = "+".join(parts)
        for tag, key in (("bus_routes:feeds", "feed"), ("bus_routes:lic", "lic")):
            vals = sorted({str(x[key]) for x in src if x.get("k") == "gtfs" and x.get(key)})
            if vals:
                tags[tag] = ", ".join(vals)
        rel = {"type": "relation", "id": rid, "members": members, "tags": tags}
        times = rec.get("times")
        if times and all("o" in s for s in stops):
            starts = {}
            for key, days in (("wd", "12345"), ("sa", "6"), ("su", "7")):
                for d in days:
                    starts[d] = [m * 60 for m in times.get(key, [])]
            rel["gtfs"] = {"offs": [s["o"] for s in stops], "starts": starts}
        extras = self._twins(road, stops, online)
        return json.dumps({"elements": [rel] + elements + extras}, separators=(",", ":"), ensure_ascii=False)

    def _twins(self, road, stops, online=True):
        """The bus stops within DB_TWIN_M of the road that the line does not list: the platform of the other side of the road
        (the mod picks the one on the right of the way of travel). Only for lines that span few tiles."""
        if len(road) < 2:
            return []
        la, lo = [p[0] for p in road], [p[1] for p in road]
        keys = self._tiles(min(la) - 0.001, min(lo) - 0.001, max(la) + 0.001, max(lo) + 0.001, online)
        if not keys or len(keys) > DB_TWIN_TILES:
            return []
        listed = {s["s"] for s in stops}
        path = simplify(road, 3)
        out = []
        for key in keys:
            t = self.tile(key, online)
            for st in (t or {}).get("stops", ()):
                if st["id"] in listed or st.get("k") == "s" or not st.get("n"):
                    continue
                if not (min(la) - 0.001 <= st["lat"] <= max(la) + 0.001 and min(lo) - 0.001 <= st["lon"] <= max(lo) + 0.001):
                    continue
                if dist_to_path(st["lat"], st["lon"], path) <= DB_TWIN_M:
                    out.append({"type": "node", "id": st["id"], "lat": st["lat"], "lon": st["lon"], "tags": self.stop_tags(st)})
        return out

    def locate(self, lat, lon, name="", radius_m=40.0, online=True):
        """(country code or None, the stop of the database at this place or None): the country of the nearest stop of the tiles at the
        place (a line over a border leaves its stops in the other country's tiles: the nearest one is the country of the place);
        the stop itself when it lies within `radius_m` (one of the same name within half as much again)."""
        cc, best, near = None, None, None
        for key in self._tiles(lat - 0.0002, lon - 0.0002, lat + 0.0002, lon + 0.0002, online):
            t = self.tile(key, online)
            if t is None:
                continue
            for st in t.get("stops", ()):
                dd = _dist_m(lat, lon, st["lat"], st["lon"])
                if near is None or dd < near[0]:
                    near = (dd, key[1])
                same = bool(name) and fold(st.get("n") or "") == fold(name)
                if dd <= radius_m * (1.5 if same else 1.0) and (best is None or dd * (0.6 if same else 1.0) < best[0]):
                    best, cc = (dd * (0.6 if same else 1.0), st), key[1]
        return (cc or (near[1] if near else None)), (best[1] if best else None)

    def status(self):
        out = []
        for repo in self.repos:
            m = repo.manifest(online=False)
            out.append({"repo": repo.mirrors[0] if repo.mirrors else "", "ready": bool(m),
                        "countries": {cc: {k: e.get(k) for k in ("routes", "stops", "built", "sources")}
                                      for cc, e in (m or {}).get("countries", {}).items()}})
        return out


def db_repos_from_env(cache_dir, env=None):
    """BNE_BUSDATA_DB: '0' off; else ';'-separated repos, each a folder or a URL (several mirrors of one repo: ',' between)."""
    env = os.environ if env is None else env
    raw = env.get("BNE_BUSDATA_DB")
    if raw == "0":
        return []
    specs = [[m.strip() for m in part.split(",") if m.strip()] for part in raw.split(";")] if raw else DB_REPOS
    return [DbRepo(m, cache_dir) for m in specs if m]


# ---- the public servers ---------------------------------------------------------------------------------------------

def post_overpass(url, query):
    req = urllib.request.Request(url, data=urllib.parse.urlencode({"data": query}).encode(),
                                 headers={"User-Agent": UA, "Accept": "application/json"})
    timeout = getattr(CURRENT, "attempt_timeout", None) or TIMEOUT_S        # (what is left of the request's budget)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        body = r.read(MAX_BYTES + 1)
    if len(body) > MAX_BYTES:
        raise ValueError("answer too large")
    return body.decode("utf-8")


def fetch_upstream(query, mirrors=None, sender=None, sleep=time.sleep, clock=time.monotonic, rounds=2):
    """The answer's text from the first mirror that gives a good one; raises RuntimeError with every failure when none."""
    global _last_call
    mirrors = mirrors or MIRRORS
    sender = sender or post_overpass
    errors = []
    token = ACTIVITY.begin("overpass", label_of(getattr(CURRENT, "label", "")))
    try:
        return _fetch_upstream(query, mirrors, sender, sleep, clock, rounds, errors, token)
    finally:
        ACTIVITY.end(token)


def _wait_turn(deadline, clock):
    """The one request at a time to the public servers: waits for its turn, but not when nobody waits any more for the
    answer, nor past the budget."""
    while not _lock.acquire(timeout=0.25):
        if not still_wanted():
            raise Abandoned("nobody waits for it any more (it was still in the queue)")
        if clock() >= deadline:
            raise RuntimeError(f"the public servers were busy for {BUDGET_S} s (still in the queue)")


def _fetch_upstream(query, mirrors, sender, sleep, clock, rounds, errors, token):
    global _last_call
    deadline = clock() + BUDGET_S
    _wait_turn(deadline, clock)
    try:
        for n, url in enumerate(mirrors * rounds):
            # each mirror twice at most, within the budget, and only while somebody waits for the answer
            if not still_wanted():
                raise Abandoned("nobody waits for it any more")
            left = deadline - clock()
            if left < 5:
                errors.append(f"the {BUDGET_S} s limit")
                break
            CURRENT.attempt_timeout = min(TIMEOUT_S, left)
            ACTIVITY.update(token, state="running", mirror=n % len(mirrors) + 1, of=len(mirrors))
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
    finally:
        CURRENT.attempt_timeout = None
        _lock.release()
    raise RuntimeError("; ".join(errors[-4:]) or "no mirror")


def get_url(url):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=OSRM_TIMEOUT_S) as r:
        return r.read(MAX_BYTES + 1).decode("utf-8")


def fetch_osrm(pts, bases=None, getter=None, sleep=time.sleep):
    """The text of the path answer for `pts` from the first routing server that has a route; RuntimeError when none."""
    token = ACTIVITY.begin("osrm", "road")
    try:
        return _fetch_osrm(pts, bases, getter, sleep, token)
    finally:
        ACTIVITY.end(token)


ROUTERS_DOWN_S = 120                 # after none of the routing servers could be reached: no new try for this long (straight lines meanwhile)
_routers = {"down_until": 0.0}


def _fetch_osrm(pts, bases, getter, sleep, token):
    live = getter is None                # (the real network: a test with its own getter is left alone)
    getter = getter or get_url
    if live and time.monotonic() < _routers["down_until"]:
        raise RuntimeError("the routing servers could not be reached a moment ago")
    errors = []
    unreachable = 0
    start = time.monotonic()
    for n, base in enumerate((bases or OSRM) * 2):
        if live and n >= len(bases or OSRM) and unreachable >= len(bases or OSRM):
            break                        # every server was tried and none could be connected to: a second round only waits longer
        if n and not still_wanted():
            raise Abandoned("nobody waits for it any more")
        if time.monotonic() - start > BUDGET_S:
            errors.append(f"the {BUDGET_S} s limit")
            break
        ACTIVITY.update(token, state="running", mirror=n % len(bases or OSRM) + 1, of=len(bases or OSRM))
        host = urllib.parse.urlsplit(base).hostname
        try:
            return json.dumps(parse_osrm(json.loads(getter(osrm_url(base, pts)))), separators=(",", ":"))
        except urllib.error.HTTPError as e:
            errors.append(f"{host}: HTTP {e.code}")
            if e.code == 400:                  # OSRM: no road near a point; another server will not know better
                break
        except (urllib.error.URLError, OSError, ValueError, TimeoutError) as e:
            errors.append(f"{host}: {type(e).__name__} {str(e)[:60]}")
            if isinstance(e, ValueError) and "no route" in str(e):
                break
            if not isinstance(e, ValueError):
                unreachable += 1
        sleep(BACKOFF_S[min(n, len(BACKOFF_S) - 1)] / 2)
    if live and unreachable >= len(bases or OSRM):
        _routers["down_until"] = time.monotonic() + ROUTERS_DOWN_S
        say(f"no routing server could be reached: straight lines for {ROUTERS_DOWN_S} s")
    raise RuntimeError("; ".join(errors[-3:]) or "no routing server")


EXPORT_MAX_POINTS = 80
EXPORT_ROUTE_BASE = 3 * 10 ** 12          # the id bands of the route database (builder/ebrdb/ids.py)
EXPORT_STOP_BASE = 6 * 10 ** 12


def stable_hash(text):
    return int(hashlib.sha1(text.encode("utf-8")).hexdigest()[:12], 16) % 10 ** 11


def polyline_encode(points):
    """[(lat, lon)] -> Google polyline, precision 1e-5."""
    out, pa, po = [], 0, 0
    for lat, lon in points:
        a, o = round(lat * 1e5), round(lon * 1e5)
        for v in (a - pa, o - po):
            v = ~(v << 1) if v < 0 else v << 1
            while v >= 0x20:
                out.append(chr((0x20 | (v & 0x1F)) + 63))
                v >>= 5
            out.append(chr(v + 63))
        pa, po = a, o
    return "".join(out)


# ---- the stop announcer (informator): offline voices ---------------------------------------------------------------------
# The mod asks for one sentence at a time ("Next stop: X") in the language of the country the bus drives in; Piper (MIT, the
# 2023.11.14-2 engine) reads it on this computer with a voice of rhasspy/piper-voices (each voice has its own licence, see its
# MODEL_CARD). The engine (22 MB) and one voice per language (60-110 MB) are downloaded once, when a trip first wants them, and
# only while the mod keeps asking: a trip that ends stops the download. Nothing runs between trips (an idle engine is closed).

PIPER_REL = "https://github.com/rhasspy/piper/releases/download/2023.11.14-2/"
PIPER_ASSETS = {("win32", "amd64"): "piper_windows_amd64.zip", ("linux", "x86_64"): "piper_linux_x86_64.tar.gz",
                ("linux", "aarch64"): "piper_linux_aarch64.tar.gz", ("darwin", "arm64"): "piper_macos_aarch64.tar.gz",
                ("darwin", "x86_64"): "piper_macos_x64.tar.gz"}
PIPER_MAX_BYTES = 40 * 1048576
VOICE_MAX_BYTES = 160 * 1048576
VOICE_URL = "https://huggingface.co/rhasspy/piper-voices/resolve/{rev}/{path}"
VOICE_OLD = "v1.0.0"                                       # the voices as the 2023 engine reads them
VOICE_NEW = "4a409e3cbfd0a189930b38f127a38e107677e8ac"     # 2026-11-15: voices that exist only in the newer form (pinned: the
                                                           # voices are retrained in place, a moving "main" would change them)
# the language of the announcements -> (voice, revision, speaker or None). A language without a voice of its own the 2023 engine
# can read takes the nearest one (lt: Latvian, hr: Slovenian); bg and et have only new voices (their diphthong symbols are dropped).
VOICES = {
    "uk": ("uk_UA-ukrainian_tts-medium", VOICE_OLD, 2),     # speakers: lada 0, mykyta 1, tetiana 2
    "cs": ("cs_CZ-jirka-medium", VOICE_OLD, None),
    "sk": ("sk_SK-lili-medium", VOICE_OLD, None),
    "pl": ("pl_PL-gosia-medium", VOICE_OLD, None),
    "de": ("de_DE-thorsten-medium", VOICE_OLD, None),
    "de_AT": ("de_DE-thorsten-medium", VOICE_OLD, None),
    "hu": ("hu_HU-anna-medium", VOICE_OLD, None),
    "ro": ("ro_RO-mihai-medium", VOICE_OLD, None),
    "fr": ("fr_FR-siwis-medium", VOICE_OLD, None),
    "nl": ("nl_NL-pim-medium", VOICE_OLD, None),
    "nl_BE": ("nl_BE-nathalie-medium", VOICE_OLD, None),
    "it": ("it_IT-paola-medium", VOICE_OLD, None),
    "es": ("es_ES-davefx-medium", VOICE_OLD, None),
    "pt": ("pt_PT-tugão-medium", VOICE_OLD, None),
    "sv": ("sv_SE-lisa-medium", VOICE_OLD, None),
    "da": ("da_DK-talesyntese-medium", VOICE_OLD, None),
    "no": ("no_NO-talesyntese-medium", VOICE_OLD, None),
    "fi": ("fi_FI-harri-medium", VOICE_OLD, None),
    "et": ("et_EE-news-medium", VOICE_NEW, 0),
    "lv": ("lv_LV-aivars-medium", VOICE_OLD, None),
    "lt": ("lv_LV-aivars-medium", VOICE_OLD, None),
    "sl": ("sl_SI-artur-medium", VOICE_OLD, None),
    "hr": ("sl_SI-artur-medium", VOICE_OLD, None),
    "bg": ("bg_BG-dimitar-medium", VOICE_NEW, None),
    "el": ("el_GR-joy-medium", VOICE_NEW, None),
    "en_GB": ("en_GB-alba-medium", VOICE_OLD, None),
    "en_US": ("en_US-lessac-medium", VOICE_OLD, None),
}
COUNTRY_LANG = {
    "UA": "uk", "CZ": "cs", "SK": "sk", "PL": "pl", "DE": "de", "AT": "de_AT", "CH": "de", "LI": "de", "HU": "hu", "RO": "ro",
    "MD": "ro", "FR": "fr", "MC": "fr", "LU": "fr", "NL": "nl", "IT": "it", "SM": "it", "VA": "it", "ES": "es", "AD": "es",
    "PT": "pt", "SE": "sv", "DK": "da", "NO": "no", "FI": "fi", "EE": "et", "LV": "lv", "LT": "lt", "SI": "sl", "HR": "hr",
    "BG": "bg", "GR": "el", "CY": "el", "IE": "en_GB", "MT": "en_GB", "GB": "en_GB", "US": "en_US",
}
# What the bus says, the way the country's own buses say it (docs/research/stop-announcements.md): "at" when it nears a stop,
# "end" when it nears the terminus, "next" once the doors close, "nextEnd" when that next stop is the terminus; "...Req" for a
# request stop where the country says so. {s} is the stop's name.
PHRASES = {
    "uk": {"at": "Зупинка {s}.", "atReq": "Зупинка {s}, на вимогу.", "end": "Кінцева зупинка {s}. Прохання звільнити салон.",
           "next": "Наступна зупинка: {s}.", "nextReq": "Наступна зупинка: {s}, на вимогу.", "nextEnd": "Наступна зупинка: {s}, кінцева."},
    "cs": {"at": "{s}.", "atReq": "{s}, na znamení.", "end": "{s}. Konečná zastávka, prosíme, vystupte.",
           "next": "Příští zastávka: {s}.", "nextReq": "Příští zastávka: {s}, na znamení.", "nextEnd": "Příští zastávka: {s}, konečná."},
    "sk": {"at": "{s}.", "atReq": "{s}, na znamenie.", "end": "{s}. Konečná zastávka, prosíme, vystúpte.",
           "next": "Nasledujúca zastávka: {s}.", "nextReq": "Nasledujúca zastávka: {s}, na znamenie.",
           "nextEnd": "Nasledujúca zastávka: {s}, konečná."},
    "pl": {"at": "Przystanek {s}.", "atReq": "Przystanek na żądanie {s}.", "end": "Przystanek końcowy {s}. Prosimy o opuszczenie pojazdu.",
           "next": "Następny przystanek: {s}.", "nextReq": "Następny przystanek: {s}, na żądanie.",
           "nextEnd": "Następny przystanek: {s}. Przystanek końcowy."},
    "de": {"at": "{s}.", "end": "{s}. Endhaltestelle. Bitte alle aussteigen.", "next": "Nächster Halt: {s}.",
           "nextEnd": "Nächster Halt: {s}. Endhaltestelle."},
    "de_AT": {"at": "{s}.", "end": "{s}. Endstation. Bitte alle aussteigen.", "next": "Nächste Haltestelle: {s}.",
              "nextEnd": "Nächste Haltestelle: {s}. Endstation."},
    "hu": {"at": "{s}.", "atReq": "{s}, feltételes megálló.", "end": "{s}, végállomás. Kérjük, szálljanak le!",
           "next": "Következik: {s}.", "nextReq": "Következik: {s}, feltételes megálló.", "nextEnd": "Következik: {s}, végállomás."},
    "ro": {"at": "Stația {s}.", "atReq": "Stația {s}, stație facultativă.", "end": "Stația {s}. Capăt de linie. Vă rugăm să coborâți.",
           "next": "Următoarea stație: {s}.", "nextReq": "Următoarea stație: {s}, stație facultativă.",
           "nextEnd": "Următoarea stație: {s}, capăt de linie."},
    "fr": {"at": "{s}.", "end": "{s}. Terminus. Tout le monde descend.", "next": "Prochain arrêt : {s}.",
           "nextEnd": "Prochain arrêt : {s}. Terminus."},
    "nl": {"at": "{s}.", "end": "{s}. Eindhalte. Iedereen uitstappen, alstublieft.", "next": "Volgende halte: {s}.",
           "nextEnd": "Volgende halte: {s}. Eindhalte."},
    "nl_BE": {"at": "{s}.", "end": "{s}. Eindhalte. Iedereen uitstappen, alstublieft.", "next": "Volgende halte: {s}.",
              "nextEnd": "Volgende halte: {s}. Eindhalte."},
    "it": {"at": "{s}.", "atReq": "{s}, fermata a richiesta.", "end": "{s}. Capolinea.", "next": "Prossima fermata: {s}.",
           "nextReq": "Prossima fermata: {s}, fermata a richiesta.", "nextEnd": "Prossima fermata: {s}. Capolinea."},
    "es": {"at": "{s}.", "end": "{s}. Final de trayecto.", "next": "Próxima parada: {s}.", "nextEnd": "Próxima parada: {s}. Final de trayecto."},
    "pt": {"at": "{s}.", "end": "{s}. Fim de linha.", "next": "Próxima paragem: {s}.", "nextEnd": "Próxima paragem: {s}. Fim de linha."},
    "sv": {"at": "{s}.", "end": "{s}. Slutstation.", "next": "Nästa hållplats: {s}.", "nextEnd": "Nästa hållplats: {s}. Slutstation."},
    "da": {"at": "{s}.", "end": "{s}. Endestation.", "next": "Næste stop: {s}.", "nextEnd": "Næste stop: {s}. Endestation."},
    "no": {"at": "{s}.", "end": "{s}. Endeholdeplass.", "next": "Neste holdeplass: {s}.", "nextEnd": "Neste holdeplass: {s}. Endeholdeplass."},
    "fi": {"at": "{s}.", "end": "{s}. Päätepysäkki.", "next": "Seuraava pysäkki: {s}.", "nextEnd": "Seuraava pysäkki: {s}. Päätepysäkki."},
    "et": {"at": "{s}.", "end": "{s}. Lõpp-peatus.", "next": "Järgmine peatus: {s}.", "nextEnd": "Järgmine peatus: {s}. Lõpp-peatus."},
    "lv": {"at": "{s}.", "end": "{s}. Galapunkts.", "next": "Nākamā pietura: {s}.", "nextEnd": "Nākamā pietura: {s}. Galapunkts."},
    "lt": {"at": "{s}.", "end": "{s}. Galinė stotelė.", "next": "Kita stotelė: {s}.", "nextEnd": "Kita stotelė: {s}. Galinė stotelė."},
    "sl": {"at": "{s}.", "end": "{s}. Končna postaja.", "next": "Naslednja postaja: {s}.", "nextEnd": "Naslednja postaja: {s}. Končna postaja."},
    "hr": {"at": "{s}.", "end": "{s}. Posljednje stajalište.", "next": "Sljedeće stajalište: {s}.",
           "nextEnd": "Sljedeće stajalište: {s}. Posljednje stajalište."},
    "bg": {"at": "Спирка {s}.", "end": "{s}. Последна спирка.", "next": "Следваща спирка: {s}.", "nextEnd": "Следваща спирка: {s}. Последна спирка."},
    "el": {"at": "{s}.", "end": "{s}. Τέλος διαδρομής.", "next": "Επόμενη στάση: {s}.", "nextEnd": "Επόμενη στάση: {s}. Τέλος διαδρομής."},
    "en_GB": {"at": "{s}.", "end": "{s}. This is the last stop. All change, please.", "next": "Next stop: {s}.",
              "nextEnd": "Next stop: {s}. This bus terminates there."},
    "en_US": {"at": "{s}.", "end": "{s}. This is the last stop.", "next": "Next stop: {s}.", "nextEnd": "Next stop: {s}, the last stop."},
}
SAY_KINDS = ("at", "end", "next", "nextEnd")
SAY_MAX_CHARS = 300
# the short forms of stop names, read out in full (a voice reads "nám." as "nam"): [(pattern, replacement)] per language
_UP = "A-ZÁÄČĎÉĚÍĹĽŇÓÔŔŘŠŤÚŮÝŽ"
EXPAND = {
    "uk": [(r"\bвул\.\s*", "вулиця "), (r"\bпл\.\s*", "площа "), (r"\b(?:просп|пр-т|пр)\.\s*", "проспект "),
           (r"\b(?:бульв|б-р)\.\s*", "бульвар "), (r"\bпров\.\s*", "провулок "), (r"\bм-н\b\.?\s*", "мікрорайон "),
           (r"\bАС\b", "автостанція"), (r"\bзал\.\s*вокз\.?", "залізничний вокзал"), (r"\bс\.\s+", "село "), (r"\bсмт\.?\s+", "селище ")],
    "cs": [(r"\bnám\.\s*", "náměstí "), (r"\baut\.\s*st\.?|\bAS\b", "autobusové stanoviště"), (r"\bžel\.\s*st\.?", "železniční stanice"),
           (r"\bžel\.\s*zast\.?", "železniční zastávka"), (r"\bhl\.\s*n\.?", "hlavní nádraží"), (r"\brozc\.\s*", "rozcestí "),
           (r"\bsídl\.\s*", "sídliště "), (r"\bnem\.\s*", "nemocnice "), (r"\bkřiž\.\s*", "křižovatka "), (r"\bZŠ\b", "základní škola"),
           (r"\bMŠ\b", "mateřská škola"), (r"\b(?:OÚ|ObÚ)\b", "obecní úřad"), (r"\bMěÚ\b", "městský úřad"), (r"\bhost\.\s*", "hostinec "),
           (rf"\bn\.\s*(?=[{_UP}])", "nad "), (rf"\bp\.\s*(?=[{_UP}])", "pod "), (r"\bMet\.", "Metují"), (r"\bOrl\.", "Orlicí"),
           (r"\bLab\.", "Labem")],
    "sk": [(r"\bnám\.\s*", "námestie "), (r"\baut\.\s*st\.?|\bAS\b", "autobusová stanica"), (r"\bžel\.\s*st\.?", "železničná stanica"),
           (r"\brázc\.\s*", "rázcestie "), (r"\bsídl\.\s*", "sídlisko "), (r"\bZŠ\b", "základná škola"), (r"\bOÚ\b", "obecný úrad"),
           (rf"\bn\.\s*(?=[{_UP}])", "nad "), (rf"\bp\.\s*(?=[{_UP}])", "pod ")],
    "pl": [(r"\bul\.\s*", ""), (r"\bpl\.\s*", "plac "), (r"\bal\.\s*", "aleja "), (r"\bos\.\s*", "osiedle "), (r"\b[Dd]w\.\s*", "Dworzec "),
           (r"\s*\bn/ż\b", "")],
    "de": [(r"(\w)str\.", r"\1straße"), (r"\bStr\.", "Straße"), (r"\bPl\.", "Platz"), (r"\bHbf\b\.?", "Hauptbahnhof"),
           (r"\bBf\b\.?", "Bahnhof"), (r"\bS\+U\b", "S- und U-Bahnhof"), (r"\bAbzw\.\s*", "Abzweig "), (r"\bRi\.\s*", "Richtung ")],
    "de_AT": [(r"(\w)str\.", r"\1straße"), (r"\bStr\.", "Straße"), (r"\bPl\.", "Platz"), (r"\bHbf\b\.?", "Hauptbahnhof"), (r"\bBf\b\.?", "Bahnhof")],
    "hu": [(r"\bu\.", "utca"), (r"\bkrt\.", "körút"), (r"\bvá\.", "vasútállomás"), (r"\bpu\.", "pályaudvar"), (r"\baut\.\s*áll\.", "autóbusz-állomás")],
    "ro": [(r"\bStr\.\s*", "Strada "), (r"\b(?:Bd|B-dul)\.?\s*", "Bulevardul "), (r"\bP-ța\s*|\bPța\.\s*", "Piața "), (r"\bCal\.\s*", "Calea ")],
    "fr": [(r"\bPl\.\s*", "Place "), (r"\bAv\.\s*", "Avenue "), (r"\bBd\b\.?\s*", "Boulevard "), (r"\bSt[e]?-", lambda m: "Sainte-" if m.group(0) == "Ste-" else "Saint-")],
    "it": [(r"\bP\.?\s?zz?a\b\.?\s*", "Piazza "), (r"\bV\.le\s*", "Viale "), (r"\bC\.so\s*", "Corso "), (r"\bV\.\s*", "Via "), (r"\bStaz\.\s*", "Stazione ")],
    "es": [(r"\bAv(?:da)?\.\s*", "Avenida "), (r"\bC/\s*", "Calle "), (r"\bPza?\.\s*", "Plaza "), (r"\bEst\.\s*", "Estación ")],
    "pt": [(r"\bAv\.\s*", "Avenida "), (r"\bR\.\s*", "Rua "), (r"\bPç\.\s*", "Praça "), (r"\bEst\.\s*", "Estação ")],
}


def speakable(name, lang):
    """A stop's name as a voice should read it: short forms in full, no quotes or brackets, separators as pauses."""
    s = str(name or "").strip()
    for pat, rep in EXPAND.get(lang, ()):
        s = re.sub(pat, rep, s)
    s = re.sub(r"[\"«»„“”]", "", s)
    s = re.sub(r"\s*[()\[\]]\s*", ", ", s)
    s = re.sub(r"\s*(?:/|;|\s[-–—]\s|\|)\s*", ", ", s)
    s = re.sub(r"\s*,\s*", ", ", s)
    s = re.sub(r"(?:,\s*)+", ", ", s)
    s = re.sub(r"\s{2,}", " ", s).strip(" ,.")
    return s


def announce_lang(cc, lat=None, lon=None, fallback=None):
    """The language of the announcements in a country (Belgium: Dutch in Flanders, French in Wallonia and Brussels); else the
    game's language when there is a voice for it; else None."""
    cc = (cc or "").upper()
    if cc == "BE":
        if lat is None or lon is None:
            return "fr"
        brussels = 50.77 <= lat <= 50.92 and 4.24 <= lon <= 4.49
        return "nl_BE" if lat >= 50.76 and not brussels else "fr"
    if cc in COUNTRY_LANG:
        return COUNTRY_LANG[cc]
    f = (fallback or "").replace("-", "_")
    if f in PHRASES:
        return f
    f = {"en": "en_US", "pt_BR": "pt", "pt_PT": "pt"}.get(f, f[:2])
    return f if f in PHRASES else None


def announcement(lang, kind, name, request=False):
    """The sentence the bus says (kind: one of SAY_KINDS) in the language `lang` (a key of PHRASES)."""
    p = PHRASES[lang]
    key = kind + "Req" if request and kind + "Req" in p else kind
    return p[key].format(s=speakable(name, lang))


def chime(rate, seconds=1.0):
    """The two-tone gong the announcements begin with (16-bit mono PCM at `rate`)."""
    n = int(rate * seconds)
    out = array.array("h", bytes(2 * n))
    for f, start in ((659.25, 0.0), (523.25, 0.38)):
        s0 = int(start * rate)
        for i in range(n - s0):
            t = i / rate
            env = min(1.0, t / 0.006) * math.exp(-4.2 * t)
            v = math.sin(2 * math.pi * f * t) + 0.35 * math.sin(4 * math.pi * f * t) + 0.12 * math.sin(6 * math.pi * f * t)
            out[s0 + i] = max(-32767, min(32767, out[s0 + i] + int(9000 * env * v)))
    return out.tobytes()


def wav_bytes(rate, pcm):
    buf = io.BytesIO()
    with wave.open(buf, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(pcm)
    return buf.getvalue()


def with_chime(speech_wav, gong=True):
    """The finished clip: the gong, a breath, the speech, a short tail. Returns (wav bytes, seconds)."""
    with wave.open(io.BytesIO(speech_wav), "rb") as w:
        rate, width, ch = w.getframerate(), w.getsampwidth(), w.getnchannels()
        pcm = w.readframes(w.getnframes())
    if width != 2 or ch != 1:
        raise ValueError("the voice gave no 16-bit mono sound")
    head = (chime(rate) + bytes(2 * int(rate * 0.1))) if gong else b""
    body = head + pcm + bytes(2 * int(rate * 0.25))
    return wav_bytes(rate, body), round(len(body) / 2 / rate, 2)


def voice_path(key):
    """"uk_UA-ukrainian_tts-medium" -> "uk/uk_UA/ukrainian_tts/medium/uk_UA-ukrainian_tts-medium" (the folder of rhasspy/piper-voices)."""
    code, rest = key.split("-", 1)
    name, quality = rest.rsplit("-", 1)
    return f"{code.split('_')[0]}/{code}/{name}/{quality}/{key}"


def fit_config(cfg):
    """A voice config the 2023 engine reads: the newer voices name symbols of two letters (diphthongs) it cannot load."""
    ids = cfg.get("phoneme_id_map") or {}
    multi = [k for k in ids if len(k) != 1]
    if multi or "vowel_clusters" in cfg:
        cfg = dict(cfg, phoneme_id_map={k: v for k, v in ids.items() if len(k) == 1})
        cfg.pop("vowel_clusters", None)
    return cfg


class VoiceNotReady(RuntimeError):
    pass


class PiperProc:
    """One running engine with one voice loaded: a sentence in (a JSON line), the path of its WAV out."""

    def __init__(self, exe, model, clock=time.monotonic):
        flags = 0x08000000 if sys.platform == "win32" else 0        # CREATE_NO_WINDOW: no console pops up over the game
        self.p = subprocess.Popen([str(exe), "--model", str(model), "--json-input"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, cwd=str(pathlib.Path(exe).parent), creationflags=flags,
                                  text=True, encoding="utf-8")
        self.lock = threading.Lock()
        self.clock = clock
        self.used = clock()

    def speak(self, text, out, speaker=None, timeout=30):
        with self.lock:
            self.used = self.clock()
            msg = {"text": text, "output_file": str(out)}
            if speaker is not None:
                msg["speaker_id"] = speaker
            killer = threading.Timer(timeout, self.close)
            killer.start()
            try:
                self.p.stdin.write(json.dumps(msg, ensure_ascii=False) + "\n")
                self.p.stdin.flush()
                line = self.p.stdout.readline().strip()
            finally:
                killer.cancel()
            self.used = self.clock()
            if not line:
                raise RuntimeError("the voice engine stopped")
            return pathlib.Path(line)

    def alive(self):
        return self.p.poll() is None

    def close(self):
        try:
            self.p.kill()
        except OSError:
            pass


class Announcer:
    """The voices of this computer (folder voice/: engine/, models/, clips/). prepare(lang) gets what a language needs (in a thread
    of its own, while the mod keeps asking: a lease of LEASE_S); speak(lang, text) gives the finished clip."""
    LEASE_S = 90
    IDLE_S = 120
    CLIPS_MAX_BYTES = 200 * 1048576

    def __init__(self, directory=None, fetch=download_file, clock=time.monotonic, engine=None):
        self.dir = pathlib.Path(directory) if directory else None
        self.fetch, self.clock = fetch, clock
        self.engine = engine          # tests: engine(model_path, text, speaker) -> WAV bytes, instead of the Piper program
        self._lock = threading.Lock()
        self._jobs = {}               # voice -> {"state": "downloading" | "failed", "got", "total", "error"}
        self._until = {}              # voice -> clock: somebody still wants it
        self._procs = {}
        self._reaper = None
        self._writes = 0

    # where things are
    def _asset(self):
        return PIPER_ASSETS.get((sys.platform, platform.machine().lower()))

    def _exe(self):
        return self.dir / "engine" / "piper" / ("piper.exe" if sys.platform == "win32" else "piper")

    def _model(self, key):
        return self.dir / "models" / (key + ".onnx")

    def _ready(self, key):
        if self.dir is None:
            return False
        m = self._model(key)
        return m.exists() and m.with_suffix(".onnx.json").exists() and (self.engine is not None or self._exe().exists())

    def status(self, lang):
        if not lang or lang not in VOICES:
            return {"lang": lang, "state": "none"}
        key, _, _ = VOICES[lang]
        out = {"lang": lang, "voice": key}
        if self.dir is None or (self.engine is None and not self._asset()):
            return dict(out, state="unsupported")
        if self._ready(key):
            return dict(out, state="ready")
        with self._lock:
            job = dict(self._jobs.get(key) or {"state": "missing"})
        return dict(out, **job)

    def prepare(self, lang):
        """The status of a language's voice; a missing one starts downloading (a failed one is tried again after a minute)."""
        st = self.status(lang)
        if st["state"] in ("none", "unsupported", "ready"):
            return st
        key = st["voice"]
        with self._lock:
            self._until[key] = self.clock() + self.LEASE_S
            job = self._jobs.get(key)
            busy = job and (job["state"] == "downloading" or (job["state"] == "failed" and self.clock() - job["at"] < 60))
            if not busy:
                self._jobs[key] = {"state": "downloading", "got": 0, "total": 0, "at": self.clock()}
        if not busy:
            threading.Thread(target=self._download, args=(lang,), daemon=True).start()
        return self.status(lang)

    def _download(self, lang):
        key, rev, _ = VOICES[lang]

        def progress(done, total, base=0):
            with self._lock:
                job = self._jobs.get(key)
                if job:
                    job["got"], job["total"] = base + done, max(job["total"], base + total)
                if self.clock() > self._until.get(key, 0):
                    raise Abandoned("nobody waits for the voice")

        try:
            (self.dir / "models").mkdir(parents=True, exist_ok=True)
            base = 0
            if self.engine is None and not self._exe().exists():
                asset = self._asset()
                arc = self.dir / asset
                say(f"voice: downloading the engine {asset}")
                self.fetch(PIPER_REL + asset, arc, PIPER_MAX_BYTES, progress)
                base = arc.stat().st_size
                tmp = self.dir / "engine.tmp"
                shutil.rmtree(tmp, ignore_errors=True)
                if asset.endswith(".zip"):
                    with zipfile.ZipFile(arc) as z:
                        z.extractall(tmp)
                else:
                    with tarfile.open(arc) as t:
                        t.extractall(tmp, filter="data")
                shutil.rmtree(self.dir / "engine", ignore_errors=True)
                os.replace(tmp, self.dir / "engine")
                arc.unlink()
                if sys.platform != "win32":
                    self._exe().chmod(0o755)
            path = urllib.parse.quote(voice_path(key))
            cfg_dest = self._model(key).with_suffix(".onnx.json")
            say(f"voice: downloading {key}")
            self.fetch(VOICE_URL.format(rev=rev, path=path + ".onnx.json"), cfg_dest, 1048576)
            cfg = fit_config(json.loads(cfg_dest.read_text(encoding="utf-8")))
            cfg_dest.write_text(json.dumps(cfg, ensure_ascii=False), encoding="utf-8")
            model = self._model(key)
            part = model.with_suffix(".dl")
            self.fetch(VOICE_URL.format(rev=rev, path=path + ".onnx"), part, VOICE_MAX_BYTES,
                       lambda d, t: progress(d, t, base))
            os.replace(part, model)
            with self._lock:
                self._jobs.pop(key, None)
            say(f"voice: {key} ready")
        except Exception as e:  # noqa: BLE001 - whatever failed, the trip goes on without a voice
            for p in (self.dir / "models").glob(key + ".*"):
                if p.suffix in (".dl", ".part") or not self._model(key).exists():
                    p.unlink(missing_ok=True)
            for p in self.dir.glob("piper_*"):                       # a half-downloaded engine
                p.unlink(missing_ok=True)
            shutil.rmtree(self.dir / "engine.tmp", ignore_errors=True)
            with self._lock:
                self._jobs[key] = {"state": "failed", "error": str(e)[:120], "at": self.clock()}
            say(f"voice: {key} failed: {e!r}")

    def speak(self, lang, text, gong=True):
        """(wav bytes, seconds, clip id) of a sentence; VoiceNotReady when the language's voice is not on this computer."""
        st = self.status(lang)
        if st["state"] != "ready":
            raise VoiceNotReady(st["state"])
        key, _, speaker = VOICES[lang]
        text = str(text)[:SAY_MAX_CHARS]
        cid = hashlib.sha1(f"{key}|{speaker}|{int(gong)}|{text}".encode("utf-8")).hexdigest()[:16]
        clips = self.dir / "clips"
        clip = clips / (cid + ".wav")
        if clip.exists():
            data = clip.read_bytes()
            with wave.open(io.BytesIO(data), "rb") as w:
                return data, round(w.getnframes() / w.getframerate(), 2), cid
        clips.mkdir(parents=True, exist_ok=True)
        if self.engine is not None:
            speech = self.engine(self._model(key), text, speaker)
        else:
            raw = clips / (cid + ".raw.wav")
            self._proc(key).speak(text, raw.resolve(), speaker)
            speech = raw.read_bytes()
            raw.unlink(missing_ok=True)
        data, secs = with_chime(speech, gong)
        clip.write_bytes(data)
        self._writes += 1
        if self._writes % 50 == 1:
            self._trim(clips)
        return data, secs, cid

    def clip_path(self, cid):
        return (self.dir / "clips" / (cid + ".wav")).resolve()

    def _proc(self, key):
        with self._lock:
            p = self._procs.get(key)
            if p is None or not p.alive():
                p = PiperProc(self._exe(), self._model(key), self.clock)
                self._procs[key] = p
            if self._reaper is None:
                self._reaper = threading.Thread(target=self._reap, daemon=True)
                self._reaper.start()
            return p

    def _reap(self):
        """Closes an engine nobody spoke through for IDLE_S; ends when none is left."""
        while True:
            time.sleep(5)
            with self._lock:
                for k, p in list(self._procs.items()):
                    if not p.alive() or self.clock() - p.used > self.IDLE_S:
                        p.close()
                        del self._procs[k]
                if not self._procs:
                    self._reaper = None
                    return

    def close(self):
        with self._lock:
            for p in self._procs.values():
                p.close()
            self._procs.clear()

    def _trim(self, clips):
        files = sorted(clips.glob("*.wav"), key=lambda p: p.stat().st_mtime)
        total = sum(p.stat().st_size for p in files)
        while files and total > self.CLIPS_MAX_BYTES:
            p = files.pop(0)
            total -= p.stat().st_size
            p.unlink(missing_ok=True)


class Service:
    def __init__(self, cache, upstream=fetch_upstream, ttl=TTL_S, router=fetch_osrm, geocoder=geo_search, places=None, gtfs=None,
                 db=None, live=False, voice=None):
        self.cache, self.upstream, self.ttl, self.router, self.geocoder = cache, upstream, ttl, router, geocoder
        self.voice = voice or Announcer(None)       # the stop announcer's voices (none without a folder)
        self.db = db or RouteDb([])
        self.live = live                     # True: ignore the route database (fresh data from the map servers and timetables)
        self.places = places or Gazetteer(None)
        self.gtfs = gtfs or Gtfs(None)
        self.places.after = self.want_timetables
        # the stops along a road are a big query: one round of mirrors, so the answer comes (or fails) before the mod stops waiting
        self.upstream_once = (lambda q: fetch_upstream(q, rounds=1)) if upstream is fetch_upstream else upstream
        self.started = time.time()
        self.served = {"cached": 0, "fetched": 0, "stale": 0, "failed": 0, "dropped": 0}
        self.index = StopIndex()
        self.indexed = 0

    def geocode(self, q, lat, lon):
        """(text, cached) of the geocoder's answer for a name (kept for a week); RuntimeError when it does not answer."""
        def ask(query):
            token = ACTIVITY.begin("photon", "search")
            try:
                ACTIVITY.update(token, state="running", mirror=1, of=1)
                return json.dumps(self.geocoder(*query), separators=(",", ":"), ensure_ascii=False)
            finally:
                ACTIVITY.end(token)
        return self.get(geo_key(q, lat, lon), (q, lat, lon), upstream=ask)

    def want_timetables(self, lat, lon):
        """Start fetching the timetables of the countries round a point (once; in the background). Not where the route
        database answers: its lines have the timetables' times already."""
        if not self.gtfs.enabled or self.db_covers(lat, lon):
            return
        if self.places.base:
            self.gtfs.want(self.places.countries_near(lat, lon))
        else:
            self.places.want(lat, lon)          # (the countries are not known yet: it calls back when they are)

    def local_search(self, q, lat, lon):
        """Only what is on this computer, in milliseconds: {"elements": stops, "places": towns, "local": true}."""
        self.places.want(lat, lon)
        self.want_timetables(lat, lon)
        elements = self.index.search(q, lat, lon)
        if self.uses_db():
            for e in self.db.named(q, lat, lon):
                if not any(_dist_m(e["lat"], e["lon"], x["lat"], x["lon"]) < 60 for x in elements if x.get("lat") is not None):
                    elements.append(e)
        if self.gtfs.ready():
            for row in self.gtfs.stops_named(q, lat, lon):
                if not any(_dist_m(row[2], row[3], e["lat"], e["lon"]) < 60 for e in elements if e.get("lat") is not None):
                    elements.append(gtfs_node(row))
        return {"elements": elements, "places": self.places.search(q, lat, lon), "local": True}

    MAP_SAME_M = 200          # stops of one name this near are one place on the map (its platforms)
    MAP_STATION_M = 150       # a stop this near a bus station of the map is that station

    def map_stops(self, lat, lon, radius, limit=600, src="auto"):
        """{"stops": [{id, name, lat, lon, kind, lines: [numbers]}]} round a point, from this computer only (the timetables and
        every stop this service has seen): bus stations first, then the stops with most lines; platforms of one stop are one."""
        if self.uses_db(src):
            got = self.db.map_places(lat, lon, radius)
            if got is not None:                                # the route database has the place: its stops and lines only
                return self.merge_map(got, lat, lon, limit, True)
        self.want_timetables(lat, lon)
        places = []                                            # [name, lat, lon, refs, kind]
        for name, la, lo, refs in (self.gtfs.stops_around(lat, lon, radius) if self.gtfs.ready() else []):
            places.append([name, la, lo, set(refs), "stop"])
        with self.index._lock:
            seen = list(self.index.stops.values())
        known = []
        for it in seen:
            if not _near(lat, lon, it["lat"], it["lon"], radius):
                continue
            tg = it["tags"]
            if tg.get("amenity") == "bus_station" or (tg.get("public_transport") == "station"):
                hit = None
                for pl in places:
                    if _dist_m(pl[1], pl[2], it["lat"], it["lon"]) <= self.MAP_STATION_M:
                        hit = pl
                        pl[0], pl[4] = it["name"], "station"           # the map's name of a bus station is the one people know
                if hit is None:
                    places.append([it["name"], it["lat"], it["lon"], set(), "station"])
            else:
                known.append(it)
        if not self.gtfs.ready():                              # no timetables here: the stops this service has seen
            for it in known:
                places.append([it["name"], it["lat"], it["lon"], set(), "stop"])
        return self.merge_map(places, lat, lon, limit, self.gtfs.ready())

    def merge_map(self, places, lat, lon, limit, timetables):
        """The map's answer of [name, lat, lon, refs, kind] places: platforms of one stop as one, bus stations first."""
        merged, by_name, stations = [], {}, []
        for pl in sorted(places, key=lambda x: (x[4] != "station", -len(x[3]))):
            key = fold(pl[0])
            same = None
            for m in by_name.get(key, []) + (stations if pl[4] == "station" else []):
                if _dist_m(m[1], m[2], pl[1], pl[2]) <= self.MAP_SAME_M:
                    same = m
                    break
            if same is None:
                merged.append(pl)
                by_name.setdefault(key, []).append(pl)
                if pl[4] == "station":
                    stations.append(pl)
            else:
                same[3] |= pl[3]
        merged.sort(key=lambda x: (x[4] != "station", -len(x[3]), _dist_m(lat, lon, x[1], x[2])))
        def by_number(r):
            return (int(re.match(r"\d*", r).group() or 10 ** 6), r)
        out = [{"id": i + 1, "name": m[0], "lat": round(m[1], 6), "lon": round(m[2], 6), "kind": m[4],
                "lines": sorted(m[3], key=by_number)[:24]} for i, m in enumerate(merged[:limit])]
        return {"stops": out, "timetables": timetables}

    def uses_db(self, src="auto"):
        """Does a request with this source choice read the route database?"""
        return self.db.enabled and (src == "db" or (src == "auto" and not self.live))

    def db_covers(self, lat, lon, src="auto"):
        """The route database answers for this place (nothing is asked of the live servers, no timetables are downloaded)."""
        try:
            return self.uses_db(src) and self.db.covers(lat, lon)
        except (OSError, ValueError):
            return False

    def nearby(self, lat, lon, offline=False, src="auto"):
        """(text, cached): the stops and lines around a point: OpenStreetMap's (kept per cell) with the timetables' lines
        merged in; the timetables alone while no map server answers. `offline`: only what this computer has (a background
        load of the mod: never a public server); None when it has nothing.
        Where the route database has the place it answers (lines and stops prepared in advance, the real timetables' times
        in them): nothing is asked of the map servers and no timetables are downloaded."""
        if self.uses_db(src):
            text = self.db.nearby(snap(lat), snap(lon), RADIUS_M, online=True)
            if text is not None:
                return text, True
            if src == "db":                  # only the database was asked for: a place it lacks has nothing
                return '{"elements":[]}', True
        if not offline:
            self.want_timetables(lat, lon)
        found = self.gtfs.lines_near(snap(lat), snap(lon), RADIUS_M) if self.gtfs.ready() else None
        key, query = nearby_key(lat, lon), nearby_query(snap(lat), snap(lon))
        have, age = self.cache.get(key)
        partial = False
        if offline:
            if have is None and not (found and found["lines"]):
                return None, True
            text = merge_gtfs(have, found, have is None) if found and found["lines"] else have
            return text, True
        if not found or not found["lines"] or (have is not None and age is not None and age < self.ttl):
            text, cached = self.get(key, query, post=slim_nearby)
        else:
            # the timetables are here, the map server may be slow: wait for it a few seconds, then answer with the timetables
            # alone (marked "partial": the mod does not keep such an answer) while the map's answer goes on being fetched
            box = {}
            INTEREST.touch(key)              # nobody waits on this fetch: it goes on while the menu keeps asking

            def work():
                CURRENT.wanted = lambda: False
                try:
                    box["v"] = self.get(key, query, post=slim_nearby)
                except RuntimeError as e:
                    box["e"] = e
            th = threading.Thread(target=work, daemon=True)
            th.start()
            th.join(NEARBY_WAIT_S)
            if "v" in box:
                text, cached = box["v"]
            else:
                say("nearby: the map server is slow or down; the timetables first")
                text, cached, partial = None, False, True
        if found and found["lines"]:
            text = merge_gtfs(text, found, partial)
        elif self.gtfs.enabled and self.places.base and self.gtfs.coming(self.places.countries_near(lat, lon)):
            # the timetables of this country are on their way (a minute): the answer is marked so the mod asks again
            data = json.loads(text)
            data["partial"] = True
            text = json.dumps(data, separators=(",", ":"), ensure_ascii=False)
        return text, cached

    def lines(self, ref, lat, lon, local=False, src="auto"):
        """(text, cached): the lines with this number: the route database's where it has the place (`local`: only its tiles on
        this computer), else those the timetables know, then OpenStreetMap's."""
        if self.uses_db(src):
            text = self.db.lines_numbered(ref, lat, lon, online=not local)
            if text is not None:
                return text, True
            if src == "db":
                return '{"elements":[]}', True
        gt = self.gtfs.lines_numbered(ref, lat, lon) if self.gtfs.ready() else []
        if local:
            found = self.index.find_lines(ref, lat, lon)
            have = {fold(e["tags"].get("ref")) for e in gt}
            elements = gt + [e for e in found if fold(e["tags"].get("ref")) not in have]
            return json.dumps({"elements": elements, "local": True}, separators=(",", ":"), ensure_ascii=False), True
        try:
            text, cached = self.get(lines_key(ref, lat, lon), lines_query(ref, lat, lon))
        except RuntimeError:
            if not gt:
                raise
            return json.dumps({"elements": gt}, separators=(",", ":"), ensure_ascii=False), False
        if not gt:
            return text, cached
        data = json.loads(text)
        data["elements"] = gt + [e for e in data.get("elements", []) if e.get("type") != "relation"]
        return json.dumps(data, separators=(",", ":"), ensure_ascii=False), cached

    def route_limits(self, road):
        """road_limits() from the towns of this computer (the files are fetched the first time, as the map of towns does);
        None when there are no towns or nothing is known about the place."""
        pl = self.places
        if not (pl.enabled and road):
            return None
        try:
            if not pl.ready(*road[0]) and not (pl.ensure(*road[0]) and pl.ready(*road[0])):
                return None
            return road_limits(pl.in_box, road)
        except (OSError, ValueError, KeyError) as e:
            say(f"limits: {type(e).__name__} {str(e)[:80]}")
            return None

    def with_limits(self, text):
        """A route answer of Overpass with the towns round its road (rel.limits) added: the answer's way tags carry the
        maxspeed already. The text unchanged when there is nothing to add."""
        try:
            data = json.loads(text)
            rel = next(e for e in data["elements"] if e.get("type") == "relation")
            road = [(g["lat"], g["lon"]) for m in rel.get("members", []) if m.get("type") == "way"
                    for g in m.get("geometry") or []]
            lim = self.route_limits(road)
            if lim is None:
                return text
            rel["limits"] = lim
            return json.dumps(data, separators=(",", ":"), ensure_ascii=False)
        except (ValueError, KeyError, TypeError, StopIteration):
            return text

    def road_through(self, points, offline=False, fallback=None):
        """The road through stops, [(lat, lon), ...]: the routing servers' (asked in windows of 24 stops, each kept), or when
        `offline` only roads already kept; straight lines where there is none (`fallback`, a list, gets an item for each such window)."""
        stops = [(round(a, 6), round(b, 6)) for a, b in points]
        road, window, i = [], 24, 0
        while i < len(stops) - 1:
            pts = stops[i:i + window]
            if len(pts) >= 2 and all(hav(a, b) <= MAX_LEG_M for a, b in zip(pts, pts[1:])):
                if offline:
                    kept, _ = self.cache.get(path_key(pts))
                    seg = [(a, b) for a, b in json.loads(kept)["points"]] if kept else pts
                else:
                    p, _ = self.path(pts)
                    seg = [(a, b) for a, b in p["points"]]
                    if p.get("source") != "osrm" and fallback is not None:
                        fallback.append(i)
            else:
                seg = pts
                if fallback is not None:
                    fallback.append(i)
            road += seg if not road else seg[1:]
            i += window - 1
        return road

    def export_route(self, d):
        """Writes a hand-made line (the mod's route builder: stops with names and places) as files for the hand-made layer of the route
        database (edits/<CC>/new/<line>.json and edits/<CC>/stops.json), into <cache>/../export/<CC>/: the stops that the database has
        keep their ids, the road is the one the routing server gives. Returns what was written. ValueError for bad input."""
        pts = d.get("points") if isinstance(d, dict) else None
        if not isinstance(pts, list) or not 2 <= len(pts) <= EXPORT_MAX_POINTS:
            raise ValueError(f"a line needs 2 to {EXPORT_MAX_POINTS} stops")
        clean = []
        for p in pts:
            try:
                lat, lon = float(p["lat"]), float(p["lon"])
            except (KeyError, TypeError, ValueError):
                raise ValueError("a stop has no place")
            if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                raise ValueError("a stop is out of range")
            clean.append({"name": str(p.get("name") or "")[:120], "lat": round(lat, 6), "lon": round(lon, 6)})
        ref = re.sub(r"[^\w\-/ ]", "", str(d.get("ref") or "")).strip()[:6] or "My"
        first, last = clean[0]["name"], clean[-1]["name"]
        name = str(d.get("name") or "")[:120] or f"{ref}: {first} - {last}"
        cc, new_stops, stop_list, matched = None, {}, [], 0
        for p in clean:
            c, st = self.db.locate(p["lat"], p["lon"], p["name"])
            cc = cc or c
            if st is not None:
                sid, matched = st["id"], matched + 1
            else:
                sid = EXPORT_STOP_BASE + stable_hash(f"hand|{p['name']}|{p['lat']:.5f}|{p['lon']:.5f}")
                new_stops[str(sid)] = {"n": p["name"], "lat": p["lat"], "lon": p["lon"], "k": "p"}
            stop_list.append({"s": sid})
        cc = cc or "ZZ"
        try:
            straight = []
            road = self.road_through([(p["lat"], p["lon"]) for p in clean], False, straight)
            if straight:
                raise RuntimeError("the routing server did not answer for all of it")
        except Exception as e:           # (no routing server: the line has no road, the service asks for one when it is used)
            say(f"export: no road ({e})")
            road = None
        ways = [{"g": polyline_encode(simplify(road, 2.0))}] if road and len(road) >= 2 else []
        tags = {"ref": ref, "name": name, "from": first, "to": last, "route": "bus", "public_transport:version": "2"}
        if re.match(r"^#[0-9a-fA-F]{6}$", str(d.get("colour") or "")):
            tags["colour"] = d["colour"].lower()
        rid = EXPORT_ROUTE_BASE + stable_hash(f"hand|{ref}|{name}|{first}|{last}")
        rec = {"v": 1, "id": rid, "cc": cc, "mode": "bus", "t": tags, "ways": ways, "stops": stop_list,
               "src": [{"k": "edit", "by": "export", "date": datetime.date.today().isoformat()}]}
        base = self.cache.dir.parent / "export" / cc
        (base / "new").mkdir(parents=True, exist_ok=True)
        files = []
        line_file = base / "new" / (re.sub(r"[^A-Za-z0-9_-]", "_", ref) + f"_{rid}.json")
        line_file.write_text(json.dumps(rec, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
        files.append(str(line_file))
        if new_stops:
            sf = base / "stops.json"
            try:
                have = json.loads(sf.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                have = {}
            have.update(new_stops)
            sf.write_text(json.dumps(have, ensure_ascii=False, indent=1, sort_keys=True) + "\n", encoding="utf-8")
            files.append(str(sf))
        (base.parent / "README.txt").write_text(
            "Lines made by hand, written by the Earth Bus Routes data service in the shape of the hand-made layer of the route database\n"
            "(https://github.com/Robitnik/earth-bus-routes-db-eu). To add them to the database, copy <CC>/new/*.json and merge\n"
            "<CC>/stops.json into edits/<CC>/ of that repository and open a pull request (see docs/FORMAT.md, Edits). The country\n"
            "code is the one of the nearest known stop (ZZ when the place is not in the database yet: rename the folder).\n", encoding="utf-8")
        return {"cc": cc, "id": rid, "folder": str(base), "files": files, "stops": len(stop_list), "matched": matched,
                "new_stops": len(new_stops), "road": bool(ways)}

    def db_route(self, rid, offline=False):
        """The route answer of a line of the route database (None when it is not there), with the towns round its road."""
        text = self.db.route(rid, road_for=lambda pts: self.road_through(pts, offline), online=not offline)
        return self.with_limits(text) if text is not None else None

    def gtfs_route(self, rid, offline=False):
        """`offline`: the road only from roads already kept (else straight lines between the stops), never a request.
        The text of a route answer for a line of the timetables: a relation with one way (the road through its stops, asked
        of the routing servers in windows of 24 stops) and its stops with their times from the start, as the mod reads
        an OpenStreetMap route."""
        pat = self.gtfs.pattern(rid)
        if pat is None:
            raise RuntimeError("no such line in the timetables")
        stops = pat["stops"]
        road = self.road_through([(x["lat"], x["lon"]) for x in stops], offline)
        way = {"type": "way", "ref": GTFS_ROUTE + rid % GTFS_ROUTE, "role": "",
               "geometry": [{"lat": a, "lon": b} for a, b in road]}
        members = [way] + [{"type": "node", "ref": GTFS_NODE + x["rowid"], "role": "platform", "lat": x["lat"], "lon": x["lon"]}
                           for x in stops]
        first, last = (stops[0]["name"], stops[-1]["name"]) if stops else ("", "")
        rel = {"type": "relation", "id": rid, "members": members,
               "tags": {"type": "route", "route": "bus", "ref": pat["ref"], "name": f"{pat['ref']}: {first} - {last}", "from": first,
                        "to": last, "operator": pat["agency"], "public_transport:version": "2", "bus_routes:source": "gtfs"},
               "gtfs": {"offs": [x["off"] for x in stops], "starts": pat["starts"]}}
        lim = self.route_limits(road)
        if lim is not None:
            rel["limits"] = lim
        seen, nodes = set(), []
        for x in stops:
            if x["rowid"] not in seen:
                seen.add(x["rowid"])
                nodes.append(gtfs_node((x["sid"], x["name"], x["lat"], x["lon"], x["rowid"])))
        return json.dumps({"elements": [rel] + nodes}, separators=(",", ":"), ensure_ascii=False)

    def stations(self, lat, lon, src="auto"):
        """(text, cached): the bus stations round a point: the route database's where it has the place, else Overpass's."""
        if self.uses_db(src):
            text = self.db.stations(lat, lon)
            if text is not None:
                return text, True
            if src == "db":
                return '{"elements":[]}', True
        c = STATIONS_CELL_DEG
        slat, slon = round(round(lat / c) * c, 4), round(round(lon / c) * c, 4)
        return self.get(stations_key(lat, lon), stations_query(slat, slon))

    def search(self, q, lat, lon):
        """(text, cached): the towns and stops on this computer first, the geocoder's (one request, ~1 s) after them; the
        slow map database only when neither knows the name."""
        local = self.local_search(q, lat, lon)
        try:
            text, cached = self.geocode(q, lat, lon)
            geo = json.loads(text)
        except (RuntimeError, ValueError) as e:
            say(f"search: {e}; what is on this computer only")
            geo, cached = {}, True
        out = {"elements": merge_elements(local["elements"], geo.get("elements") or []),
               "places": merge_places(local["places"], geo.get("places") or []),
               "source": geo.get("source") or "local"}
        if not out["elements"] and not out["places"]:
            if self.db_covers(lat, lon):                     # the database knows the place: a name it lacks is not worth 90 s of Overpass
                return json.dumps(out, separators=(",", ":"), ensure_ascii=False), cached
            return self.get(search_key(q, lat, lon), search_query(q, lat, lon))
        return json.dumps(out, separators=(",", ":"), ensure_ascii=False), cached

    def towns(self, lat, lon):
        """(text, cached): the towns round a point from the GeoNames files (downloaded the first time, ~2 s), else Overpass."""
        if self.places.enabled and self.places.ensure(lat, lon) and self.places.ready(lat, lon):
            return json.dumps({"towns": self.places.towns(lat, lon), "source": "geonames"}, separators=(",", ":"),
                              ensure_ascii=False), True
        c = TOWNS_CELL_DEG
        slat, slon = round(round(lat / c) * c, 4), round(round(lon / c) * c, 4)
        return self.get(towns_key(lat, lon), towns_query(slat, slon), post=slim_towns)

    def load_index(self):
        """Index the cache folder (call from a thread at start: it can hold many answers)."""
        self.indexed = self.index.load(self.cache.dir)
        say(f"index: {self.indexed} entries, {len(self.index.stops)} stops, {len(self.index.lines)} lines")

    def get(self, key, query, post=None, upstream=None):
        """(text, cached): a fresh cached answer, else a fetched one (kept; `post` shrinks it first), else a stale cached
        one, else RuntimeError. Requests for one key wait for each other: the second finds the first one's answer cached."""
        with _key_locks_guard:
            lock = _key_locks.setdefault(key, threading.Lock())
        with lock:
            text, age = self.cache.get(key)
            if text is not None and age is not None and age < self.ttl:
                self.served["cached"] += 1
                return text, True
            CURRENT.label = key
            # wanted while the game waits on this thread's connection, or while somebody asked for this key lately
            outer = getattr(CURRENT, "wanted", None)
            CURRENT.check = (lambda: INTEREST.alive(key) or outer()) if outer else None
            try:
                fresh = (upstream or self.upstream)(query)
            except Abandoned as e:
                self.served["dropped"] += 1
                say(f"{key}: dropped: {e}")
                if text is not None:
                    return text, True
                raise
            except RuntimeError as e:
                if text is not None:
                    self.served["stale"] += 1
                    say(f"{key}: {e}; the cached copy is {age / 86400:.1f} days old, using it")
                    return text, True
                self.served["failed"] += 1
                say(f"{key}: failed: {e}")
                raise
            finally:
                CURRENT.check = None
            if post:
                fresh = post(fresh)
            self.cache.put(key, fresh)
            self.index.add(fresh, anchor_of(key))
            self.served["fetched"] += 1
            say(f"{key}: fetched {len(fresh) // 1024} KB")
            return fresh, False

    def path(self, pts):
        """(dict, cached): the road route through pts; a straight-line one (never kept) when no routing server answers."""
        try:
            text, cached = self.get(path_key(pts), pts, upstream=self.router)
            return json.loads(text), cached
        except RuntimeError as e:
            say(f"path: {e}; straight lines instead")
            return straight_path(pts), False

    def along(self, pts, src="auto"):
        """(text, cached) of the stops near the road route (the route database's where it has the places, else Overpass's);
        none while there is only a straight fallback."""
        p, _ = self.path(pts)
        if p["source"] != "osrm":
            return '{"elements":[],"fallback":true}', False
        road = p["points"]
        if self.uses_db(src):
            text = self.db.along(road)
            if text is not None:
                return text, True
            if src == "db":
                return '{"elements":[]}', True
        return self.get(along_key(pts), along_query(road), post=lambda text: filter_along(text, road), upstream=self.upstream_once)


# ---- shifts and depots (plan 006, stage B) -------------------------------------------------------------------------------
# A shift is a chain of trips with layovers at the termini. The national timetables have no block ids, so the chain is built here:
# after a trip's last stop, the earliest departure of any line that leaves from that terminus (within SHIFT_NEAR_M) between
# SHIFT_MIN_TURN_S and SHIFT_MAX_WAIT_S later; a departure of the same line (its way back) is preferred. No network is used.
SHIFT_NEAR_M = 200
SHIFT_MIN_TURN_S = 300
SHIFT_MAX_WAIT_S = 2400
SHIFT_MAX_TRIPS = 14
SHIFT_MAX_MINS = 720
DEPOT_RADIUS_M = 10000
DEPOT_CELL_DEG = 0.05
FEATURES.extend(["shift", "depot"])
FEATURES.append("routecached")
FEATURES.extend(["source", "export"])
FEATURES.append("voice")          # /v1/voice (the voice of a country, downloaded while asked), /v1/say (a WAV): the stop announcer (0.13)        # ?src=auto|db|live on nearby and route (0.12); POST /v1/export (0.12)
FEATURES.append("nearbycached")    # /v1/nearby?..&cached=1: from this computer only (0.10.3)      # /v1/route?id=..&cached=1: from this computer only (0.10.1)


class Shifts:
    """Chains of trips out of the timetable index of a Gtfs (read only; it takes the Gtfs's lock)."""

    def __init__(self, gtfs):
        self.gtfs = gtfs

    @staticmethod
    def _day_bit(db, pid, meta, day):
        """The day of the index (a bit of the departures' mask) that stands for weekday `day` (1 Monday .. 7 Sunday): of the two
        such days in the next two weeks the one the pattern runs most on (a public holiday runs a Sunday timetable), as the
        departure lists of a route do. None when the index has no such day."""
        import datetime
        day0 = datetime.datetime.strptime(meta.get("today", "19700101"), "%Y%m%d").date()
        bits = [i for i in range(min(int(meta.get("days", "0")), 14)) if (day0 + datetime.timedelta(days=i)).isoweekday() == day]
        if not bits:
            return None
        masks = [m for (m,) in db.execute("SELECT mask FROM deps WHERE pid=?", (pid,))]
        return max(bits, key=lambda b: sum(1 for m in masks if m >> b & 1))

    @staticmethod
    def _info(db, pid, cache):
        """{ref, head, stops: [sid], offs: [s], from, to} of a pattern, or None."""
        if pid in cache:
            return cache[pid]
        p = db.execute("SELECT ref, head, stops, offs FROM patterns WHERE pid=?", (pid,)).fetchone()
        info = None
        if p is not None:
            sl, offs = p[2].split(","), [int(x) for x in p[3].split(",")]

            def name(sid):
                r = db.execute("SELECT name FROM stops WHERE sid=?", (sid,)).fetchone()
                return r[0] if r else ""
            info = {"ref": p[0], "head": p[1] or "", "stops": sl, "offs": offs, "from": name(sl[0]), "to": name(sl[-1])}
        cache[pid] = info
        return info

    @staticmethod
    def _item(pid, start, info, prev_end):
        end = start + info["offs"][-1]
        return {"pid": pid, "id": GTFS_ROUTE + pid, "start": start, "end": end, "ref": info["ref"], "head": info["head"],
                "from": info["from"], "to": info["to"], "layover": 0 if prev_end is None else start - prev_end}

    def chain(self, pid, start, day, mins):
        """[{pid, id (relation id for /v1/route), start, end, ref, head, from, to, layover}]: the trip `pid` leaving at `start`
        (seconds from midnight, may pass 86400) on weekday `day`, then the trips that follow it for `mins` minutes of the shift.
        [] when the timetables do not know the pattern."""
        pid = pid - GTFS_ROUTE if pid >= GTFS_ROUTE else pid
        mins = max(1, min(int(mins), SHIFT_MAX_MINS))
        with self.gtfs._lock:
            for db in self.gtfs.dbs.values():
                cache = {}
                first = self._info(db, pid, cache)
                if first is None:
                    continue
                return self._chain_db(db, pid, first, int(start), day, mins, cache)
        return []

    def _chain_db(self, db, pid, first, start, day, mins, cache):
        meta = dict(db.execute("SELECT k, v FROM meta").fetchall())
        bit = self._day_bit(db, pid, meta, day)
        out = [self._item(pid, start, first, None)]
        if bit is None:
            return out
        limit = start + mins * 60
        used = {(pid, start)}
        cur = first
        while len(out) < SHIFT_MAX_TRIPS:
            end = out[-1]["end"]
            lo, hi = end + SHIFT_MIN_TURN_S, min(end + SHIFT_MAX_WAIT_S, limit)
            if hi < lo:
                break
            row = db.execute("SELECT lat, lon FROM stops WHERE sid=?", (cur["stops"][-1],)).fetchone()
            if row is None:
                break
            sids = [r[0] for r in self.gtfs._stops_near(db, row[0], row[1], SHIFT_NEAR_M)]
            pids = []
            for i in range(0, len(sids), 400):
                chunk = sids[i:i + 400]
                pids += [r[0] for r in db.execute(
                    f"SELECT DISTINCT pid FROM sp WHERE pos=0 AND sid IN ({','.join('?' * len(chunk))})", chunk)]
            best = None
            for i in range(0, len(pids), 400):
                chunk = pids[i:i + 400]
                for p2, st, mask in db.execute(
                        f"SELECT pid, start, mask FROM deps WHERE pid IN ({','.join('?' * len(chunk))}) AND start BETWEEN ? AND ?",
                        chunk + [lo, hi]):
                    if not mask >> bit & 1 or (p2, st) in used:
                        continue
                    info = self._info(db, p2, cache)
                    if info is None or len(info["offs"]) < 2:
                        continue
                    key = (info["ref"] != cur["ref"], st, p2)         # the same line first, then the earliest
                    if best is None or key < best[0]:
                        best = (key, p2, st, info)
            if best is None:
                break
            _, p2, st, info = best
            used.add((p2, st))
            out.append(self._item(p2, st, info, end))
            cur = info
        return out


def depot_query(lat, lon, radius=DEPOT_RADIUS_M):
    a = f"around:{int(radius)},{lat:.4f},{lon:.4f}"
    return (f"[out:json][timeout:50];(nwr[amenity=bus_station]({a});nwr[landuse=depot]({a});nwr[building=transportation]({a});"
            f'nwr["name"~"depo|vozovna|gar[aá][zž]|depot",i]({a}););out tags center 300;')


def depot_key(lat, lon):
    snap5 = lambda v: round(round(v / DEPOT_CELL_DEG) * DEPOT_CELL_DEG, 4)
    return f"depot_{snap5(lat):.2f}_{snap5(lon):.2f}"


def pick_depot(text, lat, lon):
    """The bus depot nearest to (lat, lon) in an Overpass answer, else the nearest bus station: {"depot": {name, lat, lon, kind
    ("depot" | "station"), dist} or null} as text. A depot is a landuse=depot / building=transportation, or a name with depo,
    vozovna, garaz; a railway one, a car park or a garage building is not."""
    data = json.loads(text)
    depots, stations = [], []
    for e in data.get("elements", []):
        tags = e.get("tags") or {}
        la, lo = e.get("lat"), e.get("lon")
        if la is None and e.get("center"):
            la, lo = e["center"].get("lat"), e["center"].get("lon")
        if la is None or lo is None:
            continue
        name = tags.get("name", "")
        d = _dist_m(lat, lon, la, lo)
        if tags.get("amenity") == "bus_station":
            stations.append((d, name, la, lo))
            continue
        if tags.get("railway") or tags.get("amenity") == "parking" or tags.get("building") in ("garage", "garages"):
            continue
        folded = fold(name)
        if tags.get("landuse") == "depot" or tags.get("building") == "transportation" or re.search(r"depo|vozovna|garaz|depot", folded):
            bus = bool(re.search(r"bus|csad|dopravn|mhd", folded + " " + fold(tags.get("operator", ""))))
            depots.append((d - (3000 if bus else 0), d, name, la, lo))
    if depots:
        _, d, name, la, lo = min(depots)
        pick = {"name": name or "Depot", "lat": round(la, 6), "lon": round(lo, 6), "kind": "depot", "dist": int(d)}
    elif stations:
        d, name, la, lo = min(stations)
        pick = {"name": name or "Bus station", "lat": round(la, 6), "lon": round(lo, 6), "kind": "station", "dist": int(d)}
    else:
        pick = None
    return json.dumps({"depot": pick}, separators=(",", ":"), ensure_ascii=False)


def find_depot(service, lat, lon):
    """(text, cached) of pick_depot's answer for the depot round a point (kept per ~5 km cell like any answer)."""
    c = DEPOT_CELL_DEG
    slat, slon = round(round(lat / c) * c, 4), round(round(lon / c) * c, 4)
    return service.get(depot_key(lat, lon), depot_query(slat, slon), post=lambda t: pick_depot(t, slat, slon))


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
            # while this request is served, the public-server loops ask whether the game still waits for it
            CURRENT.wanted = lambda: not client_gone(self.connection)
            try:
                return self._get()
            finally:
                CURRENT.wanted = None

        def do_POST(self):
            """POST /v1/export: a hand-made line as files for the hand-made layer of the route database. JSON only (a web page cannot send
            that to this computer without a permission this service never gives)."""
            if not host_ok(self.headers.get("Host"), port):
                return self.fail(403, "wrong Host")
            u = urllib.parse.urlsplit(self.path)
            if u.path != "/v1/export":
                return self.fail(404, "unknown request")
            if "application/json" not in (self.headers.get("Content-Type") or ""):
                return self.fail(415, "JSON only")
            try:
                n = int(self.headers.get("Content-Length") or 0)
                if not 0 < n <= 256 * 1024:
                    return self.fail(413, "body too large")
                body = json.loads(self.rfile.read(n).decode("utf-8"))
                ans = service.export_route(body)
            except (ValueError, UnicodeDecodeError) as e:
                return self.fail(400, str(e))
            except Exception as e:
                say(f"export failed: {e!r}")
                return self.fail(500, "export failed")
            return self.send_json(200, json.dumps({"ok": True, "data": ans}, ensure_ascii=False))

        def _get(self):
            if not host_ok(self.headers.get("Host"), port):
                return self.fail(403, "wrong Host")
            u = urllib.parse.urlsplit(self.path)
            q = urllib.parse.parse_qs(u.query)
            try:
                if u.path == "/v1/info":
                    return self.send_json(200, json.dumps({"ok": True, "api": 1, "app": APP, "version": VERSION, "features": FEATURES}))
                if u.path == "/v1/db":
                    return self.send_json(200, json.dumps({"ok": True, "data": {"enabled": service.db.enabled, "live": service.live,
                                                                               "repos": service.db.status()}}))
                if u.path == "/v1/gtfs":
                    if q.get("lat") and q.get("lon"):
                        service.want_timetables(float(q["lat"][0]), float(q["lon"][0]))
                    return self.send_json(200, json.dumps({"ok": True, "data": service.gtfs.status()}))
                if u.path == "/v1/shift":
                    pid, start = int(q["pid"][0]), int(q["start"][0])
                    day, mins = int(q.get("day", ["1"])[0]), int(q.get("mins", ["120"])[0])
                    if not (1 <= day <= 7 and 0 <= start < 10 ** 6 and 1 <= mins):
                        return self.fail(400, "pid / start / day / mins out of range")
                    trips = Shifts(service.gtfs).chain(pid, start, day, mins) if service.gtfs.ready() else []
                    return self.send_json(200, json.dumps({"ok": True, "cached": True, "data": {
                        "trips": trips, "source": "gtfs", "ready": service.gtfs.ready()}}, ensure_ascii=False))
                if u.path == "/v1/depot":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    text, cached = find_depot(service, lat, lon)
                    return self.send_json(200, b'{"ok":true,"cached":' + (b"true" if cached else b"false") + b',"data":' + text.encode("utf-8") + b"}")
                if u.path in ("/v1/voice", "/v1/say"):
                    lat = float(q["lat"][0]) if q.get("lat") else None
                    lon = float(q["lon"][0]) if q.get("lon") else None
                    lang = q.get("lang", [""])[0]
                    if lang not in VOICES:
                        cc = q.get("cc", [""])[0]
                        if not cc and lat is not None and lon is not None and service.places.base:
                            near = service.places.countries_near(lat, lon)
                            cc = near[0] if near else ""
                        lang = announce_lang(cc, lat, lon, q.get("ui", [""])[0])
                    if u.path == "/v1/voice":
                        return self.send_json(200, json.dumps({"ok": True, "data": service.voice.prepare(lang)}))
                    if q.get("text"):
                        text = q["text"][0]
                    else:
                        kind = q.get("kind", [""])[0]
                        if kind not in SAY_KINDS or not q.get("name") or not lang:
                            return self.fail(400, "kind / name / lang")
                        text = announcement(lang, kind, q["name"][0], q.get("req", ["0"])[0] == "1")
                    try:
                        data, secs, cid = service.voice.speak(lang, text, q.get("gong", ["1"])[0] != "0")
                    except VoiceNotReady as e:
                        return self.fail(409, f"voice {e}")
                    if q.get("file", ["0"])[0] == "1":      # the game and the service share this computer: the clip's path is enough
                        return self.send_json(200, json.dumps({"ok": True, "data": {
                            "path": str(service.voice.clip_path(cid)), "seconds": secs, "clip": cid, "lang": lang, "text": text}}, ensure_ascii=False))
                    self.send_response(200)
                    self.send_header("Content-Type", "audio/wav")
                    self.send_header("Content-Length", str(len(data)))
                    self.send_header("X-Seconds", str(secs))
                    self.send_header("X-Clip", cid)
                    self.send_header("X-Lang", lang)
                    self.send_header("X-Text", urllib.parse.quote(text))
                    self.send_header("Cache-Control", "no-store")
                    self.send_header("Connection", "close")
                    self.end_headers()
                    self.wfile.write(data)
                    return None
                if u.path == "/v1/progress":
                    return self.send_json(200, json.dumps({"ok": True, "data": ACTIVITY.snapshot()}))
                if u.path == "/v1/status":
                    return self.send_json(200, json.dumps({
                        "ok": True, "version": VERSION, "uptime": time.time() - service.started,
                        "served": service.served, "log": log_lines[-20:], "cache": str(service.cache.dir),
                        "index": {"stops": len(service.index.stops), "lines": len(service.index.lines)}}))
                if u.path == "/v1/connections":
                    day = int(q["day"][0])
                    if not 1 <= day <= 7:
                        return self.fail(400, "day out of range")
                    sid = q["sid"][0] if q.get("sid") else None
                    lat = float(q["lat"][0]) if q.get("lat") else None
                    lon = float(q["lon"][0]) if q.get("lon") else None
                    if sid is None and (lat is None or lon is None or not (-85 <= lat <= 85 and -180 <= lon <= 180)):
                        return self.fail(400, "sid or lat / lon needed")
                    ans = gtfs_connections(service.gtfs, float(q["t"][0]), day, int(q.get("win", ["8"])[0]), sid, lat, lon,
                                           clean_ref(q["ref"][0]) if q.get("ref") else None)
                    return self.send_json(200, b'{"ok":true,"cached":true,"data":' + json.dumps(ans, separators=(",", ":"), ensure_ascii=False).encode("utf-8") + b"}")
                if u.path == "/v1/departures":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    t, day = float(q["t"][0]), int(q["day"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180) or not 1 <= day <= 7 or not -86400 <= t <= 3 * 86400:
                        return self.fail(400, "lat / lon / t / day out of range")
                    ans = gtfs_departures(service.gtfs, lat, lon, t, day, float(q.get("r", [DEP_RADIUS_M])[0]), int(q.get("mins", ["30"])[0]))
                    ans["ready"] = service.gtfs.ready()
                    return self.send_json(200, b'{"ok":true,"cached":true,"data":' + json.dumps(ans, separators=(",", ":"), ensure_ascii=False).encode("utf-8") + b"}")
                if u.path == "/v1/nearby":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    src = parse_src(q)
                    if q.get("cached", ["0"])[0] == "1":            # a background load: this computer only, at once
                        text, cached = service.nearby(lat, lon, offline=True, src=src)
                        if text is None:
                            return self.fail(404, "not on this computer")
                    else:
                        text, cached = service.nearby(lat, lon, src=src)
                elif u.path == "/v1/route":
                    rid = int(q["id"][0])
                    offline = q.get("cached", ["0"])[0] == "1"     # a background load: this computer only, at once
                    src = parse_src(q)
                    if service.uses_db(src) and (rid >= DB_ROUTE_MIN or rid < GTFS_ROUTE):
                        text = service.db_route(rid, offline)
                        if text is not None:
                            return self.send_json(200, b'{"ok":true,"cached":true,"data":' + text.encode("utf-8") + b"}")
                        if rid >= DB_ROUTE_MIN or src == "db":
                            return self.fail(404, "no such line in the route database")
                    elif src == "live" and rid >= DB_ROUTE_MIN:
                        return self.fail(404, "this line is only in the route database")
                    if GTFS_ROUTE <= rid < GTFS_NODE:
                        text, cached = service.gtfs_route(rid, offline=offline), False
                        return self.send_json(200, b'{"ok":true,"cached":false,"data":' + text.encode("utf-8") + b"}")
                    if not 0 < rid < 10 ** 12:
                        return self.fail(400, "id out of range")
                    if offline:
                        text = service.cache.get(route_key(rid))[0] or service.cache.get(f"route_{rid}")[0]
                        if text is None:
                            return self.fail(404, "not on this computer")
                        return self.send_json(200, b'{"ok":true,"cached":true,"data":' + service.with_limits(text).encode("utf-8") + b"}")
                    try:
                        text, cached = service.get(route_key(rid), route_query(rid))
                    except RuntimeError as e:
                        if "HTTP 400" not in str(e):
                            raise
                        # the servers refuse the longer query (a syntax they do not know): the plain route, kept under its own key
                        say(f"route {rid}: the query with the near bus stops was refused; the plain one instead")
                        text, cached = service.get(f"route_{rid}", route_query_basic(rid))
                    text = service.with_limits(text)
                elif u.path == "/v1/path":
                    pts = parse_pts(q["pts"][0])
                    check_legs(pts)
                    p, cached = service.path(pts)
                    text = json.dumps(p, separators=(",", ":"))
                elif u.path == "/v1/along":
                    pts = parse_pts(q["pts"][0])
                    check_legs(pts)
                    text, cached = service.along(pts, src=parse_src(q))
                elif u.path == "/v1/stations":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    text, cached = service.stations(lat, lon, src=parse_src(q))
                elif u.path == "/v1/mapstops":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    r = min(30000.0, max(200.0, float(q.get("r", ["25000"])[0])))
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    text, cached = json.dumps(service.map_stops(lat, lon, r, src=parse_src(q)), separators=(",", ":"), ensure_ascii=False), True
                elif u.path == "/v1/towns":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    text, cached = service.towns(lat, lon)
                elif u.path == "/v1/search":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    if len(fold(q["q"][0]).strip()) < 2:
                        return self.fail(400, "search text too short")
                    if q.get("local"):
                        text, cached = json.dumps(service.local_search(q["q"][0], lat, lon), separators=(",", ":"),
                                                  ensure_ascii=False), True
                    else:
                        text, cached = service.search(q["q"][0], lat, lon)
                elif u.path == "/v1/lines":
                    lat, lon = float(q["lat"][0]), float(q["lon"][0])
                    if not (-85 <= lat <= 85 and -180 <= lon <= 180):
                        return self.fail(400, "lat / lon out of range")
                    ref = clean_ref(q["ref"][0])
                    if ref is None:
                        return self.fail(400, "not a line number")
                    text, cached = service.lines(ref, lat, lon, local=bool(q.get("local")), src=parse_src(q))
                else:
                    return self.fail(404, "unknown path")
            except (KeyError, IndexError, ValueError):
                return self.fail(400, "bad parameters")
            except RuntimeError as e:
                return self.fail(502, str(e)[:300])
            self.send_json(200, b'{"ok":true,"cached":' + (b"true" if cached else b"false") + b',"data":' + text.encode("utf-8") + b"}")

    return Handler


class QuietServer(ThreadingHTTPServer):
    """A client that gives up while the answer is being sent (the game cancels a request, a page is closed) is not an error: the
    default handler prints a traceback to stderr, which BeamNG.Earth's Add-ons page shows as "stopped with an error"."""

    def handle_error(self, request, client_address):
        if isinstance(sys.exc_info()[1], (ConnectionError, TimeoutError)):
            return
        super().handle_error(request, client_address)


def serve(port=PORT, cache_dir=None, service=None):
    if service is None:
        cache = Cache(cache_dir or default_cache_dir())
        base = pathlib.Path(cache.dir).parent
        no_gtfs = os.environ.get("BNE_BUSDATA_GTFS") == "0"
        service = Service(cache, places=Gazetteer(base / "places"), gtfs=Gtfs(None if no_gtfs else base / "timetables"),
                          db=RouteDb(db_repos_from_env(base)), live=os.environ.get("BNE_BUSDATA_LIVE") == "1",
                          voice=Announcer(None if os.environ.get("BNE_BUSDATA_VOICE") == "0" else base / "voice"))
    httpd = QuietServer(("127.0.0.1", port), make_handler(service, port))
    httpd.daemon_threads = True
    say(f"{APP} {VERSION} listening on 127.0.0.1:{port}, cache {service.cache.dir}")
    threading.Thread(target=service.load_index, daemon=True).start()
    threading.Thread(target=service.places.preload, daemon=True).start()
    threading.Thread(target=service.gtfs.preload, daemon=True).start()
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
