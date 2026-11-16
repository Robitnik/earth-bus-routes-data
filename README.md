# Earth Bus Routes data service

A small program that runs beside the game and fetches bus stops and bus routes from OpenStreetMap for the
[Earth Bus Routes](https://github.com/Robitnik/earth-bus-routes) add-on of BeamNG.Earth. The game's Lua sandbox only lets a mod
talk to this computer, so this program does the asking (it listens on 127.0.0.1 only) and keeps the answers on disk.

Add it in the game: Esc > BeamNG.Earth > Add-ons > Add from GitHub > `Robitnik/earth-bus-routes-data`, then Start and
turn on "Starts with BeamNG.Earth". Standard library Python only; BeamNG.Earth runs it with its own Python.

## What it downloads and keeps

Next to its cache (`%LOCALAPPDATA%\earth-bus-routes` on Windows):

- **Towns:** the GeoNames lists of the towns of the countries round you (the world's big towns 3 MB, then e.g. Czechia 1.6 MB,
  Poland 2 MB), once, refreshed monthly. Searching a town by name and the map of towns then need no server.
- **National timetables (Czechia):** the bus timetables of the state's register (CIS JŘ, through the JrUtil project:
  `data.jr.ggu.cz`), about **124 MB** downloaded once and refreshed weekly, kept as a 65 MB index (the archive is deleted).
  It gives every bus line with its real departures. Only downloaded when you play in Czechia. To turn it off, start the
  service with the environment variable `BNE_BUSDATA_GTFS=0`.
- **The route database** (0.11): lines and stops prepared in advance for Europe, Ukraine and the United States, from
  `github.com/Robitnik/earth-bus-routes-db-eu` (raw.githubusercontent.com, with jsDelivr as a mirror). Only the small tile files of
  the places you play in (a few KB to a few hundred KB each) and the lines you open are downloaded and kept; nothing is fetched
  while the menu is closed. Where the database has the place, Overpass is not asked at all. To turn it off start the service with
  `BNE_BUSDATA_DB=0`; `BNE_BUSDATA_DB=<folder>` reads a copy on this computer (hand-edited lines), `BNE_BUSDATA_LIVE=1` asks the
  live servers first (the old way). The menu of the mod has a drop-down for it too (`?src=auto|db|live` on `/v1/nearby` and `/v1/route`).
  `POST /v1/export` writes a route the player built, as files for the database's hand-made layer, into `export/` next to the cache.
- **Answers of OpenStreetMap** (Overpass), the routing server (OSRM) and the geocoder (Photon), kept for a week.

Map data (c) OpenStreetMap contributors, ODbL (the route database is a derivative database, ODbL; its timetable feeds and their
licences are listed in its `sources/FEEDS.md`). Towns (c) GeoNames, CC BY 4.0. Timetables: CIS JŘ (Ministry of Transport of the
Czech Republic, no conditions); stop positions (c) OpenStreetMap contributors and open data of Czech towns and regions (CC BY /
CC BY-SA / CC0), see data.jr.ggu.cz. MIT licence. Source of truth: `companion/` in the main repository.
