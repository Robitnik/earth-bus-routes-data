# Earth Bus Routes data service

A small program that runs beside the game and fetches bus stops and bus routes from OpenStreetMap for the
[Earth Bus Routes](https://github.com/Robitnik/earth-bus-routes) add-on of BeamNG.Earth. The game's Lua sandbox only lets a mod
talk to this computer, so this program does the asking (it listens on 127.0.0.1 only) and keeps the answers on disk.

Add it in the game: Esc > BeamNG.Earth > Add-ons > Add from GitHub > `Robitnik/earth-bus-routes-data`, then Start and
turn on "Starts with BeamNG.Earth". Standard library Python only; BeamNG.Earth runs it with its own Python.

Map data (c) OpenStreetMap contributors, ODbL. MIT licence. Source of truth: `companion/` in the main repository.
