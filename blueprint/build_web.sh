#!/usr/bin/env bash
# Build the web version of the blueprint.
# Lean declaration links point at the doc-gen4 site set via \dochome in src/web.tex.
set -euo pipefail
cd "$(dirname "$0")"
leanblueprint web
python3 make_standalone.py
