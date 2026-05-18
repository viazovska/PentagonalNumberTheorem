#!/usr/bin/env bash
# Build the web version of the blueprint and rewrite Lean declaration links to GitHub source.
set -euo pipefail
cd "$(dirname "$0")"
leanblueprint web
python3 post_build.py
python3 make_standalone.py
