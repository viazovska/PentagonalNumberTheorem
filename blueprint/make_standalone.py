#!/usr/bin/env python3
"""Build a single-file dep_graph_standalone.html that needs no sibling assets.

Reads blueprint/web/dep_graph_document.html (which depends on js/ and styles/
folders next to it), inlines the CSS, swaps the local <script src="js/*"> tags
for public jsdelivr CDN URLs, and writes blueprint/web/dep_graph_standalone.html.

The resulting file is ~60 KB and renders the dep graph anywhere an HTTPS
connection is available — open from disk, email, drop on any static host.

Run after post_build.py so the embedded GitHub source links are correct.
"""

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
WEB_DIR = REPO_ROOT / "blueprint" / "web"
SRC = WEB_DIR / "dep_graph_document.html"
DST = WEB_DIR / "dep_graph_standalone.html"

# Versions pinned to match what leanblueprint bundles (d3 v5, d3-graphviz v3,
# @hpcc-js/wasm v1). Upgrading any of these may break the dot string the
# template hands to d3-graphviz.
CDN_REPLACEMENTS = {
    "js/jquery.min.js":  "https://cdn.jsdelivr.net/npm/jquery@3.7.1/dist/jquery.min.js",
    "js/d3.min.js":      "https://cdn.jsdelivr.net/npm/d3@5.16.0/dist/d3.min.js",
    "js/hpcc.min.js":    "https://cdn.jsdelivr.net/npm/@hpcc-js/wasm@1.16.0/dist/index.min.js",
    "js/d3-graphviz.js": "https://cdn.jsdelivr.net/npm/d3-graphviz@3.2.0/build/d3-graphviz.min.js",
}

CSS_FILES = [
    "styles/theme-white.css",
    "styles/dep_graph.css",
    "styles/extra_styles.css",
]


def main() -> int:
    if not SRC.exists():
        print(f"ERROR: {SRC} not found. Run `leanblueprint web` first.")
        return 1

    html = SRC.read_text()

    for css in CSS_FILES:
        css_content = (WEB_DIR / css).read_text()
        link_tag = f'<link rel="stylesheet" href="{css}" />'
        html = html.replace(link_tag, f"<style>\n{css_content}\n</style>")

    for local, cdn in CDN_REPLACEMENTS.items():
        html = html.replace(f'src="{local}"', f'src="{cdn}" crossorigin="anonymous"')

    # Web Workers across CDN origins are often blocked; main-thread WASM works fine.
    html = html.replace("useWorker: true", "useWorker: false")

    # The "Home" link points at the sibling index.html, which isn't shipped here.
    html = re.sub(r'<a class="toc" href="index\.html">Home</a>\s*', "", html)

    DST.write_text(html)
    print(f"Wrote {DST} ({DST.stat().st_size:,} bytes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
