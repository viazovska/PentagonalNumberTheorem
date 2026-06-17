#!/usr/bin/env python3
"""Post-process leanblueprint HTML to point Lean declaration links at GitHub source.

leanblueprint 0.0.20 hardcodes URLs to `<dochome>/find/#doc/<decl>` (doc-gen4 site).
This script rewrites them to `<github>/blob/<branch>/<file>#L<line>` so they open
the actual Lean source on GitHub instead of a docs site that may not be deployed.

Run after `leanblueprint web` (or `leanblueprint all`).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

GITHUB_REPO = "viazovska/PentagonalNumberTheorem"
BRANCH = "main"
GH_BASE = f"https://github.com/{GITHUB_REPO}/blob/{BRANCH}"

REPO_ROOT = Path(__file__).resolve().parent.parent
WEB_DIR = REPO_ROOT / "blueprint" / "web"

DECL_RE = re.compile(
    r"^(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|inductive|structure|class|opaque|axiom)\s+"
    r"(\w+)"
)
SKIP_DIRS = {".lake", "docbuild", "blueprint", ".git"}


def build_decl_map() -> dict[str, tuple[str, int]]:
    """Map unqualified declaration names to (relative path, line number)."""
    decl_map: dict[str, tuple[str, int]] = {}
    for lean_file in REPO_ROOT.rglob("*.lean"):
        if any(part in SKIP_DIRS for part in lean_file.parts):
            continue
        rel = lean_file.relative_to(REPO_ROOT)
        with lean_file.open() as f:
            for lineno, line in enumerate(f, start=1):
                m = DECL_RE.match(line)
                if m and m.group(1) not in decl_map:
                    decl_map[m.group(1)] = (str(rel), lineno)
    return decl_map


def patch_html(decl_map: dict[str, tuple[str, int]]) -> int:
    # Match fully-qualified names like `qSeries.jacobiTripleProduct` (allow dots).
    url_re = re.compile(r"https://[^\"]+/docs/find/#doc/([\w.]+)")
    patched = 0

    def repl(m: re.Match) -> str:
        decl = m.group(1)
        # Try the full name first (covers unnamespaced declarations).
        if decl in decl_map:
            f, ln = decl_map[decl]
            return f"{GH_BASE}/{f}#L{ln}"
        # Try the unqualified name (last component after the last dot).
        # This handles `qSeries.jacobiTripleProduct` → lookup `jacobiTripleProduct`.
        short = decl.rsplit(".", 1)[-1]
        if short in decl_map:
            f, ln = decl_map[short]
            return f"{GH_BASE}/{f}#L{ln}"
        return m.group(0)

    for html in WEB_DIR.rglob("*.html"):
        text = html.read_text()
        new_text = url_re.sub(repl, text)
        if new_text != text:
            html.write_text(new_text)
            patched += 1
    return patched


def main() -> int:
    decl_map = build_decl_map()
    if not decl_map:
        print("No Lean declarations found.", file=sys.stderr)
        return 1
    print(f"Found {len(decl_map)} Lean declarations.")
    patched = patch_html(decl_map)
    print(f"Patched {patched} HTML file(s) under {WEB_DIR}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
