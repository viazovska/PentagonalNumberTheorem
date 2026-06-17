"""plasTeX package: rewrite lean_decl URLs to GitHub source links at build time.

leanblueprint's make_lean_data() runs at priority 150 and sets:
    node.userdata['lean_urls'] = [(decl, dochome/find/#doc/decl), ...]
This package registers a callback at priority 160 to overwrite those with
direct GitHub source links, so the fix survives every leanblueprint rebuild.
"""

import re
from pathlib import Path

GITHUB_REPO = "viazovska/PentagonalNumberTheorem"
BRANCH = "main"
GH_BASE = f"https://github.com/{GITHUB_REPO}/blob/{BRANCH}"

DECL_RE = re.compile(
    r"^(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|inductive|structure|class|opaque|axiom)\s+"
    r"(\w+)"
)
SKIP_DIRS = {".lake", "docbuild", "blueprint", ".git"}


def _build_decl_map(repo_root: Path) -> dict:
    decl_map: dict = {}
    for lean_file in repo_root.rglob("*.lean"):
        if any(part in SKIP_DIRS for part in lean_file.parts):
            continue
        rel = lean_file.relative_to(repo_root)
        try:
            with lean_file.open() as f:
                for lineno, line in enumerate(f, start=1):
                    m = DECL_RE.match(line)
                    if m and m.group(1) not in decl_map:
                        decl_map[m.group(1)] = (str(rel), lineno)
        except OSError:
            pass
    return decl_map


def ProcessOptions(options, document):
    def patch_lean_urls():
        # document.userdata['working-dir'] is the absolute path to blueprint/src/
        working_dir = Path(document.userdata.get('working-dir', '.'))
        repo_root = working_dir.parent.parent
        decl_map = _build_decl_map(repo_root)
        if not decl_map:
            return

        for graph in document.userdata.get('dep_graph', {}).get('graphs', {}).values():
            for node in graph.nodes:
                new_urls = []
                for decl, old_url in node.userdata.get('lean_urls', []):
                    # Try full qualified name, then last component (namespace-stripped)
                    short = decl.rsplit('.', 1)[-1]
                    if decl in decl_map:
                        f, ln = decl_map[decl]
                        new_urls.append((decl, f"{GH_BASE}/{f}#L{ln}"))
                    elif short in decl_map:
                        f, ln = decl_map[short]
                        new_urls.append((decl, f"{GH_BASE}/{f}#L{ln}"))
                    else:
                        new_urls.append((decl, old_url))
                node.userdata['lean_urls'] = new_urls

    document.addPostParseCallbacks(160, patch_lean_urls)
