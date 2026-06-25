# Pentagonal Number Theorem

A Lean 4 / Mathlib formalization of **Euler's Pentagonal Number Theorem**:

$$
\prod_{i=1}^{\infty}(1-x^i) = \sum_{k\in\mathbb{Z}}(-1)^k x^{(3k^2-k)/2}.
$$

The mathematical proof is laid out as a
[blueprint](https://viazovska.github.io/PentagonalNumberTheorem/blueprint/); the
Lean formalization fills in the leaves of the proof tree.

## Project site

- **Landing page / overview**: <https://viazovska.github.io/PentagonalNumberTheorem/>
- **Web blueprint**: <https://viazovska.github.io/PentagonalNumberTheorem/blueprint/>
- **Dependency graph**: <https://viazovska.github.io/PentagonalNumberTheorem/blueprint/dep_graph_document.html>
- **PDF blueprint**: <https://viazovska.github.io/PentagonalNumberTheorem/blueprint.pdf>
- **Lean API docs**: <https://viazovska.github.io/PentagonalNumberTheorem/docs/>

The site is built and deployed by `.github/workflows/blueprint.yml` on every push to `main`.

## Repository layout

```
PentagonalNumberTheorem/          Lean source for the formalization
├── odd_and_even_distinct_partitions.lean
└── pentagonal_number-theorem.lean

blueprint/
├── src/
│   ├── content_v2.tex            Blueprint content (main file)
│   ├── web.tex                   Master file for the web build
│   ├── print.tex                 Master file for the PDF build
│   └── macros/                   Shared / web / print-only macros
├── lean_decls                    Lean declarations referenced by the blueprint
├── post_build.py                 Rewrites doc URLs to GitHub source links
└── build_web.sh                  Convenience wrapper: web build + post_build

home_page/                        Jekyll source for the landing page
docbuild/                         doc-gen4 build configuration
.github/workflows/blueprint.yml   CI: build Lean, blueprint, deploy to Pages
```

## Building locally

### Prerequisites

- [elan](https://github.com/leanprover/elan) (the Lean toolchain manager)
- Python 3 with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint):
  `pip install leanblueprint`
- TeX Live (or equivalent) for the PDF build

### Lean code

```bash
lake exe cache get      # download Mathlib cache
lake build              # build the Lean code
```

### Blueprint

```bash
./blueprint/build_web.sh        # web blueprint + GitHub link rewrite
leanblueprint pdf               # PDF blueprint
```

Open `blueprint/web/index.html` in a browser to view the result locally.

`build_web.sh` runs `leanblueprint web` and then `post_build.py`, which rewrites
every Lean-declaration link (originally pointing at the doc-gen4 docs site) to
the matching `.lean` source file and line on GitHub. The mapping is computed
automatically from your Lean source — no manual URL maintenance needed.

## Contributing

The blueprint is the proof; Lean fills it in. To contribute a formalization:

1. Pick an unproved lemma from the
   [dependency graph](https://viazovska.github.io/PentagonalNumberTheorem/blueprint/dep_graph_document.html)
   (look for nodes whose ancestors are all proved).
2. Write the Lean statement and proof in `PentagonalNumberTheorem/`.
3. Add `\lean{your_decl_name}` to the corresponding blueprint item in
   `blueprint/src/content_v2.tex`, and add the declaration name to
   `blueprint/lean_decls`.
4. Add `\leanok` to mark the statement (or proof) as formalized.
5. Open a pull request.

## Authors

JC, PM, MV.
