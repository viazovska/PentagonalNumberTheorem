# Pentagonal Number Theorem

A Lean 4 / Mathlib formalization of **Euler's Pentagonal Number Theorem**:

$$
\prod_{i=1}^{\infty}(1-x^i) = \sum_{k\in\mathbb{Z}}(-1)^k x^{(3k^2-k)/2}.
$$

Two independent proof routes are formalized — a combinatorial proof via Franklin's
involution and an algebraic/analytic proof via the Jacobi Triple Product identity.

## Project site

- **Landing page / overview**: <https://viazovska.github.io/PentagonalNumberTheorem/>
- **Web blueprint**: <https://viazovska.github.io/PentagonalNumberTheorem/blueprint/>
- **Dependency graph**: <https://viazovska.github.io/PentagonalNumberTheorem/blueprint/dep_graph_document.html>
- **PDF blueprint**: <https://viazovska.github.io/PentagonalNumberTheorem/blueprint.pdf>
- **Lean API docs**: <https://viazovska.github.io/PentagonalNumberTheorem/docs/>

The site is built and deployed by `.github/workflows/blueprint.yml` on every push to `main`.

## Formalizations

### Franklin involution (`EulerPentagonalNumberTheorem_Franklin/`)

A combinatorial proof following Franklin's sign-reversing involution on partitions
into distinct parts. Zero sorries. Key declarations:

- `distinctPartitions n` — partitions of `n` into distinct positive parts
- `distinctPartitionsAlpha n`, `distinctPartitionsBeta n`, `distinctPartitionsSpecial n` — the three partition classes
- `pe n`, `po n` — count of even/odd-size distinct partitions of `n`
- `alphaOp`, `betaOp` — Franklin's involution operations, proved to be mutual inverses
- `DPalpha_card_eq_DPbeta_card` — the bijection between α- and β-partitions
- `pe_minus_po_nonpent` — `pe(n) - po(n) = 0` for non-pentagonal `n`
- `pe_minus_po_pent_minus`, `pe_minus_po_pent_plus` — `pe(n) - po(n) = ±1` at pentagonal `n`

### q-series / Jacobi Triple Product (`Qseries_Formalization/`)

An algebraic and analytic proof route through the Jacobi Triple Product identity.
Zero sorries. Key declarations:

- `fps_euler_second` — Euler's second identity as formal power series over any commutative ring
- `fps_key_identity` — `S_k = (q;q)_∞⁻¹` for all `k` (coefficient stabilization)
- `jacobiTripleProduct_fps` — Jacobi Triple Product as an identity in `A⟦X⟧` (FPS over Laurent polynomials ℂ[z, z⁻¹])
- `jacobiTripleProduct_analytic` — analytic JTP: `(q;q)_∞ · (-z;q)_∞ · (-q/z;q)_∞ = ∑_{k∈ℤ} zᵏ q^{k(k-1)/2}` for all `‖q‖ < 1`, `z ≠ 0`
- `eulerPentagonalNumber` — Euler's pentagonal number theorem (corollary of JTP)

Supporting infrastructure: q-Pochhammer symbols `qPoch`, `qPochInf`; q-binomial
coefficients `qBinom`; summability and locally-uniform-convergence lemmas.

## Repository layout

```
EulerPentagonalNumberTheorem_Franklin/    Franklin involution proof
├── Defs.lean                             Partition definitions and involution operations
├── Helpers.lean                          Helper lemmas
├── Lemmas.lean                           Main theorems (Franklin bijection, pe - po formula)
├── FormalPowerSeries.lean                FPS statements (Lemmas 3, 5; Theorems 7, 25)
└── Main.lean                             Imports all components

Qseries_Formalization/                    q-series / JTP proof route
└── QSeries/
    ├── Defs.lean                         q-Pochhammer and related definitions
    ├── FiniteBinomial.lean               q-binomial (Gaussian binomial) coefficients
    ├── InfPochhammer.lean                Infinite q-Pochhammer symbol (q;q)_∞
    ├── CauchyIdentity.lean               Cauchy product diagonal coefficient identities
    ├── EulerIdentities.lean              Euler's first and second FPS identities
    ├── FPS.lean                          FPS infrastructure and pi-topology summability
    ├── FPS_Euler.lean                    FPS Euler second identity
    ├── FPS_Algebra.lean                  FPS JTP (jacobiTripleProduct_fps), Cauchy coefficients
    ├── JTP_Core.lean                     Core JTP infrastructure
    ├── JTP_KeyIdentity.lean              Key identity S_k = (q;q)_∞⁻¹
    ├── JTP_Helpers.lean                  Helper lemmas for the JTP proof
    ├── JTP_Analytic.lean                 Analytic JTP (jacobiTripleProduct_analytic)
    ├── JacobiTripleProduct.lean          Top-level JTP and pentagonal number theorem
    └── PentagonalNumber.lean             eulerPentagonalNumber

blueprint/
├── src/
│   ├── content_v2.tex                    Blueprint content (Franklin route)
│   ├── content_Jac.tex                   Blueprint content (JTP route)
│   ├── web.tex                           Master file for the web build
│   ├── print.tex                         Master file for the PDF build
│   └── macros/                           Shared / web / print-only macros
├── post_build.py                         Rewrites doc URLs to GitHub source links
└── build_web.sh                          Convenience wrapper: web build + post_build

home_page/                                Jekyll source for the landing page
.github/workflows/blueprint.yml           CI: build Lean, blueprint, deploy to Pages
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
the matching `.lean` source file and line on GitHub.

## Contributing

The blueprint is the proof; Lean fills it in. To contribute a formalization:

1. Pick an unproved lemma from the
   [dependency graph](https://viazovska.github.io/PentagonalNumberTheorem/blueprint/dep_graph_document.html)
   (look for nodes whose ancestors are all proved).
2. Write the Lean statement and proof in the appropriate source folder.
3. Add `\lean{your_decl_name}` to the corresponding blueprint item in
   `blueprint/src/content_v2.tex` or `content_Jac.tex`, and add the declaration
   name to `blueprint/lean_decls`.
4. Add `\leanok` to mark the statement (or proof) as formalized.
5. Open a pull request.

## Authors

Jonathan Conrad, Paula Mürmann, Maryna Viazovska.
