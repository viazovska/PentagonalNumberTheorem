# lean-pool inclusion criteria — evidence

Checked against [`candidates/CRITERIA.txt`](https://github.com/Vilin97/lean-pool/blob/main/candidates/CRITERIA.txt)
and the gates in `CONTRIBUTING.md`. All figures re-measured on this branch.

## INCLUDE criteria

| Criterion | Status | Evidence |
|---|---|---|
| Domain fits mathlib / cslib / physlean | ✅ mathlib | number theory + enumerative combinatorics |
| ≥ 250 LOC of own `.lean` (not vendored) | ✅ **4582** | 19 files under `QSeries/` and `EulerPentagonalNumberTheorem_Franklin/` |
| Reads like theorems a big library could absorb | ✅ | 271 declarations; q-Pochhammer / Gaussian binomial / Euler identities / Cauchy identity / JTP form a reusable API, none of which exists in Mathlib today |

## EXCLUDE criteria — none apply

| Exclusion | Applies? |
|---|---|
| tool (tactic, automation, build util) | No — no tactics or tooling |
| educational (course, book, tutorial, game) | No |
| personal (AoC, Project Euler, learning, MWE) | No |
| translation (Lean 3→4, mathport) | No — written for Lean 4 |
| fork / mirror of mathlib etc. | No |
| empty (no theorems, abandoned) | No — 271 declarations, active |
| scaffold (excessive sorrys) | No — **0 sorrys** |

## Hard gates from CONTRIBUTING.md

| Gate | Status | Evidence |
|---|---|---|
| `sorry`-free | ✅ 0 | across all 19 project files |
| No axioms beyond `Classical.choice`/`propext`/`Quot.sound` | ✅ | `#print axioms` on all headline results |
| No `unsafe` / `partial` | ✅ 0 | grep over project sources |
| Permissive licence | ✅ Apache-2.0 | root `LICENSE`; declared in `CITATION.cff` |
| Builds warning-free | ✅ | `lake build --wfail` → 8293 jobs, 0 warnings, exit 0 |
| Clears Mathlib linters | ✅ | `weak.linter.mathlibStandardSet` enabled in `lakefile.toml` and enforced by `--wfail` |
| Latest Lean / Mathlib | ✅ | `leanprover/lean4:v4.30.0-rc1`; Mathlib tracked at `master` |
| File headers | ✅ 19/19 | Apache header on every file |
| Size limits | ✅ | largest 716 lines (`FPS_Algebra.lean`) |
| `provenance` declared | ✅ `mix` | see below |

## Provenance: `mix`

CONTRIBUTING requires one of `human` / `AI` / `mix`, describing **who wrote the Lean proofs**.
`mix` is the honest answer, and matches what `formalization.yaml` discloses for Palomar:

- **Aristotle** (Harmonic) contributed to the mathematical argument, the blueprint structure, and
  the Franklin-route development — `EulerPentagonalNumberTheorem_Franklin/README.md` carries its
  attribution.
- **Claude** assisted with Lean proof development, blueprint maintenance, and CI.
- **The human authors** set the definitions and the overall proof architecture, and reviewed all
  statements against the source manuscript.

Do not claim `human`. The pool reviews provenance explicitly and understating it is the kind of
thing that costs credibility.

## Above the bar

Two things worth leading with, since they are uncommon among pooled projects:

- **100% docstring coverage** — 220/220 public declarations documented.
- **A blueprint.** Every formalized declaration is tied to a prose statement and paragraph-level
  proof sketch; `leanblueprint checkdecls` enforces in CI that no `\lean{}` annotation names a
  declaration that does not exist. Published with doc-gen4 API docs at
  <https://viazovska.github.io/PentagonalNumberTheorem/>.

## The one thing a reviewer will probe

The repository contains **two independent proofs of the same theorem**. That is a strength for
confidence, but a curator may ask whether both belong in a shared pool. Pre-empt it: the q-series
route is the reusable library (and the part with no Mathlib overlap), while the Franklin route is
a self-contained combinatorial proof that already builds on Mathlib's `Nat.Partition.genFun` and
serves as an independent check. Submitting them as one card, under a single entry module that
imports both, presents this accurately.
