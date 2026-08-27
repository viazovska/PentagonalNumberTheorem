# Issue text — "Propose a repo" path (recommended)

Open at <https://github.com/Vilin97/lean-pool/issues>. This is the lower-effort of the two paths:
a maintainer imports the repository. Title and body below.

---

**Title:** Propose: Euler's pentagonal number theorem (two independent proofs) + Jacobi triple product

**Body:**

Repository: <https://github.com/viazovska/PentagonalNumberTheorem>
Licence: Apache-2.0 · Toolchain: `leanprover/lean4:v4.30.0-rc1` · Mathlib: tracked at `master`

Two independent formalizations of Euler's pentagonal number theorem that share no lemmas:

- **Franklin's involution** — the sign-reversing involution on partitions into distinct parts,
  giving `[qⁿ] ∏_{k=1}^{n}(1 - qᵏ) = p_e(n) - p_o(n)`, equal to `(-1)^k` at generalized pentagonal
  `n = k(3k-1)/2` and `0` otherwise. Built on Mathlib's `Nat.Partition.genFun`.
- **q-series / Jacobi triple product** — q-Pochhammer symbols, the Gaussian binomial coefficient,
  Euler's two identities, the Cauchy identity, and the Jacobi triple product proved both as a
  formal power series identity over an arbitrary commutative ring and analytically over `ℂ` for
  `‖q‖ < 1`, then specialized to the pentagonal number theorem for the infinite product.

**Why it may fit the pool.** Mathlib currently has no q-Pochhammer symbol, no Gaussian binomial
coefficient, no Jacobi triple product and no pentagonal number theorem. It does have
`Nat.Partition.genFun`, whose module docstring lists "generating function for the partition
function p(n) (TODO: prove this)" — which this project's `coeff_pGenFun_eq_p_count` effectively
does. So the q-series half is a clean addition and the combinatorial half already docks onto
existing Mathlib API.

**Gates.** 4582 LOC of own Lean across 19 files; 0 `sorry`; axioms limited to `propext`,
`Classical.choice`, `Quot.sound`; no `unsafe`/`partial`; Apache-2.0; Apache header on 19/19 files;
largest file 716 lines; `lake build --wfail` green (Mathlib's standard linter set is enabled in
`lakefile.toml` and enforced by `--wfail` in CI).

**Provenance: `mix`.** Aristotle (Harmonic) contributed to the mathematical argument and the
Franklin-route development; Claude assisted with Lean proof development and CI. The human authors
set the definitions and proof architecture and reviewed all statements against the source
manuscript.

**Extras.** Every formalized declaration is tied to a blueprint entry with a prose statement and
proof sketch, with `leanblueprint checkdecls` enforcing in CI that every `\lean{}` annotation
names a real declaration. 220/220 public declarations carry docstrings. Blueprint, dependency
graph and doc-gen4 API docs: <https://viazovska.github.io/PentagonalNumberTheorem/>

A single entry module `PentagonalNumberTheorem.lean` imports both halves, if that helps the
import.

Happy to open a content PR under `LeanPool/` instead if you'd prefer — a project card is drafted
and ready.
