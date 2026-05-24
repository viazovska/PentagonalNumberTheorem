# Lean / Stainless two-layer hybrid — interface specification

This document is the **audited contract** between the two halves of the
Pentagonal Number Theorem (PNT) development. Each layer is proved in its own
trusted base; they meet only at the statements and definitions pinned here.
Nothing imports the other tool's *proof* — the bridge is a human-audited (and
test-checked) **correspondence**, not a trust transfer.

```
        ┌────────────────────────────────────────────────────────────┐
        │ LAYER 2  —  Lean 4 + mathlib   (counting / cardinality)      │
        │   p_e(n) − p_o(n) = pentagonal coefficient                   │
        │   via |𝒫_α| = |𝒫_β| (bijection) + parity swap + special set  │
        │   trusted base: Lean kernel                                  │
        └───────────────▲──────────────────────────────────────────────┘
                        │  shared interface theorem  (§2)
        ┌───────────────┴──────────────────────────────────────────────┐
        │ LAYER 1  —  Stainless (Scala)  (the involution as a program)  │
        │   Franklin's map is a sum-preserving, parity-swapping         │
        │   involution whose fixed points are exactly 𝒫_special        │
        │   trusted base: Stainless encoding + Z3/cvc5                  │
        └────────────────────────────────────────────────────────────┘
                        │  definition correspondence  (§3)
                 audited by  agreement_check.py  (§4)
```

## 1. Layer responsibilities

**Layer 1 (Stainless — `FranklinInvolution.scala`).** The involution *as an
executable algorithm*. Stainless is good here: automatic arithmetic, case
analysis, termination, and modular contracts; and the code actually runs.
It owns:
- the partition data structure and the α/β/special **criteria** (decidable);
- **disjointness** + **trichotomy** of the three classes — *machine-checked valid*;
- α/β **operations**, with the per-operation contracts in §2;
- **closure** and **sum-preservation** of `franklinInvolution` — proved
  *modularly* from the op contracts (valid).

**Layer 2 (Lean + mathlib — `Aristotle/`, `PentagonalNumberTheorem/`).** The
*counting* conclusion, which Stainless cannot even state (no cardinality of a
set of partitions; `Set` in SMT is not foldable — see `README.md`). It owns:
- |𝒫_α(n)| = |𝒫_β(n)| from α being a bijection 𝒫_α → 𝒫_β;
- the even/odd reshuffle from the parity swap;
- 𝒫_special(n) being empty (non-pentagonal) or a single staircase set;
- ⇒ `p_e(n) − p_o(n) = (−1)^k` at pentagonal n, else 0.

## 2. The shared interface theorem

Everything Layer 2 needs from Layer 1 is the following statement about
`F = franklinInvolution` on `𝒫(n)` (distinct positive parts summing to `n`):

> **F is a sign-reversing involution.** For every `S ∈ 𝒫(n)`:
> 1. `F(S) ∈ 𝒫(n)`                              (closure — Stainless: `franklinClosed`, valid)
> 2. `sum(F(S)) = sum(S) = n`                    (Stainless: `franklinPreservesSum`, valid)
> 3. `F(F(S)) = S`                               (involution — Stainless: `franklinIsInvolution`, *open*)
> 4. `F(S) = S  ⟺  S ∈ 𝒫_special(n)`            (fixed points = special)
> 5. `S ∉ 𝒫_special(n) ⇒ |F(S)| ≢ |S| (mod 2)`  (parity swap)

This is exactly the hypothesis of the standard **sign-reversing-involution
counting lemma**, from which Layer 2 derives `p_e − p_o` = (signed count over the
fixed-point set) = the pentagonal coefficient. Items (1),(2) are verified in
Stainless today; (3),(4),(5) are the residual obligations (§5).

## 3. Definition correspondence  (Lean `Finset`  ↔  Stainless sorted `List`)

The bridge is sound only if the two layers denote the **same** objects. The
representations differ deliberately (see `README.md`):

| Notion            | Lean (`Aristotle/Defs.lean`, `Finset ℕ`) | Stainless (`FranklinInvolution.scala`, sorted `List[BigInt]`) |
|-------------------|------------------------------------------|----------------------------------------------------------------|
| partition of `n`  | `DP n`                                   | `isPartition` + `sum p == n`                                   |
| base / max        | `partBase` / `partMax`                   | `base` (head) / `maxOf`                                        |
| slope / slope set | `partSlope` / `partSlopeSet`             | `slope` (`runDownFrom`) / `inSlopeSet`                         |
| classes           | `DPalpha` / `DPbeta` / `DPspecial`       | `isAlpha` / `isBeta` / `isSpecial`                             |
| operations        | `alphaOp` / `betaOp`                     | `alphaOp` / `betaOp`                                           |

## 4. The residual Stainless VCs are already proven theorems in Lean

The obligations Stainless cannot discharge (the inductive/structural facts of §2
items 3–5) are **exactly** the ones the Lean development already proves with
`Finset`/cardinality machinery. Each open Stainless VC corresponds 1:1 to a
named, machine-checked Lean theorem:

| Open Stainless VC (contract)            | Proven Lean theorem                  | Location                |
|-----------------------------------------|--------------------------------------|-------------------------|
| `mGe2b` : `m ≥ 2b` on 𝒫_α               | `DPalpha_max_ge_2base`               | `Aristotle/Helpers.lean:86` |
| `alphaOp` post: `α(S) ∈ 𝒫_β` (Lem. 16)  | `alphaOp_mem_DPbeta`                 | `Aristotle/Lemmas.lean:373` |
| `betaOp` post: `β(S) ∈ 𝒫_α` (Lem. 17)   | `betaOp_mem_DPalpha`                 | `Aristotle/Lemmas.lean:398` |
| `franklinIsInvolution`, α-branch (L. 18)| `betaOp_alphaOp` : `β(α(S)) = S`     | `Aristotle/Lemmas.lean:458` |
| `franklinIsInvolution`, β-branch (L. 19)| `alphaOp_betaOp` : `α(β(S)) = S`     | `Aristotle/Lemmas.lean:474` |

And Lean carries the development past Layer 1 entirely — `DPalpha_card_eq_DPbeta_card`,
the parity-class lemmas, and `pe_minus_po_pent_minus/plus` (the §1 Layer-2 goal).

**Verification status (checked, not asserted):** `lake build Aristotle.Helpers
Aristotle.Lemmas` completes — *8271 jobs, exit 0, no `sorry`* — so these are
kernel-checked. (The whole `Aristotle/` namespace is `sorry`-free; the only
`sorry` in the repo is in the unrelated `Aristotle/FormalPowerSeries.lean`.)

## 5. Where the boundary actually sits (per-lemma split)

The split need not be at the big theorem boundary — it can be at the level of
individual residual VCs, which is the most economical version. Stainless already
**assumes a lemma's contract at every call site whether or not it proved the
lemma** (that is how `franklinClosed` was proved from still-`unknown` op
contracts). So the workflow is:

1. Stainless discharges everything it can
   (currently **83/86** in `FranklinInvolution.scala`; **106/107** in
   `AlphaSumProof.scala`).
2. The residual obligations stay as stated contracts — Stainless reports
   `unknown`, but callers still assume them, so the Stainless development goes
   through *modulo* this short list:
   - `alphaOp` / `betaOp` postconditions  (∈ 𝒫_β / 𝒫_α)  — Lemmas 16–17;
   - `mGe2b` (`m ≥ 2b`)                                   — the key structural fact;
   - `franklinIsInvolution` (`F∘F = id`)                  — Lemmas 18–19.
3. Those same statements are *already* proved in **Lean** against the §3
   definitions (§4), where mathlib's `Finset`/cardinality lemmas make them
   tractable — and in this project they are done, not aspirational.
4. Because Lean's kernel is a *stronger* oracle than the SMT solvers Stainless
   already trusts, routing a VC to Lean **does not weaken** Stainless's
   guarantees — unlike the reverse direction (importing a Stainless result into
   Lean as an `axiom`, which would weaken Lean's kernel guarantee).

This is the **Why3 model** (dispatch residual VCs to an interactive prover —
Why3↔Coq does exactly this), instantiated for Stainless↔Lean. Note Lean is *not*
an automatic oracle: it did not auto-discharge `mGe2b`; that induction was
written by hand (`DPalpha_max_ge_2base`) — just in the system where it is
feasible to write.

## 6. Trust boundary, stated honestly

- **Layer 2 facts and all §4 residual VCs** are Lean-kernel-checked (build-verified).
- **Layer 1 facts** marked *valid* are trusted up to {Stainless encoding, Z3/cvc5}.
- **The remaining seam is the representation correspondence** of §3: that the Lean
  functions over `Finset ℕ` and the Stainless functions over sorted `List[BigInt]`
  denote the same maps. This is **not** discharged by proof or by test here — it is
  audited by reading the two definitions side by side (§3). It is the inherent
  cross-system gap: closing it formally requires a machine-checked
  `Finset`↔sorted-`List` refinement (or a Stainless-IR → Lean embedding), which is
  a separate, research-grade artifact.
- No step imports one prover's *proof* into the other's trusted base; each layer
  is proved in its own kernel/solver, and only statements meet at §2.
