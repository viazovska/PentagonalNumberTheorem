# Franklin's Involution in Stainless

A Scala formalization of Franklin's involution — the combinatorial core of
Euler's Pentagonal Number Theorem — written for **Stainless**, Viktor Kuncak's
(EPFL LARA) verification system for pure Scala.

It is a direct port of the Lean 4 development in this repo:

| Concept                         | Lean (`Aristotle/Defs.lean`) | Scala (`FranklinInvolution.scala`) |
|---------------------------------|------------------------------|------------------------------------|
| Partition of `n`, distinct parts| `DP n` (`Finset ℕ`)          | strictly-sorted `List[BigInt]` + `isPartition` |
| base / max / slope / slope set  | `partBase` … `partSlopeSet`  | `base`, `maxOf`, `slope`, `inSlopeSet` |
| classes 𝒫_α, 𝒫_β, 𝒫_special     | `DPalpha`, `DPbeta`, `DPspecial` | `isAlpha`, `isBeta`, `isSpecial` |
| operations α, β                 | `alphaOp`, `betaOp`          | `alphaOp`, `betaOp`                |
| Franklin's map                  | (Lemmas 16–19)               | `franklinInvolution`               |

## Why a sorted list, not a `Set`

Lean uses `Finset ℕ`. Stainless's `Set` is an uninterpreted SMT set — you cannot
fold a `sum` over it nor read off `min`/`max`. A **strictly increasing
`List[BigInt]`** gives distinctness (strict sort), `min = head`, `max = last`,
and a verifiable recursive `sum`, while keeping `BigInt` unbounded arithmetic
matching Lean's `ℕ`.

## Running

Stainless is not bundled in this repo. Install it (see
<https://stainless.epfl.ch>), then:

```bash
stainless ScalaEPT/FranklinInvolution.scala
```

or add the `sbt-stainless` plugin to an sbt project.

## Proof obligations (the `.holds` functions)

These are what Stainless tries to prove via its SMT back-end:

- `alphaBetaDisjoint`, `classTrichotomy` — the α/β/special partition (Lemmas in
  `content_v2.tex`); these are propositional/arithmetic and the most likely to
  discharge automatically.
- `franklinPreservesSum`, `franklinClosed` — α and β are sum-preserving partition
  rewrites.
- `alphaLandsInBeta`, `betaLandsInAlpha` — Lemmas 16–17 (`alphaOp_mem_DPbeta`,
  `betaOp_mem_DPalpha`).
- `franklinIsInvolution` — the central theorem `F ∘ F = id` (Lemmas 18–19).

### Actual results

Verified with `stainless 0.9.9.3` (Scala 3 / dotty standalone, Z3 back-end,
`--timeout=30`) on an arm64 JDK 21:

```
total: 86   valid: 83   invalid: 0   unknown: 3
```

The membership criteria for α and β are stated as `ensuring` postconditions
directly on `alphaOp` / `betaOp` — i.e. "on a 𝒫_α-input, α returns a valid
partition in 𝒫_β with the same sum" (Lemma 16) and dually for β (Lemma 17).
These are *proof obligations* (Stainless proves them for all valid inputs), not
runtime checks.

- **83 valid** — all structural and arithmetic VCs, including the full α/β/special
  **disjointness** (`alphaBetaDisjoint`) and **trichotomy** (`classTrichotomy`),
  every termination measure, sortedness/positivity-preservation of
  `insertSorted`/`erase`, and — crucially — `franklinClosed` and
  `franklinPreservesSum`. The latter two are proved **modularly**: when verifying
  `franklinInvolution`, Stainless *assumes* the `ensuring` contracts of `alphaOp`/
  `betaOp` at the call sites, so closure and sum-preservation fall out without
  re-deriving what α/β do.
- **0 invalid** — an earlier run flagged 1 invalid VC: `slope` required only
  `!p.isEmpty`, so `runDownFrom`'s `x >= 0` precondition wasn't met (a partition
  could in principle hold negatives). Fixed by strengthening `slope`/`inSlopeSet`/
  `alphaOp`/`betaOp` to require `isPartition(p)` and giving `maxOf` the
  postcondition `allPositive(p) ==> res > 0`.
- **3 unknown (timeout)** — all the irreducible induction is isolated here:
  the `ensuring` postconditions of `alphaOp` and `betaOp` (Lemmas 16–17), and
  `franklinIsInvolution` (the central `F∘F = id`, Lemmas 18–19). SMT cannot
  crack these in 30s unaided.

### Closing the 3 timeouts

These need **supporting lemmas with `@induct`** — the same inductive content as
the Lean proofs in `Aristotle/Lemmas.lean` (e.g. that `erase` then `insertSorted`
shifts the sum by a known delta, that α raises the max to `m+1`, that `β∘α`
restores base and slope). The file is structured so each lemma can be added as
its own `.holds` function and then cited (Stainless reuses proved lemmas
automatically). Once `alphaOp`/`betaOp`'s postconditions are discharged,
`franklinIsInvolution` follows from `β∘α = id` and `α∘β = id`.
