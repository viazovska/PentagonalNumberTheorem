# EulerPentagonalNumberTheorem_Franklin — Summary

Lean 4 / Mathlib formalization of Euler's Pentagonal Number Theorem via **Franklin's
sign-reversing involution**. Five files, 1230 lines, zero sorries.

The argument: partitions of `n` into distinct positive parts split into three classes
(α, β, special). Franklin's involution bijects α ↔ β, flipping parity of partition
size. For non-pentagonal `n` the special class is empty and `pe(n) = po(n)`; for
pentagonal `n` it is a single fixed point, giving `pe(n) - po(n) = ±1`.

---

## Files

### `Defs.lean` (110 lines)

Core definitions:

| Name | Description |
|---|---|
| `consecutiveTopRun S m` | Length of the consecutive run `{m, m-1, …}` at the top of `S` |
| `distinctPartitions n` | Finite sets `S ⊆ {1,…,n}` with `∑ S = n` |
| `distinctPartitionsEven / Odd n` | Even / odd cardinality subsets of `distinctPartitions n` |
| `pe n`, `po n` | Counts of even / odd distinct partitions of `n` |
| `partBase S`, `partMax S` | Smallest and largest element of `S` |
| `partSlope S` | `consecutiveTopRun S (partMax S)` — length of the top staircase |
| `partSlopeSet S` | The top staircase `{partMax S, partMax S − 1, …}` |
| `distinctPartitionsAlpha n` | α-class: `partBase S ≤ partSlope S` |
| `distinctPartitionsBeta n` | β-class: `partSlope S < partBase S` |
| `distinctPartitionsSpecial n` | Special class: `partBase S = partSlope S + 1` or `partBase S = partSlope S` at boundary |
| `smkSet k` | The staircase partition `{k, k+1, …, 2k−1}`, summing to `(3k²−k)/2` |
| `spkSet k` | The staircase partition `{k+1, k+2, …, 2k}`, summing to `(3k²+k)/2` |
| `alphaOp S` | Franklin's α-operation: moves bottom part to extend top staircase |
| `betaOp S` | Franklin's β-operation: removes top of staircase to create new bottom part |

### `Helpers.lean` (309 lines, 39 lemmas)

Auxiliary lemmas used by `Lemmas.lean`:
- Properties of `consecutiveTopRun`: membership, boundary conditions, bounds
- Basic membership and ordering facts about `distinctPartitions`, `distinctPartitionsAlpha`, `distinctPartitionsBeta`
- Key inequalities: `partMax S ≥ 2 · partBase S` for α-partitions; `partMax S ≥ 2 · partSlope S + 1` for β-partitions
- Sum, max, slope, and base computations for `alphaOp` and `betaOp`

### `Lemmas.lean` (543 lines, 25 theorems)

All main results of the formalization:

| Theorem | Statement |
|---|---|
| `DPalpha_inter_DPbeta` | α ∩ β = ∅ |
| `DPalpha_inter_DPspecial` | α ∩ special = ∅ |
| `DPbeta_inter_DPspecial` | β ∩ special = ∅ |
| `DP_eq_union` | `distinctPartitions n = α ∪ β ∪ special` |
| `SmkSet_card`, `SmkSet_sum` | `smkSet k` has cardinality `k` and sum `(3k²−k)/2` |
| `SpkSet_card`, `SpkSet_sum` | `spkSet k` has cardinality `k` and sum `(3k²+k)/2` |
| `DPspecial_empty_of_nonpent` | Special class is empty when `n` is not a generalized pentagonal number |
| `DPspecial_pent_minus` | Special class = `{smkSet k}` when `2n = 3k²−k` |
| `DPspecial_pent_plus` | Special class = `{spkSet k}` when `2n = 3k²+k` |
| `alphaOp_mem_DPbeta` | `alphaOp` maps α into β |
| `betaOp_mem_DPalpha` | `betaOp` maps β into α |
| `betaOp_alphaOp` | `betaOp ∘ alphaOp = id` on α |
| `alphaOp_betaOp` | `alphaOp ∘ betaOp = id` on β |
| `DPalpha_card_eq_DPbeta_card` | `|α| = |β|` |
| `alphaOp_card`, `betaOp_card` | `alphaOp`/`betaOp` change cardinality by ±1 |
| `DPalpha_odd_card_eq_DPbeta_even_card` | `|α_odd| = |β_even|` |
| `DPalpha_even_card_eq_DPbeta_odd_card` | `|α_even| = |β_odd|` |
| `pe_minus_po_eq_special` | `pe(n) − po(n) = |special(n)_even| − |special(n)_odd|` |
| `pe_minus_po_zero` | `pe(0) − po(0) = 1` |
| `pe_minus_po_nonpent` | `pe(n) − po(n) = 0` for non-pentagonal `n ≥ 1` |
| `pe_minus_po_pent_minus` | `pe(n) − po(n) = (−1)^k` when `2n = 3k²−k` |
| `pe_minus_po_pent_plus` | `pe(n) − po(n) = (−1)^k` when `2n = 3k²+k` |

### `FormalPowerSeries.lean` (236 lines, 11 theorems)

Bridges the combinatorial result to the formal power series identity, using Mathlib's
`PowerSeries` and `Nat.Partition` API:

| Theorem | Statement |
|---|---|
| `p_count`, `pGenFun` | Unrestricted partition count and its generating function |
| `coeff_pGenFun_eq_p_count` | Coefficients of `pGenFun` are `p_count` |
| `pGenFun_eq_prod` | `pGenFun = ∏ (1 − Xᵏ)⁻¹` |
| `coeff_prod_eq_signed_partition_sum` | Coefficient of `∏(1−Xᵏ)` at `n` equals the signed partition sum |
| `signed_partition_sum_eq_pe_sub_po` | Signed partition sum equals `pe(n) − po(n)` |
| `coeff_prod_eq_pe_sub_po` | Coefficient of `∏(1−Xᵏ)` at `n` equals `pe(n) − po(n)` |
| `coeff_prod_pentagonal_zero` | Coefficient at 0 is 1 |
| `coeff_prod_pentagonal_nonpent` | Coefficient at non-pentagonal `n` is 0 |
| `coeff_prod_pentagonal_minus` | Coefficient at `(3k²−k)/2` is `(−1)^k` |
| `coeff_prod_pentagonal_plus` | Coefficient at `(3k²+k)/2` is `(−1)^k` |
| `euler_pentagonal_number_theorem_packaged` | All cases packaged into a single statement |

### `Main.lean` (32 lines)

Imports all four modules.
