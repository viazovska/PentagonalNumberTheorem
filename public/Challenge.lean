/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import Mathlib

/-!
# Public challenge statements

Self-contained statements of this repository's results. Palomar requires the challenge module to
import only Lean core, Mathlib or Tau Ceti, so every project-specific definition is unfolded here
into plain Mathlib vocabulary.

The **primary** result is the combinatorial one, proved via Franklin's sign-reversing involution
on partitions into distinct parts. Writing `D n` for the partitions of `n` into distinct positive
parts, realised as the subsets of `{1, …, n}` summing to `n`:

* `distinctPartitions n = (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n)`
* `pe n` / `po n` = the number of such subsets of even / odd cardinality

The **accompanying extension** is the q-series route, which reaches the same theorem for the
infinite product via the Jacobi triple product:

* `QSeries.qPochhammerInf a q = ∏' k : ℕ, (1 - a * q ^ k)`
* `QSeries.jacobiProd q z     = qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q/z) q`
* `QSeries.jacobiBilateral q z = (∑' k : ℕ, z ^ k * q ^ k.choose 2)
                                   + ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2`

The proofs live in `Solution.lean`, which may import the project.
-/

namespace PentagonalNumberTheorem.Challenge

open Finset

/-! ## Primary result — Franklin's involution -/

/-- **Euler's pentagonal number theorem, Franklin form (unified integer index).**
For every `n`, either `n` is a generalized pentagonal number `k(3k-1)/2` for some `k : ℤ`, in
which case the number of partitions of `n` into an even number of distinct parts exceeds the
number with an odd number of distinct parts by exactly `(-1)^|k|`; or `n` is not of that form,
in which case the two counts are equal. -/
theorem franklin_pentagonal_number_theorem (n : ℕ) :
    (∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2 ∧
        ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 0).card : ℤ)
          - ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
              fun S => S.card % 2 = 1).card : ℤ)
          = (-1 : ℤ) ^ k.natAbs)
      ∨ ((¬ ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2) ∧
        ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 0).card : ℤ)
          - ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
              fun S => S.card % 2 = 1).card : ℤ)
          = 0) := by
  sorry

/-- **The generating-function side of the Franklin route.** The coefficient of `Xⁿ` in the
truncated product `∏_{k=1}^{n} (1 - Xᵏ)` over `ℤ⟦X⟧` is the signed count `p_e(n) - p_o(n)`.
Truncating at `n` is harmless: the factors with `k > n` are `≡ 1 mod X^{n+1}`. -/
theorem franklin_coeff_prod_eq_pe_sub_po (n : ℕ) :
    (PowerSeries.coeff n) (∏ k ∈ Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℤ))
      = ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 0).card : ℤ)
        - ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 1).card : ℤ) := by
  sorry

/-! ## Accompanying extension — the q-series / Jacobi triple product route -/

/-- **Jacobi triple product identity.** For `‖q‖ < 1`, `‖z‖ < 1` and `z ≠ 0`,
`(q;q)_∞ (-z;q)_∞ (-q/z;q)_∞` equals the bilateral theta series `∑_{k ∈ ℤ} z^k q^{k(k-1)/2}`. -/
theorem jacobiTripleProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    (∏' k : ℕ, (1 - q * q ^ k)) * (∏' k : ℕ, (1 - -z * q ^ k)) *
        (∏' k : ℕ, (1 - -q / z * q ^ k)) =
      (∑' k : ℕ, z ^ k * q ^ k.choose 2)
        + ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2 := by
  sorry

/-- **Euler's pentagonal number theorem, infinite-product form.** For `‖q‖ < 1`, the infinite
product `(q;q)_∞` equals the bilateral series `∑_{k ∈ ℤ} (-1)^k q^{ω(k)}` over the generalized
pentagonal numbers `ω(k) = k(3k-1)/2`, written as two one-sided sums. Obtained from the Jacobi
triple product by specialization. -/
theorem euler_pentagonal_number {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q * q ^ k)) =
      (∑' k : ℕ, (-1 : ℂ) ^ k * q ^ (((k : ℤ) * (3 * (k : ℤ) - 1) / 2).toNat))
        + ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) *
            q ^ ((-((k : ℤ) + 1) * (3 * -((k : ℤ) + 1) - 1) / 2).toNat) := by
  sorry

end PentagonalNumberTheorem.Challenge
