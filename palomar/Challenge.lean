/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import Mathlib

/-!
# Palomar challenge statements

Self-contained statements of the two headline results of this repository. Palomar requires the
challenge module to import only Lean core, Mathlib or Tau Ceti, so every project-specific
definition is unfolded here into plain Mathlib vocabulary:

* `QSeries.qPochhammerInf a q = ∏' k : ℕ, (1 - a * q ^ k)`
* `QSeries.pentagonal k      = (k * (3 * k - 1) / 2).toNat`   (`k : ℤ`)
* `QSeries.jacobiProd q z    = qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q/z) q`
* `QSeries.jacobiBilateral q z = (∑' k : ℕ, z ^ k * q ^ k.choose 2)
                                  + ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2`

The proofs live in `Solution.lean`, which is allowed to import the project.
-/

namespace PentagonalNumberTheorem.Challenge

/-- **Euler's pentagonal number theorem.** For `‖q‖ < 1`, the infinite product `(q;q)_∞`
equals the bilateral series `∑_{k ∈ ℤ} (-1)^k q^{ω(k)}` over the generalized pentagonal
numbers `ω(k) = k(3k-1)/2`, written as two one-sided sums. -/
theorem euler_pentagonal_number {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q * q ^ k)) =
      (∑' k : ℕ, (-1 : ℂ) ^ k * q ^ (((k : ℤ) * (3 * (k : ℤ) - 1) / 2).toNat))
        + ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) *
            q ^ ((-((k : ℤ) + 1) * (3 * -((k : ℤ) + 1) - 1) / 2).toNat) := by
  sorry

/-- **Jacobi triple product identity.** For `‖q‖ < 1`, `‖z‖ < 1` and `z ≠ 0`,
`(q;q)_∞ (-z;q)_∞ (-q/z;q)_∞` equals the bilateral theta series `∑_{k ∈ ℤ} z^k q^{k(k-1)/2}`. -/
theorem jacobiTripleProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    (∏' k : ℕ, (1 - q * q ^ k)) * (∏' k : ℕ, (1 - -z * q ^ k)) *
        (∏' k : ℕ, (1 - -q / z * q ^ k)) =
      (∑' k : ℕ, z ^ k * q ^ k.choose 2)
        + ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2 := by
  sorry

end PentagonalNumberTheorem.Challenge
