/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import QSeries.JacobiTripleProduct

/-!
# Helper lemmas for the Jacobi triple product identity
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-- If the Jacobi triple product functional equation holds at $z_0$, then it holds at every
forward iterate $q^n z_0$ for all $n : \mathbb{N}$. -/
theorem fe_propagates_forward {q : ℂ} (hq' : q ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hf : jacobiProd q z₀ = jacobiBilateral q z₀)
    (hq : ‖q‖ < 1) (hz₀_norm : ‖z₀‖ < 1) :
    ∀ n : ℕ, jacobiProd q (q ^ n * z₀) = jacobiBilateral q (q ^ n * z₀) := by
  intro n
  induction n with
  | zero => grind +splitImp
  | succ n ih =>
      simp_all +decide [ pow_succ', mul_assoc ]
      convert congr_arg ( fun x => x / ( q ^ n * z₀ ) ) ih using 1
      · convert jacobiProd_fe hq hq' ( show q ^ n * z₀ ≠ 0 from mul_ne_zero ( pow_ne_zero _ hq' ) hz₀ ) using 1
      · convert jacobiBilateral_fe hq hq' _ _ using 1
        · simpa using lt_of_le_of_lt ( mul_le_of_le_one_left ( by positivity ) ( pow_le_one₀ ( by positivity ) hq.le ) ) hz₀_norm
        · aesop

/-- Extends the Jacobi triple product identity from the annulus $\|q\| < \|z\| < 1$ to the
full punctured disk $0 < \|z\| < 1$, using forward propagation of the functional equation. -/
theorem jtp_annulus_to_disk {q : ℂ} (hq : ‖q‖ < 1)
    (h_annulus : ∀ z : ℂ, ‖q‖ < ‖z‖ → ‖z‖ < 1 → z ≠ 0 →
      jacobiProd q z = jacobiBilateral q z)
    {z : ℂ} (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    jacobiProd q z = jacobiBilateral q z := by
  by_cases hq0 : q = 0
  · subst hq0; exact h_annulus z (by simp [norm_pos_iff.mpr hz']) hz hz'
  · by_cases hzq : ‖q‖ < ‖z‖
    · exact h_annulus z hzq hz hz'
    · push Not at hzq
      grind +suggestions

end

end qSeries