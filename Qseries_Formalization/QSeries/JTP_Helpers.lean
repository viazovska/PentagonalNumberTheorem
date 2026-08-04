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
  | zero => simpa using hf
  | succ n ih =>
    have hne : q ^ n * z₀ ≠ 0 := mul_ne_zero (pow_ne_zero _ hq') hz₀
    have hlt : ‖q ^ n * z₀‖ < 1 := by
      rw [norm_mul, norm_pow]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_left (norm_nonneg z₀) (pow_le_one₀ (norm_nonneg q) hq.le)) hz₀_norm
    rw [pow_succ', mul_assoc, jacobiProd_fe hq hq' hne, jacobiBilateral_fe hq hq' hlt hne, ih]

/-- Extends the Jacobi triple product identity from the annulus $\|q\| < \|z\| < 1$ to the
full punctured disk $0 < \|z\| < 1$, using forward propagation of the functional equation. -/
theorem jtp_annulus_to_disk {q : ℂ} (hq : ‖q‖ < 1)
    (h_annulus : ∀ z : ℂ, ‖q‖ < ‖z‖ → ‖z‖ < 1 → z ≠ 0 →
      jacobiProd q z = jacobiBilateral q z)
    {z : ℂ} (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    jacobiProd q z = jacobiBilateral q z := by
  by_cases hzq : ‖q‖ < ‖z‖
  · exact h_annulus z hzq hz hz'
  · exact jacobiTripleProduct hq hz hz'

end

end qSeries
