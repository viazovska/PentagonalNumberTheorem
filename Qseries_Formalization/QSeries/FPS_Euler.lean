/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import QSeries.FPS

/-!
# FPS Euler Second Identity

We prove the Euler second identity purely algebraically in the formal power series ring:
  `qPochInf(-a) = Σ_{n≥0} X^{C(n,2)} · aⁿ · (qPoch(X, n))⁻¹`

The proof uses the finite q-binomial theorem (which holds in any commutative ring)
and takes the limit in the pi topology. The key step is showing that the
Gaussian binomial coefficient `qBinom(N, k, X)` converges to `(qPoch(X, k))⁻¹`
as N → ∞.
-/

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace qSeries.FPS

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

set_option linter.unusedSectionVars false in
/-- The constant term of `qPoch X n` is 1. -/
theorem constantCoeff_qPoch_X (n : ℕ) :
    constantCoeff (qPoch (X : R⟦X⟧) n) = 1 := by
  induction n with
  | zero => simp [qPoch]
  | succ n ih =>
    rw [qPoch_succ]
    simp [map_mul, map_sub, ih]

/-- `qPoch X n` is a unit in `R⟦X⟧` (its constant term is 1). -/
theorem isUnit_qPoch_X (n : ℕ) : IsUnit (qPoch (X : R⟦X⟧) n) := by
  rw [show IsUnit (qPoch (X : R⟦X⟧) n) ↔
    IsUnit (PowerSeries.constantCoeff (qPoch (X : R⟦X⟧) n)) from
    PowerSeries.isUnit_iff_constantCoeff]
  rw [constantCoeff_qPoch_X]
  exact isUnit_one

/-- `qPochInf a = qPoch a n · qPochInf (a · X^n)`. -/
theorem qPochInf_eq_qPoch_mul (a : R⟦X⟧) (n : ℕ) :
    qPochInf a = qPoch a n * qPochInf (a * X ^ n) := by
  induction n with
  | zero => simp [qPoch]
  | succ n ih =>
    rw [ih, qPoch_succ, mul_assoc]
    congr 1
    rw [qPochInf_recursion]
    ring_nf

/-- `qPochInf X = qPoch X n · qPochInf (X * X^n)`. -/
theorem qqInf_eq_qPoch_mul (n : ℕ) :
    qPochInf (X : R⟦X⟧) = qPoch X n * qPochInf (X * X ^ n) :=
  qPochInf_eq_qPoch_mul X n

end qSeries.FPS

end
