/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import Mathlib

/-!
# q-Pochhammer symbols as formal power series

This file reformulates the q-Pochhammer symbols and the Jacobi triple product
identity in the ring of formal power series `A⟦q⟧`, where `A = ℂ[z, z⁻¹]`
is the ring of Laurent polynomials.

## Key idea

The variable `q` is the formal power series indeterminate `X`, while `z` lives in
the coefficient ring `A = LaurentPolynomial ℂ`. The q-Pochhammer symbol
`(a; q)_∞ = ∏_{k ≥ 0} (1 - a qᵏ)` is a well-defined element of `A⟦X⟧`
because the factors converge to `1` in the `X`-adic (pi) topology — no analytic
convergence hypotheses are needed.

## Main definitions

* `qSeries.FPS.qPoch`    — Finite q-Pochhammer `(a; X)_n` in `R⟦X⟧`.
* `qSeries.FPS.qPochInf` — Infinite q-Pochhammer `(a; X)_∞` in `R⟦X⟧` (via `tprod`).

## Main results

* `qSeries.FPS.multipliable_qPoch` — The infinite product is multipliable.
* `qSeries.FPS.qPochInf_recursion`  — `(a; X)_∞ = (1 - a) · (aX; X)_∞`.
* `qSeries.FPS.qPochInf_eq_mk`     — Coefficient-wise characterisation.
* `qSeries.FPS.jacobiTripleProduct_fps` — The Jacobi triple product in `A⟦X⟧`
  (proved in `QSeries.FPS_Algebra`).
-/

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace qSeries.FPS

section Finite

variable {R : Type*} [CommRing R]

/-- **Finite q-Pochhammer symbol** in `R⟦X⟧`.
`(a; X)_n = ∏_{k=0}^{n-1} (1 - a · X^k)` where `a ∈ R⟦X⟧`. -/
def qPoch (a : R⟦X⟧) (n : ℕ) : R⟦X⟧ :=
  ∏ k ∈ range n, (1 - a * X ^ k)

/-- The empty finite q-Pochhammer product `(a; X)_0 = 1`. -/
@[simp]
theorem qPoch_zero (a : R⟦X⟧) : qPoch a 0 = 1 := by
  simp [qPoch]

/-- The recurrence `(a; X)_{n+1} = (a; X)_n * (1 - a X^n)`. -/
theorem qPoch_succ (a : R⟦X⟧) (n : ℕ) :
    qPoch a (n + 1) = qPoch a n * (1 - a * X ^ n) := by
  simp [qPoch, prod_range_succ]

/-- The shift identity `(a; X)_{n+1} = (1 - a) * (aX; X)_n`. -/
theorem qPoch_eq_mul_qPoch_shift (a : R⟦X⟧) (n : ℕ) :
    qPoch a (n + 1) = (1 - a) * qPoch (a * X) n := by
  induction n with
  | zero => simp [qPoch]
  | succ n ih => rw [qPoch_succ, ih, qPoch_succ]; ring

end Finite

section Stabilisation

variable {R : Type*} [CommRing R]

/-- For `d < n`, the `d`-th coefficient of `(a; X)_{n+1}` equals that of `(a; X)_n`. -/
theorem coeff_qPoch_stable (a : R⟦X⟧) {d n : ℕ} (hdn : d < n) :
    coeff d (qPoch a (n + 1)) = coeff d (qPoch a n) := by
  rw [qPoch_succ, mul_sub, mul_one, map_sub, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', if_neg hdn.not_ge, sub_zero]

/-- For `N ≥ M > d`, the `d`-th coefficient of `(a; X)_N` equals that of `(a; X)_M`. -/
theorem coeff_qPoch_eq_of_ge (a : R⟦X⟧) {d M N : ℕ}
    (hM : d < M) (hN : M ≤ N) :
    coeff d (qPoch a N) = coeff d (qPoch a M) := by
  induction hN with
  | refl => rfl
  | step hN ih =>
      convert coeff_qPoch_stable a (lt_of_lt_of_le hM hN) using 1
      exact ih.symm

end Stabilisation

section Infinite

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

omit [DiscreteTopology R] in
/-- The infinite product `∏_{k ≥ 0} (1 - a X^k)` is multipliable in `R⟦X⟧`. -/
theorem multipliable_qPoch (a : R⟦X⟧) :
    Multipliable (fun k : ℕ => 1 - a * X ^ k) := by
  have hord : ∀ k : ℕ, (k : ℕ∞) ≤ (-(a * X ^ k) : R⟦X⟧).order := fun k =>
    PowerSeries.le_order _ _ fun i hi => by
      have hik : i < k := by exact_mod_cast hi
      rw [map_neg, PowerSeries.coeff_mul_X_pow', if_neg hik.not_ge, neg_zero]
  simp only [sub_eq_add_neg]
  refine WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top R
    (ENat.tendsto_nhds_top_iff_natCast_lt.2 fun n => Filter.eventually_atTop.2 ⟨n + 1, ?_⟩)
  exact fun k hk => lt_of_lt_of_le (by exact_mod_cast hk) (hord k)

/-- **Infinite q-Pochhammer symbol** `(a; X)_∞ = ∏_{k ≥ 0} (1 - a · X^k)`.
Well-defined in `R⟦X⟧` with the pi topology. -/
def qPochInf (a : R⟦X⟧) : R⟦X⟧ :=
  ∏' k : ℕ, (1 - a * X ^ k)

/-- The `d`-th coefficient of `(a; X)_∞` equals the `d`-th coefficient of `(a; X)_{d+1}`. -/
theorem coeff_qPochInf (a : R⟦X⟧) (d : ℕ) :
    coeff d (qPochInf a) = coeff d (qPoch a (d + 1)) := by
  have h_limit : Filter.Tendsto (fun n => coeff d (qPoch a n)) Filter.atTop
      (nhds (coeff d (qPochInf a))) :=
    ((WithPiTopology.continuous_coeff R d).tendsto _).comp
      (multipliable_qPoch a).hasProd.tendsto_prod_nat
  refine tendsto_nhds_unique h_limit (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact (coeff_qPoch_eq_of_ge a (Nat.lt_succ_self _) hn).symm

/-- **Coefficient-wise definition.** -/
theorem qPochInf_eq_mk (a : R⟦X⟧) :
    qPochInf a = mk fun d => coeff d (qPoch a (d + 1)) := by
  ext d; rw [coeff_mk, coeff_qPochInf]

/-- If the constant coefficient of `a` is zero, then that of `(a; X)_∞` is `1`. -/
theorem constantCoeff_qPochInf_of_order_pos (a : R⟦X⟧) (ha : coeff 0 a = 0) :
    coeff 0 (qPochInf a) = 1 := by
  rw [coeff_qPochInf, qPoch_succ, qPoch_zero]
  simp [-coeff_zero_eq_constantCoeff, ha]

/-- The recursion `(a; X)_∞ = (1 - a) * (aX; X)_∞`. -/
theorem qPochInf_recursion (a : R⟦X⟧) :
    qPochInf a = (1 - a) * qPochInf (a * X) := by
  -- The shifted partial products converge to `(aX; X)_∞`.
  have h_shift : Filter.Tendsto (fun n => ∏ k ∈ range n, (1 - a * X ^ (k + 1))) Filter.atTop
      (nhds (qPochInf (a * X))) :=
    (multipliable_qPoch (a * X)).hasProd.tendsto_prod_nat.congr
      fun n => prod_congr rfl fun k _ => by ring
  -- The partial products of `(a; X)_∞`, reindexed, converge to `(a; X)_∞`.
  have h_all : Filter.Tendsto (fun n => ∏ k ∈ range (n + 1), (1 - a * X ^ k)) Filter.atTop
      (nhds (qPochInf a)) :=
    (multipliable_qPoch a).hasProd.tendsto_prod_nat.comp (Filter.tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique h_all ?_
  have hsplit : ∀ n : ℕ, ∏ k ∈ range (n + 1), (1 - a * X ^ k)
      = (1 - a) * ∏ k ∈ range n, (1 - a * X ^ (k + 1)) := fun n => by
    rw [prod_range_succ', pow_zero, mul_one, mul_comm]
  simp_rw [hsplit]
  exact tendsto_const_nhds.mul h_shift

/-- `(a; X)_∞` is a unit in `R⟦X⟧` whenever `1 - coeff 0 a` is a unit in `R`. -/
theorem isUnit_qPochInf (a : R⟦X⟧) (ha : IsUnit (1 - coeff 0 a : R)) :
    IsUnit (qPochInf a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
    coeff_qPochInf, qPoch_succ, qPoch_zero, one_mul, pow_zero, mul_one]
  simpa using ha

end Infinite

section JTP

local notation "A" => LaurentPolynomial ℂ

instance : TopologicalSpace A := ⊥
instance : DiscreteTopology A := ⟨rfl⟩

local notation "PS" => (PowerSeries.C : A →+* A⟦X⟧)

/-- `z = T(1)` viewed as a constant power series in `A⟦X⟧`. -/
abbrev z : A⟦X⟧ := PS (LaurentPolynomial.T 1)

/-- `z⁻¹ = T(-1)` viewed as a constant power series in `A⟦X⟧`. -/
abbrev zinv : A⟦X⟧ := PS (LaurentPolynomial.T (-1))

/-- `(q; q)_∞` in `A⟦X⟧`. -/
def qqInf : A⟦X⟧ := qPochInf X

/-- `(-z; q)_∞` in `A⟦X⟧`. -/
def negzInf : A⟦X⟧ := qPochInf (-z)

/-- `(-q/z; q)_∞` in `A⟦X⟧`. -/
def negqzInf : A⟦X⟧ := qPochInf (-X * zinv)

/-- The **Jacobi triple product** (LHS) as an element of `A⟦X⟧`. -/
def jtpProd : A⟦X⟧ := qqInf * negzInf * negqzInf

/-- The **bilateral theta series** (RHS). -/
def jtpSeries : A⟦X⟧ :=
  (∑' n : ℕ, PS (LaurentPolynomial.T (n : ℤ)) * X ^ n.choose 2) +
  (∑' m : ℕ, PS (LaurentPolynomial.T (-(↑m + 1))) * X ^ (m + 2).choose 2)

end JTP

end qSeries.FPS

end
