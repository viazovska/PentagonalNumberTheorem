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
  induction' n with n ih
  · simp +decide [ qPoch ]
  · convert congr_arg ( fun x => x * ( 1 - a * X ^ ( n + 1 ) ) ) ih using 1 <;> push_cast [ qPoch_succ ] <;> ring!

end Finite

section Stabilisation

variable {R : Type*} [CommRing R]

/-- For `d < n`, the `d`-th coefficient of `(a; X)_{n+1}` equals that of `(a; X)_n`. -/
theorem coeff_qPoch_stable (a : R⟦X⟧) {d n : ℕ} (hdn : d < n) :
    coeff d (qPoch a (n + 1)) = coeff d (qPoch a n) := by
  rw [ qPoch_succ, PowerSeries.coeff_mul ]
  rw [ Finset.sum_eq_single ( d, 0 ) ] <;> simp_all +decide [ PowerSeries.coeff_mul ]
  · cases n <;> aesop
  · intro i j hij h; split_ifs <;> simp_all +decide [ PowerSeries.coeff_X_pow ] 
    rw [ Finset.sum_eq_zero ] <;> simp_all +decide
    intros; omega

/-- For `N ≥ M > d`, the `d`-th coefficient of `(a; X)_N` equals that of `(a; X)_M`. -/
theorem coeff_qPoch_eq_of_ge (a : R⟦X⟧) {d M N : ℕ}
    (hM : d < M) (hN : M ≤ N) :
    coeff d (qPoch a N) = coeff d (qPoch a M) := by
  induction' hN with N hN ih
  · rfl
  · convert coeff_qPoch_stable a (lt_of_lt_of_le hM hN) using 1
    exact ih.symm

end Stabilisation

section Infinite

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- The infinite product `∏_{k ≥ 0} (1 - a X^k)` is multipliable in `R⟦X⟧`. -/
theorem multipliable_qPoch (a : R⟦X⟧) :
    Multipliable (fun k : ℕ => 1 - a * X ^ k) := by
  set f : ℕ → PowerSeries R := fun k => -(a * X ^ k)
  have h_multipliable : Multipliable (fun k => 1 + f k) := by
    apply MvPowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    have h_order : ∀ k, MvPowerSeries.order (f k) ≥ k := by
      intro k
      have h_order_f : ∀ m < k, (PowerSeries.coeff m (f k)) = 0 := by
        simp +zetaDelta at *
        simp +decide [ PowerSeries.coeff_mul, PowerSeries.coeff_X_pow ]
        exact fun m hm => Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Finset.mem_antidiagonal.mp hx ] )
      simp_all +decide [ MvPowerSeries.order ]
      simp +decide [ MvPowerSeries.weightedOrder ]
      split_ifs <;> simp_all +decide
      intro m hm x hx; contrapose! hx; simp_all +decide [ Finsupp.weight ] 
      convert h_order_f m hm using 1
      rw [ show x = Finsupp.single () m from ?_ ]
      · convert rfl
      · simp_all +decide [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ]
        ext; simp [hx]
    rw [ ENat.tendsto_nhds_top_iff_natCast_lt ]
    exact fun n => Filter.eventually_atTop.2 ⟨ n + 1, fun k hk => lt_of_lt_of_le ( Nat.cast_lt.2 hk ) ( h_order k ) ⟩
  convert h_multipliable using 1
  exact funext fun k => by rw [ sub_eq_add_neg ] 

/-- **Infinite q-Pochhammer symbol** `(a; X)_∞ = ∏_{k ≥ 0} (1 - a · X^k)`.
Well-defined in `R⟦X⟧` with the pi topology. -/
def qPochInf (a : R⟦X⟧) : R⟦X⟧ :=
  ∏' k : ℕ, (1 - a * X ^ k)

/-- The `d`-th coefficient of `(a; X)_∞` equals the `d`-th coefficient of `(a; X)_{d+1}`. -/
theorem coeff_qPochInf (a : R⟦X⟧) (d : ℕ) :
    coeff d (qPochInf a) = coeff d (qPoch a (d + 1)) := by
  have h_limit : Filter.Tendsto (fun n => coeff d (qPoch a n)) Filter.atTop (nhds (coeff d (qPochInf a))) := by
    have := multipliable_qPoch a
    convert Filter.Tendsto.comp ( continuous_iff_continuousAt.mp
      (WithPiTopology.continuous_coeff R d) _ ) this.hasProd.tendsto_prod_nat
  exact tendsto_nhds_unique h_limit ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop ( d + 1 ) ] with n hn; rw [ coeff_qPoch_eq_of_ge a ( Nat.lt_succ_self _ ) hn ] ) )

/-- **Coefficient-wise definition.** -/
theorem qPochInf_eq_mk (a : R⟦X⟧) :
    qPochInf a = mk fun d => coeff d (qPoch a (d + 1)) := by
  ext d; rw [coeff_mk, coeff_qPochInf]

/-- If the constant coefficient of `a` is zero, then the constant coefficient of `(a; X)_∞` is 1. -/
theorem constantCoeff_qPochInf_of_order_pos (a : R⟦X⟧) (ha : coeff 0 a = 0) :
    coeff 0 (qPochInf a) = 1 := by
  rw [coeff_qPochInf, qPoch_succ, qPoch_zero]
  simp [pow_zero, mul_one, - coeff_zero_eq_constantCoeff, ha]

/-- The recursion `(a; X)_∞ = (1 - a) * (aX; X)_∞`. -/
theorem qPochInf_recursion (a : R⟦X⟧) :
    qPochInf a = (1 - a) * qPochInf (a * X) := by
  have h_def : qPochInf a = ∏' k, (1 - a * X ^ k) := rfl
  have h_extract : ∏' k, (1 - a * X ^ k) = (1 - a) * ∏' k, (1 - a * X ^ (k + 1)) := by
    by_cases h : Multipliable ( fun k : ℕ => 1 - a * X ^ k )
    · convert h.hasProd.tprod_eq using 1
      have := h.hasProd
      have := this.tendsto_prod_nat
      have h_shift : Filter.Tendsto (fun n => (1 - a) * ∏ i ∈ Finset.range n, (1 - a * X ^ (i + 1))) Filter.atTop (nhds ((1 - a) * ∏' k, (1 - a * X ^ (k + 1)))) := by
        refine' Filter.Tendsto.mul tendsto_const_nhds _
        convert multipliable_qPoch ( a * X ) |> Multipliable.hasProd |> HasProd.tendsto_prod_nat using 1
        · exact funext fun n => Finset.prod_congr rfl fun _ _ => by ring
        · simp +decide only [pow_succ', mul_assoc]
      convert tendsto_nhds_unique h_shift _
      convert this.comp ( Filter.tendsto_add_atTop_nat 1 ) using 2 ; simp +decide [ Finset.prod_range_succ' ]
      ring
    · exact False.elim ( h <| multipliable_qPoch a )
  rw [ h_def, h_extract, show qPochInf ( a * X ) = ∏' k : ℕ, ( 1 - a * X ^ ( k + 1 ) ) from ?_ ]
  exact tprod_congr fun k => by ring

/-- `(a; X)_∞` is a unit in `R⟦X⟧` whenever `1 - coeff 0 a` is a unit in `R`. -/
theorem isUnit_qPochInf (a : R⟦X⟧) (ha : IsUnit (1 - coeff 0 a : R)) :
    IsUnit (qPochInf a) := by
  rw [ ← isUnit_pow_iff ]
  swap
  exact Nat.one_ne_zero
  convert ha using 1
  rw [ ← isUnit_pow_iff ] ; norm_num [ PowerSeries.isUnit_iff_constantCoeff ]
  rw [ show constantCoeff ( qPochInf a ) = 1 - constantCoeff a from ?_ ]
  rw [ pow_one ]
  · convert coeff_qPochInf a 0 using 1
    · exact (coeff_zero_eq_constantCoeff_apply (qPochInf a)).symm
    · simp +decide [ qPoch ]
  · aesop

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
