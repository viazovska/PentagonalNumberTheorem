/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import QSeries.FPS
import QSeries.FPS_Euler
import QSeries.Defs
import QSeries.FiniteBinomial

/-!
# Algebraic identities for FPS q-series

Purely algebraic proofs of the **Euler second identity** and the **key identity**
`S_k = (qPochInf X)⁻¹` in the formal power series ring `R⟦X⟧` over any
commutative ring with discrete topology. Combined with the product expansion
and Cauchy product, these identities yield the Jacobi triple product.

## Main results

* `qSeries.FPS.fps_euler_second` — FPS Euler second identity.
* `qSeries.FPS.fps_key_identity` — `S_k = (qPochInf X)⁻¹` for all `k`.
* `qSeries.FPS.cauchy_coeff_nonneg` — Cauchy diagonal coefficient for `n ≥ 0`.
* `qSeries.FPS.cauchy_coeff_neg` — Cauchy diagonal coefficient for `n < 0`.
* `qSeries.FPS.jacobiTripleProduct_fps` — FPS Jacobi Triple Product Identity.
-/

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace qSeries.FPS

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]


/-- Inverse of `qPoch X k` in `R⟦X⟧`, defined via `invOfUnit` since the
constant coefficient is `1`. -/
def qPochInv (k : ℕ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit (qPoch (X : R⟦X⟧) k) 1

/-- `qPoch X k` times its formal power series inverse equals 1. -/
@[simp]
theorem qPoch_mul_qPochInv (k : ℕ) :
    qPoch (X : R⟦X⟧) k * qPochInv (R := R) k = 1 := by
  convert MvPowerSeries.mul_invOfUnit _ _ _
  convert constantCoeff_qPoch_X k
  exacts [ inferInstance, inferInstance ]

/-- The formal power series inverse of `qPoch X k` times `qPoch X k` equals 1. -/
@[simp]
theorem qPochInv_mul_qPoch (k : ℕ) :
    qPochInv (R := R) k * qPoch (X : R⟦X⟧) k = 1 := by
  rw [ mul_comm, qPoch_mul_qPochInv ]

/-- The recursion `(1 - X^{k+1}) * qPochInv(k+1) = qPochInv(k)` for the inverse q-Pochhammer symbol. -/
theorem qPochInv_succ_mul (k : ℕ) :
    (1 - (X : R⟦X⟧) ^ (k + 1)) * qPochInv (R := R) (k + 1) = qPochInv k := by
  have h_qPoch_succ : qPoch (X : R⟦X⟧) (k + 1) = qPoch (X : R⟦X⟧) k * (1 - X ^ (k + 1)) := by
    rw [qPoch_succ]
    ring
  convert congr_arg ( fun x => qPochInv k * x * qPochInv ( k + 1 ) ) h_qPoch_succ.symm using 1 <;> ring!
  · simp +decide [ mul_assoc, qPochInv_mul_qPoch ]
  · rw [ add_comm, mul_assoc, qPoch_mul_qPochInv, mul_one ]

/-- `qPochInf X` is a unit. -/
theorem isUnit_qqInf : IsUnit (qPochInf (X : R⟦X⟧)) := by
  apply isUnit_qPochInf; simp

/-- Inverse of `qPochInf X`. -/
def qqInv : R⟦X⟧ := ↑(isUnit_qqInf (R := R)).unit⁻¹

/-- `qPochInf X` times its formal power series inverse equals 1. -/
@[simp]
theorem qqInf_mul_qqInv : qPochInf (X : R⟦X⟧) * qqInv (R := R) = 1 :=
  isUnit_qqInf.mul_val_inv

/-- The formal power series inverse of `qPochInf X` times `qPochInf X` equals 1. -/
@[simp]
theorem qqInv_mul_qqInf : qqInv (R := R) * qPochInf (X : R⟦X⟧) = 1 :=
  isUnit_qqInf.val_inv_mul

/-- `qPochInf X * qPochInv n = qPochInf (X * X^n)`: multiplying the infinite product by the `n`-th inverse Pochhammer symbol shifts the argument. -/
theorem qqInf_mul_qPochInv (n : ℕ) :
    qPochInf (X : R⟦X⟧) * qPochInv (R := R) n = qPochInf (X * X ^ n) := by
  convert congr_arg ( fun x => x * qPochInv n ) ( qPochInf_eq_qPoch_mul ( X : R⟦X⟧ ) n ) using 1
  rw [ mul_right_comm, mul_comm ]
  simp +zetaDelta at *


private lemma choose2_step (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- `C(m+k,2) + C(m,2) + m = C(k,2) + m*(m+k)`. -/
lemma choose2_add (m k : ℕ) :
    (m + k).choose 2 + m.choose 2 + m = k.choose 2 + m * (m + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 from by omega, choose2_step, choose2_step]; linarith

/-- `C(n,2) + C(n+l+1,2) + (n+l+1) = C(l+2,2) + n*(n+l+1)`. -/
lemma choose2_add' (n l : ℕ) :
    n.choose 2 + (n + (l + 1)).choose 2 + (n + (l + 1)) =
    (l + 2).choose 2 + n * (n + (l + 1)) := by
  have h := choose2_add n (l + 1)
  have h2 : (l + 2).choose 2 = (l + 1).choose 2 + (l + 1) := by
    rw [show l + 2 = (l + 1) + 1 from by omega]; exact choose2_step (l + 1)
  linarith


section Euler2

set_option maxHeartbeats 400000 in
/-- For `j + k ≤ n`, the `j`-th coefficient of `qBinom n k X` equals that of `qPochInv k`. -/
theorem coeff_qBinom_eq_qPochInv {k j n : ℕ} (hjk : j + k ≤ n) :
    PowerSeries.coeff j (qSeries.qBinom n k (X : R⟦X⟧)) =
    PowerSeries.coeff j (qPochInv (R := R) k) := by
  by_contra h
  have h_eq : qBinom n k (X : R⟦X⟧) * qPoch (X : R⟦X⟧) k * qPoch (X : R⟦X⟧) (n - k) = qPoch (X : R⟦X⟧) n := by
    convert qBinom_mul_qPochhammer_mul_qPochhammer ( X : R⟦X⟧ ) ( show k ≤ n from by omega ) using 1
  have h_rhs : qPoch (X : R⟦X⟧) n * (qPochInv (n - k) : R⟦X⟧) - 1 ∈ {f : R⟦X⟧ | ∀ j < n - k + 1, (coeff j) f = 0} := by
    have h_qPoch_def : qPoch (X : R⟦X⟧) n = qPoch (X : R⟦X⟧) (n - k) * qPoch (X * X ^ (n - k)) k := by
      have h_rhs : qPoch (X : R⟦X⟧) n = qPoch (X : R⟦X⟧) (n - k) * ∏ i ∈ Finset.range k, (1 - X * X ^ (n - k + i)) := by
        unfold qPoch
        rw [ ← Finset.prod_range_add, Nat.sub_add_cancel ( by omega ) ]
      convert h_rhs using 2
      exact Finset.prod_congr rfl fun _ _ => by ring
    have h_qPoch_mod : qPoch (X * X ^ (n - k)) k - 1 ∈ {f : R⟦X⟧ | ∀ j < n - k + 1, (coeff j) f = 0} := by
      intro j hj
      revert j hj
      induction k with
      | zero => intro j hj; simp_all +decide [ qPoch ]
      | succ k ih =>
          intro j hj
          simp_all +decide [ qPoch ]
          induction ( range ( k + 1 ) ) using Finset.induction <;> simp_all +decide [ Finset.prod_insert, pow_succ, mul_assoc, mul_left_comm, mul_add, add_mul, sub_mul, mul_sub ]
          simp_all +decide [ ← mul_assoc, ← pow_succ', coeff_X_pow ]
          simp_all +decide [ ← pow_add, coeff_mul ]
          rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ coeff_X_pow ]
          intros; omega
    intro j hj; specialize h_qPoch_mod j hj; simp_all +decide [ ← mul_assoc, ← eq_sub_iff_add_eq' ] 
    rw [ mul_right_comm, qPoch_mul_qPochInv ] ; aesop
  have h_coeff : (qBinom n k (X : R⟦X⟧) - qPochInv k) * qPoch (X : R⟦X⟧) k ∈ {f : R⟦X⟧ | ∀ j < n - k + 1, (coeff j) f = 0} := by
    convert h_rhs using 1
    simp +decide [ ← h_eq, sub_mul ]
    simp +decide [ mul_assoc, qPoch_mul_qPochInv ]
  have h_coeff_inv : (qBinom n k (X : R⟦X⟧) - qPochInv k) ∈ {f : R⟦X⟧ | ∀ j < n - k + 1, (coeff j) f = 0} := by
    intro j hj
    revert hj
    induction j using Nat.strong_induction_on
    next j ih =>
    intro hj
    have := h_coeff j hj
    rw [ PowerSeries.coeff_mul ] at this
    rw [ Finset.sum_eq_single ( j, 0 ) ] at this <;> simp_all +decide [ Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ]
    · rw [ constantCoeff_qPoch_X ] at this ; aesop
    · intro a b hab h; specialize ih a; rcases eq_or_ne a j with rfl | ha <;> simp_all +decide
      rw [ ih ( lt_of_le_of_ne ( by omega ) ha ) ( by omega ), MulZeroClass.zero_mul ]
  exact h ( by simpa [ sub_eq_zero ] using h_coeff_inv j ( by omega ) )

private theorem qPoch_neg_eq_sum (a : R⟦X⟧) (n : ℕ) :
    qPoch (-a) n = ∑ k ∈ Finset.range (n + 1),
      X ^ k.choose 2 * qSeries.qBinom n k (X : R⟦X⟧) * a ^ k := by
  unfold qPoch
  have h := qBinom_finite_thm ( X : R⟦X⟧ ) a n; simp_all +decide [ mul_comm ] 

private theorem euler2_coeff_vanish (a : R⟦X⟧) (d k : ℕ) (hk : d < k.choose 2) :
    PowerSeries.coeff d (X ^ k.choose 2 * a ^ k * qPochInv (R := R) k) = 0 := by
  simp +decide [ mul_assoc, PowerSeries.coeff_mul, hk ]
  simp +decide [ PowerSeries.coeff_X_pow, hk.ne' ]
  exact Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Finset.mem_antidiagonal.mp hx ] )

/-- FPS Euler second identity: `qPochInf(-a) = Σ_{k≥0} X^{C(k,2)} · a^k · (qPoch X k)⁻¹` in `R⟦X⟧`. -/
theorem fps_euler_second (a : R⟦X⟧) :
    qPochInf (-a) = ∑' k : ℕ, X ^ k.choose 2 * a ^ k * qPochInv (R := R) k := by
  simp +decide [ PowerSeries.ext_iff, coeff_qPochInf, qPoch_neg_eq_sum ] at *
  intro n
  have h_sum_eq : ∑ x ∈ Finset.range (n + 2), (PowerSeries.coeff n) (X ^ x.choose 2 * qSeries.qBinom (n + 1) x (X : R⟦X⟧) * a ^ x) = ∑' k : ℕ, (PowerSeries.coeff n) (X ^ k.choose 2 * a ^ k * qPochInv (R := R) k) := by
    rw [ tsum_eq_sum ]
    refine Finset.sum_congr rfl fun x hx => ?_
    · by_cases h : n < x.choose 2 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
      · rw [ PowerSeries.coeff_mul, PowerSeries.coeff_mul ]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [ PowerSeries.coeff_mul, PowerSeries.coeff_mul ]
        refine congr_arg _ ( Finset.sum_congr rfl fun q hq => ?_ )
        rw [ PowerSeries.coeff_X_pow ]
        split_ifs <;> simp_all +decide [ Finset.mem_antidiagonal ]
        omega
      · have h_coeff_eq : ∀ j ≤ n - x.choose 2, PowerSeries.coeff j (qSeries.qBinom (n + 1) x (X : R⟦X⟧)) = PowerSeries.coeff j (qPochInv (R := R) x) := by
          intro j hj
          apply coeff_qBinom_eq_qPochInv
          exact (by
          rcases x with ( _ | _ | x ) <;> simp_all +decide [ Nat.choose ]
          · lia
          · omega)
        simp +decide [ PowerSeries.coeff_mul, h_coeff_eq ]
        refine Finset.sum_congr rfl fun i hi => ?_
        refine congr_arg _ ( Finset.sum_congr rfl fun p hp => ?_ )
        by_cases h : p.2 ≤ n - x.choose 2 <;> simp_all +decide [ PowerSeries.coeff_X_pow ]
        grind +revert
    · intro b hb; by_cases h : n < b.choose 2 <;> simp_all +decide [ euler2_coeff_vanish ] 
      rcases b with ( _ | _ | b ) <;> simp_all +decide [ Nat.choose ]
      linarith [ Nat.choose_pos ( by omega : 2 ≤ b ) ]
  rw [ h_sum_eq, tsum_eq_sum ]
  any_goals exact Finset.range ( n + 2 )
  · convert h_sum_eq.symm using 1
    · rw [ tsum_eq_sum ]
      intro k hk
      convert euler2_coeff_vanish a n k _ using 1
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose ]
      omega
    · convert h_sum_eq.symm using 1
      have h_summable : Summable (fun k : ℕ => X ^ k.choose 2 * a ^ k * qPochInv (R := R) k) := by
        have h_summable : ∀ d : ℕ, ∃ N : ℕ, ∀ k ≥ N, (PowerSeries.coeff d) (X ^ k.choose 2 * a ^ k * qPochInv (R := R) k) = 0 := by
          intro d
          use d + 2
          intro k hk
          have h_coeff_zero : (PowerSeries.coeff d) (X ^ k.choose 2 * a ^ k * qPochInv (R := R) k) = 0 := by
            apply euler2_coeff_vanish
            induction hk <;> simp_all +decide [ Nat.choose ]; all_goals grind
          exact h_coeff_zero
        refine Pi.summable.mpr ?_
        intro x
        obtain ⟨N, hN⟩ := h_summable (x 0)
        refine summable_of_ne_finset_zero (s := Finset.range N) ?_
        simp +zetaDelta at *
        convert hN using 1
        convert Iff.rfl
        convert MvPowerSeries.coeff_apply _ _
        ext; simp [Finsupp.single_apply]
      have h_cont : Continuous (fun f : R⟦X⟧ => PowerSeries.coeff n f) :=
        WithPiTopology.continuous_coeff R n
      exact (h_summable.hasSum.map (PowerSeries.coeff n).toAddMonoidHom h_cont).tsum_eq.symm
  · intro k hk
    convert euler2_coeff_vanish a n k _ using 1
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose ]
    grind +extAll

end Euler2


section KeyIdentity

/-- The key sum `S_k = ∑_m X^{m(m+k)} / ((X;X)_m (X;X)_{m+k})`. -/
def S_fps (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k)

/-- The defining series for `S_fps k` is summable in `R⟦X⟧`. -/
theorem summable_S_fps (k : ℕ) :
    Summable (fun m : ℕ => X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k)) := by
  rw [ ← summable_congr fun m => ?_ ]
  swap
  exact fun m => mk fun d => if d < m * ( m + k ) then 0 else coeff ( d - m * ( m + k ) ) ( qPochInv ( R := R ) m * qPochInv ( m + k ) )
  · refine Pi.summable.mpr ?_
    intro x
    simp [PowerSeries.mk]
    exact summable_of_ne_finset_zero (s := Finset.range (x () + 1)) (fun n hn => if_pos (by nlinarith [Finset.mem_range.not.mp hn]))
  · ext d; simp +decide [ mul_assoc, mul_comm, mul_left_comm, PowerSeries.coeff_mul ] 
    split_ifs <;> simp_all +decide [ PowerSeries.coeff_X_pow ]
    · exact Eq.symm ( Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Finset.mem_antidiagonal.mp hx ] ) )
    · rw [ ← Finset.sum_filter ]
      rw [ ← Finset.sum_biUnion ]
      · refine Finset.sum_bij ( fun x hx => ( x.1, x.2 ) ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.mem_biUnion ]
        grind
      · intro a ha b hb hab; simp_all +decide [ Finset.disjoint_left ] 
        grind

/-- Key auxiliary: `qPochInv(n-1) + X^n * qPochInv(n) = qPochInv(n)`.
    Equivalently, `(1 - X^{n+1}) * qPochInv(n+1) + X^{n+1} * qPochInv(n+1) = qPochInv(n+1)`. -/
private theorem qPochInv_split (n : ℕ) :
    qPochInv (R := R) n + X ^ (n + 1) * qPochInv (R := R) (n + 1) =
    qPochInv (R := R) (n + 1) := by
  have h := qPochInv_succ_mul (R := R) n
  -- h : (1 - X^{n+1}) * qPochInv(n+1) = qPochInv(n)
  rw [← h]; ring

/-- The intermediate sum `T_k = ∑ m, X^{m(m+k)} * qPochInv(m) * qPochInv(m+k+1)`. -/
private def T_fps (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k + 1)

private theorem summable_T_fps (k : ℕ) :
    Summable (fun m : ℕ => X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k + 1)) := by
  rw [ ← summable_congr fun m => ?_ ]
  swap
  exact fun m => mk fun d => if d < m * ( m + k ) then 0 else PowerSeries.coeff ( d - m * ( m + k ) ) ( qPochInv ( R := R ) m * qPochInv ( m + k + 1 ) )
  · refine Pi.summable.mpr ?_
    intro x
    simp [PowerSeries.mk]
    exact summable_of_ne_finset_zero (s := Finset.range (x () + 1)) (fun n hn => if_pos (by nlinarith [Finset.mem_range.not.mp hn]))
  · ext d; simp +decide [ PowerSeries.coeff_mul, mul_assoc ] 
    split_ifs <;> simp_all +decide [ PowerSeries.coeff_X_pow ]
    · exact Eq.symm ( Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Finset.mem_antidiagonal.mp hx ] ) )
    · rw [ ← Finset.sum_filter ]
      rw [ ← Finset.sum_biUnion ]
      · refine Finset.sum_bij ( fun x hx => ( x.1, x.2 ) ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.mem_biUnion ]
        grind
      · intro a ha b hb hab; simp_all +decide [ Finset.disjoint_left ] 
        lia

private theorem T_eq_S_add (k : ℕ) :
    T_fps (R := R) k = S_fps k + X ^ (k + 1) * S_fps (k + 1) := by
  unfold T_fps S_fps
  rw [ ← Summable.tsum_mul_left ]
  · rw [ ← Summable.tsum_add ]
    · refine tsum_congr fun m => ?_
      have h_split : qPochInv (m + k) = (1 - (X : R⟦X⟧) ^ (m + k + 1)) * qPochInv (m + k + 1) := by
        rw [ ← qPochInv_succ_mul ]
      rw [ h_split ] ; ring
    · convert summable_S_fps k using 1
      infer_instance
    · refine Summable.mul_left _ ?_
      convert summable_S_fps ( k + 1 ) using 1
      infer_instance
  · convert summable_S_fps ( k + 1 ) using 1
    infer_instance

private theorem X_mul_S_shift (k : ℕ) :
    X ^ (k + 1) * S_fps (R := R) (k + 2) =
    ∑' n : ℕ, X ^ ((n + 1) * (n + 1 + k)) * qPochInv (R := R) n * qPochInv (n + k + 2) := by
  convert Summable.tsum_mul_left ( X ^ ( k + 1 ) ) _ using 1
  any_goals try exact inferInstance
  rotate_left
  convert ( Summable.tsum_mul_left _ _ ) using 1
  any_goals exact summable_S_fps ( k + 2 )
  congr! 1
  rotate_left
  all_goals try infer_instance
  · rw [ Summable.tsum_mul_left ]
    · unfold S_fps; ring
    · exact summable_S_fps ( k + 2 )
  · ext; ring

private theorem T_eq_S_add' (k : ℕ) :
    T_fps (R := R) k = S_fps (k + 1) + X ^ (k + 1) * S_fps (k + 2) := by
  refine HasSum.tsum_eq ?_
  have h_combined : HasSum (fun m : ℕ => X ^ ((m + 1) * (m + 1 + k)) * qPochInv m * qPochInv (m + k + 2)) (X ^ (k + 1) * S_fps (R := R) (k + 2)) := by
    have h_combined : HasSum (fun m : ℕ => X ^ (m * (m + (k + 2))) * qPochInv m * qPochInv (m + (k + 2))) (S_fps (R := R) (k + 2)) := by
      exact Summable.hasSum ( summable_S_fps _ )
    convert HasSum.mul_left ( X ^ ( k + 1 ) ) h_combined using 1 ; ring
    exact funext fun n => by ring
  convert hasSum_nat_add_iff' 1 |>.1 _ using 1
  · infer_instance
  · convert HasSum.add ( hasSum_nat_add_iff' 1 |>.2 <| show HasSum ( fun n => X ^ ( n * ( n + ( k + 1 ) ) ) * qPochInv n * qPochInv ( n + ( k + 1 ) ) ) ( S_fps ( k + 1 ) ) from ?_ ) h_combined using 1
    · ext n; simp +decide [ add_assoc, pow_add ] ; ring
      rw [ show qPochInv n = qPochInv ( n + 1 ) - X ^ ( n + 1 ) * qPochInv ( n + 1 ) by
            exact eq_sub_of_add_eq ( qPochInv_split n ) ] ; ring
      simp +decide [ mul_assoc, ← pow_add ]
    · simp +decide [ add_comm, add_left_comm, add_assoc ]
      ring
    · exact Summable.hasSum ( summable_S_fps _ )

/-- The recurrence: `S_k − S_{k+1} = X^{k+1} (S_{k+2} − S_{k+1})`. -/
theorem S_fps_recurrence (k : ℕ) :
    S_fps (R := R) k - S_fps (k + 1) =
    X ^ (k + 1) * (S_fps (R := R) (k + 2) - S_fps (k + 1)) := by
  have h1 := T_eq_S_add (R := R) k
  have h2 := T_eq_S_add' (R := R) k
  have h3 : S_fps (R := R) k + X ^ (k + 1) * S_fps (k + 1) =
    S_fps (k + 1) + X ^ (k + 1) * S_fps (k + 2) := by rw [← h1, ← h2]
  have h4 : S_fps (R := R) k - S_fps (k + 1) =
    X ^ (k + 1) * S_fps (R := R) (k + 2) - X ^ (k + 1) * S_fps (k + 1) := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (X ^ (k + 1) * S_fps (k + 2))]; exact h3
  rw [h4, mul_sub]

/-- `S_fps k` is independent of `k`: all values are equal to `S_fps 0`. -/
theorem S_fps_const (k : ℕ) : S_fps (R := R) k = S_fps 0 := by
  revert k
  have h_recurrence : ∀ k, S_fps (R := R) k - S_fps (R := R) (k + 1) = X ^ (k + 1) * (S_fps (R := R) (k + 2) - S_fps (R := R) (k + 1)) :=
    S_fps_recurrence
  have h_induction : ∀ k, ∀ d, d < k + 1 → PowerSeries.coeff d (S_fps (R := R) k - S_fps (R := R) (k + 1)) = 0 := by
    intro k d hd
    rw [ h_recurrence k, PowerSeries.coeff_mul ]
    exact Finset.sum_eq_zero fun p hp => by rw [ PowerSeries.coeff_X_pow, if_neg ( by linarith [ Finset.mem_antidiagonal.mp hp ] ) ] ; ring
  have h_induction_step : ∀ k, S_fps (R := R) k - S_fps (R := R) (k + 1) = 0 := by
    intro k
    ext d
    by_cases hd : d < k + 1
    · exact h_induction k d hd
    · revert hd k
      induction d using Nat.strong_induction_on
      next d ih =>
      intro k hd
      rw [ h_recurrence k, PowerSeries.coeff_mul ]
      rw [ Finset.sum_eq_single ( k + 1, d - ( k + 1 ) ) ] <;> simp +decide [ hd ]
      · specialize ih ( d - ( k + 1 ) ) ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.succ_pos _ ) ) ( k + 1 ) ; simp_all +decide [ Nat.sub_sub ]
        by_cases h : k + 1 + ( k + 1 ) < d <;> simp_all +decide [ ← h_recurrence ]
        · rw [ sub_eq_zero ] at * ; aesop
        · grind
      · intro a b hab h; by_cases ha : a = k + 1 <;> simp_all +decide [ PowerSeries.coeff_X_pow ]
        omega
      · exact fun h => False.elim <| h <| add_tsub_cancel_of_le <| le_of_not_gt hd
  exact fun k => Nat.recOn k rfl fun n ih => by linear_combination' ih - h_induction_step n

/-- For `d < k`, the `d`-th coefficient of `qPochInv k` equals the `d`-th coefficient of `qqInv`. -/
theorem coeff_qPochInv_eq_qqInv {k d : ℕ} (hkd : d < k) :
    PowerSeries.coeff d (qPochInv (R := R) k) = PowerSeries.coeff d (qqInv (R := R)) := by
  revert hkd
  induction d using Nat.strong_induction_on
  next d ih =>
  intro hkd
  have h_coeff_zero : (PowerSeries.coeff d) (qPochInf (X : R⟦X⟧) * (qPochInv (R := R) k - qqInv (R := R))) = 0 := by
    have h_coeff_zero : (PowerSeries.coeff d) (qPochInf (X * X ^ k)) = (PowerSeries.coeff d) (1 : R⟦X⟧) := by
      rw [ qSeries.FPS.coeff_qPochInf ]
      rw [ qPoch ]
      simp +decide [ ← pow_succ', ← pow_add, Finset.prod_mul_distrib ]
      induction ( Finset.range ( d + 1 ) ) using Finset.induction <;> simp_all +decide [ Finset.prod_range_succ ]
      simp_all +decide [ sub_mul, PowerSeries.coeff_mul ]
      rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ PowerSeries.coeff_X_pow ]
      omega
    simp_all +decide [ mul_sub, qqInf_mul_qPochInv ]
  simp_all +decide [ PowerSeries.coeff_mul ]
  rw [ Finset.sum_eq_single ( 0, d ) ] at h_coeff_zero <;> simp_all +decide [ Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ]
  · have h_const_coeff : constantCoeff (qPochInf (X : R⟦X⟧)) = 1 := by
      convert constantCoeff_qPochInf_of_order_pos ( X : R⟦X⟧ ) _
      · exact funext fun x => by simp +decide [ PowerSeries.coeff_zero_eq_constantCoeff ]
      · simp +decide [ PowerSeries.coeff_X ]
    grind +revert
  · intro a b hab h; specialize ih b ( by omega ) ( by omega ) ; aesop

/-- For `d < k`, the `d`-th coefficient of `S_fps k` equals the `d`-th coefficient of `qqInv`. -/
theorem coeff_S_fps_eq_qqInv (k : ℕ) (d : ℕ) (hkd : d < k) :
    PowerSeries.coeff d (S_fps (R := R) k) = PowerSeries.coeff d (qqInv (R := R)) := by
  have hS_k : S_fps k = ∑' m : ℕ, X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k) := by
    rfl
  have h_sum_zero : ∑' m : ℕ, (PowerSeries.coeff d) (X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k)) = (PowerSeries.coeff d) (X ^ 0 * qPochInv (R := R) 0 * qPochInv (0 + k)) := by
    rw [ tsum_eq_single 0 ]
    · simp +decide
    · intro m hm; rw [ mul_assoc, PowerSeries.coeff_mul ] 
      rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ PowerSeries.coeff_X_pow ]
      exact fun h => absurd h ( by nlinarith [ Nat.pos_of_ne_zero hm ] )
  convert h_sum_zero using 1
  · have h_sum_zero : ∀ {f : ℕ → R⟦X⟧}, Summable f →
        (PowerSeries.coeff d) (∑' m : ℕ, f m) = ∑' m : ℕ, (PowerSeries.coeff d) (f m) :=
      fun hf => ((hf.hasSum.map (PowerSeries.coeff d).toAddMonoidHom
        (WithPiTopology.continuous_coeff R d)).tsum_eq).symm
    exact h_sum_zero (summable_S_fps (R := R) k) ▸ hS_k ▸ rfl
  · have := qPoch_mul_qPochInv ( R := R ) 0; simp_all +decide [ qPoch ] 
    convert coeff_qPochInv_eq_qqInv ( show d < k from hkd ) |> Eq.symm using 1

/-- **Key identity**: `S_k = (qPochInf X)⁻¹` for all `k ≥ 0`. -/
theorem fps_key_identity (k : ℕ) : S_fps (R := R) k = qqInv := by
  ext d
  have h1 := S_fps_const (R := R) k
  have h2 := S_fps_const (R := R) (d + 1)
  have h3 := coeff_S_fps_eq_qqInv (R := R) (d + 1) d (Nat.lt_succ_self d)
  calc PowerSeries.coeff d (S_fps k)
      = PowerSeries.coeff d (S_fps 0) := by rw [h1]
    _ = PowerSeries.coeff d (S_fps (d + 1)) := by rw [h2]
    _ = PowerSeries.coeff d qqInv := h3

end KeyIdentity


section Cauchy

/-- `qPochInf X * qPochInf(-a) = Σ_n X^{C(n,2)} a^n qPochInf(X · X^n)` in `R⟦X⟧`. -/
theorem qqInf_mul_euler2 (a : R⟦X⟧) :
    qPochInf (X : R⟦X⟧) * qPochInf (-a) =
    ∑' n : ℕ, X ^ n.choose 2 * a ^ n * qPochInf (X * X ^ n) := by
  have h_euler : qPochInf (-a) = ∑' n : ℕ, X ^ (n.choose 2) * a ^ n * qPochInv n := by
    convert fps_euler_second a using 1
  have h_subst : ∀ n : ℕ, qPochInf X * (X ^ (n.choose 2) * a ^ n * qPochInv n) = X ^ (n.choose 2) * a ^ n * qPochInf (X * X ^ n) := by
    intro n
    rw [← qqInf_mul_qPochInv n]
    ring
  by_cases h : Summable ( fun n : ℕ => X ^ n.choose 2 * a ^ n * qPochInv n ) <;> simp_all +decide [ tsum_mul_left ]
  · rw [ ← funext h_subst, ← h.tsum_mul_left ]
  · simp +decide [ ← h_subst, tsum_eq_zero_of_not_summable h ]
    rw [ tsum_eq_zero_of_not_summable ]
    contrapose! h
    convert h.mul_left ( qqInv ( R := R ) ) using 1
    simp +decide [ ← mul_assoc, qqInv_mul_qqInf ]

/-- Cauchy diagonal coefficient for non-negative index `k`: the `(m+k, m)` diagonal of the double series sums to `X^{C(k,2)}` in `R⟦X⟧`. -/
theorem cauchy_coeff_nonneg (k : ℕ) :
    HasSum (fun m : ℕ =>
      X ^ (m + k).choose 2 * qPochInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochInv (R := R) m))
      (X ^ k.choose 2 : R⟦X⟧) := by
  have h_sum : HasSum (fun m : ℕ => X ^ (m * (m + k)) * qPochInf (X : R⟦X⟧) * qPochInv (m + k) * qPochInv m) 1 := by
    have h_sum : HasSum (fun m : ℕ => X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k)) (qqInv (R := R)) := by
      convert ( summable_S_fps ( R := R ) k |> Summable.hasSum ) using 1
      convert fps_key_identity k |> Eq.symm
    convert h_sum.mul_left ( qPochInf ( X : R⟦X⟧ ) ) using 1 <;> ring
    · ext; ring
    · rw [ qqInf_mul_qqInv ]
  convert h_sum.mul_left ( X ^ k.choose 2 ) using 1
  · ext m; rw [ ← qqInf_mul_qPochInv ] ; ring
    rw [ show ( m + k ).choose 2 = m.choose 2 + m * k + k.choose 2 by
          rw [ Nat.add_choose_eq ]
          simp +decide [ Finset.Nat.sum_antidiagonal_succ ] ; ring ] ; ring
    rw [ show m ^ 2 = m.choose 2 * 2 + m by
          exact Nat.recOn m ( by norm_num ) fun n ih => by simp +decide [ Nat.choose_succ_succ, pow_succ' ] at * ; linarith; ] ; ring
  · rw [ mul_one ]

/-- Cauchy diagonal coefficient for negative index `-(l+1)`: the `(n, n+l+1)` diagonal of the double series sums to `X^{C(l+2,2)}` in `R⟦X⟧`. -/
theorem cauchy_coeff_neg (l : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ n.choose 2 * qPochInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochInv (R := R) (n + (l + 1))))
      (X ^ (l + 2).choose 2 : R⟦X⟧) := by
  have h_sum : HasSum (fun n : ℕ => X ^ (n * (n + (l + 1))) * qPochInv (R := R) n * qPochInv (R := R) (n + (l + 1))) (qqInv (R := R)) := by
    convert Summable.hasSum _
    · convert fps_key_identity ( l + 1 ) |> Eq.symm using 1
    · convert summable_S_fps ( l + 1 ) using 1
      infer_instance
  convert HasSum.mul_left ( X ^ ( l + 2 ).choose 2 * qPochInf ( X : R⟦X⟧ ) ) h_sum using 1
  · ext n; simp +decide [ ← mul_assoc, ← pow_add ] 
    rw [ ← qqInf_mul_qPochInv ]
    rw [ show ( n + ( l + 1 ) ).choose 2 + ( n + ( l + 1 ) ) = ( l + 2 ).choose 2 + n * ( n + ( l + 1 ) ) - n.choose 2 by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ choose2_add' n l ] ] ; ring
    rw [ ← pow_add, ← pow_add, ← pow_add, ← pow_add ]
    rw [ Nat.add_sub_of_le ( by nlinarith [ Nat.choose_le_pow n 2 ] ) ]
  · rw [ mul_assoc, qqInf_mul_qqInv, mul_one ]

end Cauchy


section JTP

private theorem jtpProd_expand :
    @jtpProd = (∑' n : ℕ, X ^ n.choose 2 * z ^ n * qPochInf (X * X ^ n)) *
              (∑' m : ℕ, X ^ (m.choose 2 + m) * zinv ^ m * qPochInv m) := by
  convert congr_arg₂ ( · * · ) ( qqInf_mul_euler2 z ) _ using 1
  convert fps_euler_second ( X * zinv ) using 1
  · exact tprod_congr fun _ => by ring
  · simp +decide [ pow_add, mul_pow, mul_assoc, mul_comm, mul_left_comm ]

open LaurentPolynomial in
/-- `z * zinv = 1` in `A⟦X⟧`. -/
private theorem z_mul_zinv : z * zinv = 1 := by
  show PowerSeries.C (T 1) * PowerSeries.C (T (-1)) = 1
  rw [← map_mul, ← map_one (PowerSeries.C (R := LaurentPolynomial ℂ))]
  congr 1
  unfold T
  rw [AddMonoidAlgebra.single_mul_single, mul_one]
  norm_num

open LaurentPolynomial in
/-- `z ^ n * zinv ^ n = 1` for all `n`. -/
private theorem z_pow_mul_zinv_pow (n : ℕ) : z ^ n * zinv ^ n = 1 := by
  rw [← mul_pow, z_mul_zinv, one_pow]

open LaurentPolynomial in
/-- `z ^ n = PS (T n)` for natural `n`. -/
private theorem z_pow_eq (n : ℕ) :
    z ^ n = (PowerSeries.C : LaurentPolynomial ℂ →+* _) (T (n : ℤ)) := by
  induction n <;> simp_all +decide [ pow_succ' ]
  rw [ PowerSeries.ext_iff ] at *
  grind +suggestions

open LaurentPolynomial in
/-- `zinv ^ (m + 1) = PS (T (-(↑m + 1)))`. -/
private theorem zinv_pow_eq (m : ℕ) :
    zinv ^ (m + 1) = (PowerSeries.C : LaurentPolynomial ℂ →+* _) (T (-(↑m + 1))) := by
  induction m <;> simp_all +decide [ pow_succ, zinv ]
  rw [ ← map_mul, mul_comm ]
  erw [ AddMonoidAlgebra.single_mul_single ] ; norm_num

open LaurentPolynomial in
/-- Non-negative diagonal of the Cauchy product: HasSum giving `z^k * X^{C(k,2)}`. -/
private theorem nonneg_diag_hasSum (k : ℕ) :
    HasSum (fun m : ℕ =>
      (X ^ (m + k).choose 2 * z ^ (m + k) * qPochInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * zinv ^ m * qPochInv m))
      (z ^ k * X ^ k.choose 2) := by
  have key : ∀ m, (X ^ (m + k).choose 2 * z ^ (m + k) * qPochInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * zinv ^ m * qPochInv (R := LaurentPolynomial ℂ) m) =
      z ^ k * (X ^ (m + k).choose 2 * qPochInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochInv m)) := by
    intro m
    have hz := z_pow_mul_zinv_pow m
    rw [pow_add z m k, pow_add (X : (LaurentPolynomial ℂ)⟦X⟧) (m.choose 2) m]
    calc _ = z ^ k * (z ^ m * zinv ^ m) *
        (X ^ (m + k).choose 2 * qPochInf (X * X ^ (m + k)) *
        (X ^ m.choose 2 * X ^ m * qPochInv m)) := by ring
      _ = _ := by rw [hz, mul_one]
  simp_rw [key]
  exact HasSum.mul_left _ (cauchy_coeff_nonneg k)

open LaurentPolynomial in
/-- Negative diagonal of the Cauchy product: HasSum giving `zinv^{l+1} * X^{C(l+2,2)}`. -/
private theorem neg_diag_hasSum (l : ℕ) :
    HasSum (fun n : ℕ =>
      (X ^ n.choose 2 * z ^ n * qPochInf (X * X ^ n)) *
      (X ^ ((n + (l + 1)).choose 2 + (n + (l + 1))) * zinv ^ (n + (l + 1)) *
      qPochInv (n + (l + 1))))
      (zinv ^ (l + 1) * X ^ (l + 2).choose 2) := by
  have key : ∀ n, (X ^ n.choose 2 * z ^ n * qPochInf (X * X ^ n)) *
      (X ^ ((n + (l + 1)).choose 2 + (n + (l + 1))) * zinv ^ (n + (l + 1)) *
      qPochInv (R := LaurentPolynomial ℂ) (n + (l + 1))) =
      zinv ^ (l + 1) * (X ^ n.choose 2 * qPochInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochInv (n + (l + 1)))) := by
    intro n
    have hz := z_pow_mul_zinv_pow n
    rw [pow_add zinv n (l + 1), pow_add (X : (LaurentPolynomial ℂ)⟦X⟧) ((n + (l + 1)).choose 2) (n + (l + 1))]
    calc _ = zinv ^ (l + 1) * (z ^ n * zinv ^ n) *
        (X ^ n.choose 2 * qPochInf (X * X ^ n) *
        (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochInv (n + (l + 1)))) := by ring
      _ = _ := by rw [hz, mul_one]
  simp_rw [key]
  exact HasSum.mul_left _ (cauchy_coeff_neg l)

/-- The equivalence ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) splitting along the diagonal:
  (n, m) ↦ if m ≤ n then inl (n - m, m) else inr (m - n - 1, n). -/
private def diagEquiv : ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun p := if p.2 ≤ p.1 then Sum.inl (p.1 - p.2, p.2) else Sum.inr (p.2 - p.1 - 1, p.1)
  invFun s := match s with
    | Sum.inl (k, m) => (m + k, m)
    | Sum.inr (l, n) => (n, n + l + 1)
  left_inv := by intro ⟨n, m⟩; simp only; split_ifs with h <;> simp <;> omega
  right_inv := by intro s; rcases s with ⟨k, m⟩ | ⟨l, n⟩ <;> simp <;> omega

open LaurentPolynomial in
private abbrev a_n (n : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ n.choose 2 * z ^ n * qPochInf (X * X ^ n)

open LaurentPolynomial in
private abbrev b_m (m : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ (m.choose 2 + m) * zinv ^ m * qPochInv m

open LaurentPolynomial in
/-- The a_n sequence is summable. -/
private theorem summable_a : Summable a_n := by
  refine Pi.summable.mpr ?_
  intro x
  have h_summable : ∀ d : ℕ, Summable (fun n : ℕ => PowerSeries.coeff d (a_n n)) := by
    intro d
    have h_summable : ∀ n : ℕ, n > d + 1 → PowerSeries.coeff d (a_n n) = 0 := by
      intro n hn; rw [ show a_n n = X ^ n.choose 2 * z ^ n * qPochInf ( X * X ^ n ) by rfl ] ; simp +decide [ PowerSeries.coeff_mul, PowerSeries.coeff_X_pow ] 
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [ Finset.sum_eq_zero ] <;> simp +zetaDelta at *
      intros; subst_vars; simp_all +decide [ Nat.choose_two_right ] 
      nlinarith [ Nat.div_add_mod ( n * ( n - 1 ) ) 2, Nat.mod_lt ( n * ( n - 1 ) ) two_pos, Nat.sub_add_cancel ( by omega : 1 ≤ n ) ]
    rw [ ← summable_nat_add_iff ( d + 2 ) ]
    exact ⟨ _, hasSum_single 0 fun n hn => h_summable _ <| by omega ⟩
  convert h_summable ( x 1 ) using 1
  ext n; exact (by
  unfold a_n; simp +decide [ Finsupp.single_apply ] 
  convert rfl
  convert MvPowerSeries.coeff_apply _ _
  ext; simp [Finsupp.single_apply])

open LaurentPolynomial in
/-- The b_m sequence is summable. -/
private theorem summable_b : Summable b_m := by
  refine Pi.summable.mpr ?_
  intro x
  have h_finite : Set.Finite {i : ℕ | b_m i x ≠ 0} := by
    have h_lowest_degree : ∀ m : ℕ, ∀ x : Unit →₀ ℕ, b_m m x ≠ 0 → x 0 ≥ m.choose 2 + m := by
      intro m x hx_nonzero
      have h_degree : PowerSeries.coeff (x 0) (b_m m) ≠ 0 := by
        contrapose! hx_nonzero; simp_all +decide [ MvPowerSeries.coeff ] 
        convert hx_nonzero using 1
        convert MvPowerSeries.coeff_apply _ _
        · convert MvPowerSeries.coeff_apply _ _
          ext; simp [Finsupp.single_apply]
        · infer_instance
      contrapose! h_degree
      simp +decide [ b_m, PowerSeries.coeff_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_C ]
      exact Finset.sum_eq_zero fun y hy => by rw [ Finset.sum_eq_zero fun z hz => if_neg ( by linarith [ Finset.mem_antidiagonal.mp hy, Finset.mem_antidiagonal.mp hz ] ) ] ; ring
    exact Set.finite_iff_bddAbove.mpr ⟨ x 0, fun m hm => by linarith [ h_lowest_degree m x hm, Nat.choose_pos ( show m ≤ m from le_rfl ) ] ⟩
  exact summable_of_ne_finset_zero (s := h_finite.toFinset) (fun i hi => Classical.not_not.1 fun hi' => hi (h_finite.mem_toFinset.2 hi'))

open LaurentPolynomial in
/-- The double product sequence is summable. -/
private theorem summable_ab :
    Summable (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) := by
  have h_tensor : ∀ x : ℕ, Summable (fun p : ℕ × ℕ => (a_n p.1 * b_m p.2).coeff x) := by
    intro x
    have h_tensor : ∀ p : ℕ × ℕ, (a_n p.1 * b_m p.2).coeff x = 0 ∨ p.1 ≤ x + 1 ∧ p.2 ≤ x + 1 := by
      unfold a_n b_m; simp +decide [ PowerSeries.coeff_mul, PowerSeries.coeff_X_pow ] ; (
      intro a b; by_cases ha : a ≤ x + 1 <;> by_cases hb : b ≤ x + 1 <;> simp +decide [ ha, hb ] 
      · refine Finset.sum_eq_zero fun i hi => ?_ ; simp +decide [ Finset.sum_ite ] at hi ⊢
        refine Or.inr <| Finset.sum_eq_zero fun j hj => ?_ ; simp_all +decide [ Finset.sum_ite ]
        refine Or.inl <| Finset.sum_eq_zero fun k hk => ?_ ; simp_all +decide [ Finset.mem_filter, Finset.mem_antidiagonal ]
        linarith [ Nat.choose_pos ( by omega : 2 ≤ b ) ]
      · refine Finset.sum_eq_zero fun i hi => ?_
        simp +zetaDelta at *
        refine Or.inl <| Finset.sum_eq_zero fun j hj => ?_ ; simp_all +decide [ Nat.choose_eq_zero_of_lt ]
        refine Or.inl <| Finset.sum_eq_zero fun k hk => if_neg <| ?_ ; simp_all +decide [ Nat.choose_eq_zero_of_lt ]
        rw [ Nat.choose_two_right ]
        exact ne_of_lt <| Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by nlinarith only [ ha, hb, hi, hj, hk, Nat.sub_add_cancel ( by omega : 1 ≤ a ) ] 
      · refine Finset.sum_eq_zero fun i hi => ?_
        simp +zetaDelta at *
        refine Or.inr <| Finset.sum_eq_zero fun j hj => ?_ ; simp_all +decide [ Finset.mem_antidiagonal ]
        refine Or.inl <| Finset.sum_eq_zero fun k hk => if_neg <| ?_ ; linarith [ Finset.mem_antidiagonal.mp hk, Nat.choose_pos <| show 2 ≤ b from by omega ])
    generalize_proofs at *; (
    exact summable_of_ne_finset_zero (s := Finset.product (Finset.range (x + 2)) (Finset.range (x + 2))) (fun p hp => Or.resolve_right (h_tensor p) fun h => hp (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩)))
  refine Pi.summable.mpr ?_
  intro x; specialize h_tensor ( x 0 ) ; convert h_tensor using 1
  convert rfl
  convert MvPowerSeries.coeff_apply _ _
  ext; simp

open LaurentPolynomial in
/-- HasSum for the double product giving jtpProd. -/
private theorem hasSum_ab_jtpProd :
    HasSum (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) jtpProd := by
  have := @summable_ab
  convert this.hasSum using 1
  convert jtpProd_expand using 1
  convert ( Summable.tsum_mul_tsum ( show Summable a_n from ?_ ) ( show Summable b_m from ?_ ) ) using 1
  · constructor <;> intro h <;> simp_all +decide
  · convert summable_a using 1
  · convert summable_b using 1

open LaurentPolynomial in
/-- The non-negative part of the theta series is summable. -/
private theorem summable_nonneg :
    Summable (fun k : ℕ => z ^ k * X ^ k.choose 2) := by
  have h_summable : ∀ d : ℕ, ∃ N : ℕ, ∀ k ≥ N, PowerSeries.coeff d (z ^ k * X ^ k.choose 2) = 0 := by
    intro d
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ≥ N, k.choose 2 > d := by
      use d + 2
      intro k hk; induction hk <;> simp_all +decide [ Nat.choose ] 
      · grind
      · grind +qlia
    use N; intro k hk; specialize hN k hk; simp_all +decide [ PowerSeries.coeff_mul, PowerSeries.coeff_X_pow ] 
    exact Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Finset.mem_antidiagonal.mp hx ] )
  refine Pi.summable.mpr ?_
  intro x
  obtain ⟨ N, hN ⟩ := h_summable ( Finsupp.toMultiset x |> Multiset.count 1 )
  refine summable_of_ne_finset_zero (s := Finset.range N) ?_
  intro k hk; specialize hN k ( le_of_not_gt fun hk' => hk <| Finset.mem_range.mpr hk' ) ; simp_all +decide 
  convert hN using 1
  convert MvPowerSeries.coeff_mul _ _ _
  convert MvPowerSeries.coeff_mul _ _ _
  · ext; simp
  · infer_instance

open LaurentPolynomial in
/-- The negative part of the theta series is summable. -/
private theorem summable_neg :
    Summable (fun l : ℕ => zinv ^ (l + 1) * X ^ (l + 2).choose 2) := by
  have h_min_deg : ∀ l : ℕ, PowerSeries.order (zinv ^ (l + 1) * X ^ (l + 2).choose 2) = (l + 2).choose 2 := by
    intro l
    have h_min_deg : PowerSeries.order (zinv ^ (l + 1)) = 0 := by
      rw [ PowerSeries.order_eq ]
      simp +decide [ zinv ]
      exact Finsupp.single_ne_zero.mpr ( by norm_num )
    rw [ PowerSeries.order_mul, h_min_deg ] ; aesop
  refine Pi.summable.mpr ?_
  intro x
  refine summable_of_ne_finset_zero (s := Finset.range (x 0 + 1)) ?_
  intro l hl; specialize h_min_deg l; contrapose! hl
  have h_min_deg : PowerSeries.order (zinv ^ (l + 1) * X ^ (l + 2).choose 2) ≤ x 0 := by
    apply le_of_not_gt; intro h_contra
    rw [ PowerSeries.order ] at h_contra
    split_ifs at h_contra <;> simp_all +decide [ PowerSeries.coeff ]
    convert h_contra ( x PUnit.unit ) le_rfl using 1
    simp +decide [ MvPowerSeries.coeff ]
    convert hl using 1
    simp +decide [ LinearMap.proj ]
    congr!
    ext; simp
  simp_all +decide [ Nat.choose ]
  norm_cast at h_min_deg; omega

open LaurentPolynomial in
/-- Summability of the non-negative diagonal rearrangement. -/
private theorem summable_nonneg_diag :
    Summable (fun p : ℕ × ℕ => a_n (p.2 + p.1) * b_m p.2) := by
  have h_support : ∀ d : ℕ, Set.Finite {p : ℕ × ℕ | PowerSeries.coeff d (a_n (p.2 + p.1) * b_m p.2) ≠ 0} := by
    intro d
    refine Set.Finite.subset ( Set.finite_Icc 0 ( d + 1 ) |> Set.Finite.prod <| Set.finite_Icc 0 ( d + 1 ) ) ?_
    intro p hp
    have h_m : p.2 ≤ d := by
      contrapose! hp; simp_all +decide [ PowerSeries.coeff_mul ] 
      refine Finset.sum_eq_zero fun x hx => ?_ ; simp_all +decide [ PowerSeries.coeff_X_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ] 
      refine Or.inr <| Finset.sum_eq_zero fun i hi => if_neg <| ?_ ; simp_all +decide [ Nat.choose_two_right ]
      grind
    have h_k : p.2 + p.1 ≤ d + 1 := by
      contrapose! hp; simp_all +decide [ PowerSeries.coeff_mul ] 
      refine Finset.sum_eq_zero fun x hx => ?_ ; simp_all +decide [ coeff_X_pow ]
      refine Or.inl <| Finset.sum_eq_zero fun y hy => ?_ ; simp_all +decide [ Finset.mem_antidiagonal ]
      refine Or.inl <| Finset.sum_eq_zero fun z hz => if_neg <| ?_ ; simp_all +decide [ Finset.mem_antidiagonal ]
      rw [ Nat.choose_two_right ]
      exact ne_of_lt <| Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by nlinarith only [ hp, h_m, hx, hy, hz, Nat.sub_add_cancel ( by omega : 1 ≤ p.2 + p.1 ) ] 
    exact ⟨⟨Nat.zero_le _, by omega⟩, ⟨Nat.zero_le _, by omega⟩⟩
  have h_summable : ∀ d : ℕ, Summable (fun p : ℕ × ℕ => PowerSeries.coeff d (a_n (p.2 + p.1) * b_m p.2)) := by
    intro d; specialize h_support d; exact (by
    exact summable_of_ne_finset_zero (s := h_support.toFinset) (fun p hp => Classical.not_not.1 fun h => hp (h_support.mem_toFinset.2 h)))
  refine Pi.summable.mpr ?_
  intro x
  convert h_summable ( x 0 ) using 1
  convert rfl
  convert MvPowerSeries.coeff_apply _ _
  ext; simp

set_option maxHeartbeats 400000 in
open LaurentPolynomial in
/-- Summability of the negative diagonal rearrangement. -/
private theorem summable_neg_diag :
    Summable (fun p : ℕ × ℕ => a_n p.2 * b_m (p.2 + p.1 + 1)) := by
  have h_sum_zero : ∀ d : ℕ, Set.Finite {p : ℕ × ℕ | coeff d (a_n p.2 * b_m (p.2 + p.1 + 1)) ≠ 0} := by
    have h_min_deg : ∀ n l : ℕ, ∀ d : ℕ, coeff d (a_n n * b_m (n + l + 1)) ≠ 0 → n + l + 1 ≤ d := by
      intro n l d hd; contrapose! hd; simp_all +decide [ a_n, b_m ] 
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, PowerSeries.coeff_mul ]
      refine Finset.sum_eq_zero fun x hx => ?_ ; simp_all +decide [ PowerSeries.coeff_X_pow ]
      intro hx'; rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ add_assoc ] 
      intro h; linarith [ Nat.choose_pos ( by omega : 2 ≤ n + ( l + 1 ) ) ] 
    intro d; exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ d, d ⟩, fun p hp => by specialize h_min_deg p.2 p.1 d hp; exact ⟨ by omega, by omega ⟩ ⟩ 
  refine Pi.summable.mpr ?_
  intro x
  refine summable_of_ne_finset_zero (s := Set.Finite.toFinset (h_sum_zero (Finsupp.degree x))) ?_
  simp +contextual [ Finsupp.degree ]
  intro a b h; contrapose! h; simp_all +decide [ PowerSeries.coeff ] 
  convert h using 1
  rw [ show ( fun₀ | () => ∑ i ∈ x.support, x i ) = x from ?_ ]
  · rfl
  · rw [ Finset.sum_eq_single PUnit.unit ] <;> aesop

open LaurentPolynomial in
/-- HasSum for the non-negative diagonal (combined over all k). -/
private theorem hasSum_nonneg_part :
    HasSum (fun p : ℕ × ℕ => a_n (p.2 + p.1) * b_m p.2)
      (∑' k : ℕ, z ^ k * X ^ k.choose 2) := by
  have hf := summable_nonneg_diag
  have h1 := hf.hasSum
  have h2 : ∑' (p : ℕ × ℕ), a_n (p.2 + p.1) * b_m p.2 =
      ∑' k : ℕ, z ^ k * X ^ k.choose 2 := by
    rw [hf.tsum_prod' (fun k => (nonneg_diag_hasSum k).summable)]
    conv_rhs => rw [← summable_nonneg.hasSum.tsum_eq]
    exact tsum_congr fun k => (nonneg_diag_hasSum k).tsum_eq
  rwa [h2] at h1

open LaurentPolynomial in
/-- HasSum for the negative diagonal (combined over all l). -/
private theorem hasSum_neg_part :
    HasSum (fun p : ℕ × ℕ => a_n p.2 * b_m (p.2 + p.1 + 1))
      (∑' l : ℕ, zinv ^ (l + 1) * X ^ (l + 2).choose 2) := by
  have hf := summable_neg_diag
  have h1 := hf.hasSum
  have h2 : ∑' (p : ℕ × ℕ), a_n p.2 * b_m (p.2 + p.1 + 1) =
      ∑' l : ℕ, zinv ^ (l + 1) * X ^ (l + 2).choose 2 := by
    rw [hf.tsum_prod' (fun l => (neg_diag_hasSum l).summable)]
    conv_rhs => rw [← summable_neg.hasSum.tsum_eq]
    exact tsum_congr fun l => (neg_diag_hasSum l).tsum_eq
  rwa [h2] at h1

open LaurentPolynomial in
/-- HasSum for the double product giving jtpSeries. -/
private theorem hasSum_ab_jtpSeries :
    HasSum (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) jtpSeries := by
  have h_split : HasSum (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) (jtpSeries) := by
    have h_summable : Summable (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) := by
      convert qSeries.FPS.summable_ab using 1
    convert h_summable.hasSum using 1
    rw [ show ( ∑' c : ℕ × ℕ, a_n c.1 * b_m c.2 ) = ( ∑' k : ℕ × ℕ, a_n ( k.2 + k.1 ) * b_m k.2 ) + ( ∑' k : ℕ × ℕ, a_n k.2 * b_m ( k.2 + k.1 + 1 ) ) from ?_ ]
    · rw [ hasSum_nonneg_part.tsum_eq, hasSum_neg_part.tsum_eq ]
      unfold jtpSeries z zinv; norm_num [ z_pow_eq, zinv_pow_eq ] 
    · rw [ ← Equiv.tsum_eq ( diagEquiv.symm ) ]
      rw [ Summable.tsum_sum ] ; aesop
      · convert summable_nonneg_diag using 1
      · convert summable_neg_diag using 1
  exact h_split

open LaurentPolynomial in
/-- jtpProd = jtpSeries via HasSum.mul, diagEquiv, and diagonal HasSum results. -/
theorem jacobiTripleProduct_fps : @jtpProd = @jtpSeries :=
  hasSum_ab_jtpProd.unique hasSum_ab_jtpSeries

end JTP

end qSeries.FPS

end