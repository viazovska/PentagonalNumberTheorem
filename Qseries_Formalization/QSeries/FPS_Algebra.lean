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
    qPoch (X : R⟦X⟧) k * qPochInv (R := R) k = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simpa using constantCoeff_qPoch_X (R := R) k)

/-- The formal power series inverse of `qPoch X k` times `qPoch X k` equals 1. -/
@[simp]
theorem qPochInv_mul_qPoch (k : ℕ) :
    qPochInv (R := R) k * qPoch (X : R⟦X⟧) k = 1 := by
  rw [mul_comm, qPoch_mul_qPochInv]

/-- The recursion `(1 - X^{k+1}) * qPochInv(k+1) = qPochInv(k)` for the inverse
q-Pochhammer symbol. -/
theorem qPochInv_succ_mul (k : ℕ) :
    (1 - (X : R⟦X⟧) ^ (k + 1)) * qPochInv (R := R) (k + 1) = qPochInv k := by
  have h1 := qPoch_mul_qPochInv (R := R) (k + 1)
  rw [qPoch_succ, ← pow_succ'] at h1
  refine (isUnit_qPoch_X (R := R) k).mul_left_cancel ?_
  rw [qPoch_mul_qPochInv, ← mul_assoc, h1]

/-- `qPochInf X` is a unit. -/
theorem isUnit_qqInf : IsUnit (qPochInf (X : R⟦X⟧)) :=
  isUnit_qPochInf X (by simp)

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

/-- `qPochInf X * qPochInv n = qPochInf (X * X^n)`: multiplying the infinite product by
the `n`-th inverse Pochhammer symbol shifts the argument. -/
theorem qqInf_mul_qPochInv (n : ℕ) :
    qPochInf (X : R⟦X⟧) * qPochInv (R := R) n = qPochInf (X * X ^ n) := by
  rw [qqInf_eq_qPoch_mul n, mul_right_comm, qPoch_mul_qPochInv, one_mul]


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
  have h2 : (l + 2).choose 2 = (l + 1).choose 2 + (l + 1) := choose2_step (l + 1)
  linarith


section Euler2

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Every nonconstant term of a finite q-Pochhammer product is divisible by `a`:
`(a; X)_k = 1 + a * g` for some `g`. -/
private theorem aux_fpsalg_a_qPoch_eq_one_add (a : R⟦X⟧) (k : ℕ) :
    ∃ g : R⟦X⟧, qPoch a k = 1 + a * g := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨g - X ^ k - a * g * X ^ k, by rw [qPoch_succ, hg]; ring⟩

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- For `j ≤ m` the `j`-th coefficient of `(X·X^m; X)_k` agrees with that of `1`. -/
private theorem aux_fpsalg_a_coeff_qPoch_X_pow (m k : ℕ) {j : ℕ} (hj : j < m + 1) :
    PowerSeries.coeff j (qPoch ((X : R⟦X⟧) * X ^ m) k) = PowerSeries.coeff j 1 := by
  obtain ⟨g, hg⟩ := aux_fpsalg_a_qPoch_eq_one_add ((X : R⟦X⟧) * X ^ m) k
  rw [hg, map_add, ← pow_succ', PowerSeries.coeff_X_pow_mul', if_neg hj.not_ge, add_zero]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Telescoping split `(X; X)_n = (X; X)_{n-k} · (X·X^{n-k}; X)_k` for `k ≤ n`. -/
private theorem aux_fpsalg_a_qPoch_split {k n : ℕ} (hkn : k ≤ n) :
    qPoch (X : R⟦X⟧) n =
      qPoch (X : R⟦X⟧) (n - k) * qPoch ((X : R⟦X⟧) * X ^ (n - k)) k := by
  conv_lhs => rw [show n = n - k + k from (Nat.sub_add_cancel hkn).symm]
  rw [qPoch, qPoch, qPoch, Finset.prod_range_add]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by ring)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Two power series agreeing in all coefficients below `N` still agree there after
multiplication by a common factor. -/
private theorem aux_fpsalg_a_coeff_mul_congr {f g b : R⟦X⟧} {N j : ℕ} (hj : j < N)
    (h : ∀ i < N, PowerSeries.coeff i f = PowerSeries.coeff i g) :
    PowerSeries.coeff j (f * b) = PowerSeries.coeff j (g * b) := by
  have hd : (X : R⟦X⟧) ^ N ∣ f - g :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi => by rw [map_sub, h i hi, sub_self]
  have hj0 := PowerSeries.X_pow_dvd_iff.mp (hd.mul_right b) j hj
  rwa [sub_mul, map_sub, sub_eq_zero] at hj0

/-- `k ≤ C(k,2) + 1`. -/
private lemma aux_fpsalg_a_le_choose2 (k : ℕ) : k ≤ k.choose 2 + 1 := by
  induction k with
  | zero => omega
  | succ k ih => rw [choose2_step]; omega

/-- `C(k,2)` eventually dominates: `d < C(k,2)` as soon as `d + 2 ≤ k`. -/
private lemma aux_fpsalg_a_lt_choose2 {d k : ℕ} (hk : d + 2 ≤ k) : d < k.choose 2 := by
  have := aux_fpsalg_a_le_choose2 k
  omega

/-- For `j + k ≤ n`, the `j`-th coefficient of `qBinom n k X` equals that of `qPochInv k`. -/
theorem coeff_qBinom_eq_qPochInv {k j n : ℕ} (hjk : j + k ≤ n) :
    PowerSeries.coeff j (qSeries.qBinom n k (X : R⟦X⟧)) =
    PowerSeries.coeff j (qPochInv (R := R) k) := by
  have hkn : k ≤ n := by omega
  have h_eq : qSeries.qBinom n k (X : R⟦X⟧) * qPoch (X : R⟦X⟧) k *
      qPoch (X : R⟦X⟧) (n - k) = qPoch (X : R⟦X⟧) n :=
    qSeries.qBinom_mul_qPochhammer_mul_qPochhammer (X : R⟦X⟧) hkn
  have hcancel : qSeries.qBinom n k (X : R⟦X⟧) * qPoch (X : R⟦X⟧) k
      = qPoch ((X : R⟦X⟧) * X ^ (n - k)) k := by
    refine (isUnit_qPoch_X (R := R) (n - k)).mul_right_cancel ?_
    rw [h_eq, aux_fpsalg_a_qPoch_split hkn]
    exact mul_comm _ _
  have hdvd : (X : R⟦X⟧) ^ (n - k + 1) ∣
      qSeries.qBinom n k (X : R⟦X⟧) - qPochInv (R := R) k := by
    refine (IsUnit.dvd_mul_right (isUnit_qPoch_X (R := R) k)).mp ?_
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [sub_mul, hcancel, qPochInv_mul_qPoch, map_sub,
      aux_fpsalg_a_coeff_qPoch_X_pow _ _ hm, sub_self]
  rw [← sub_eq_zero, ← map_sub]
  exact PowerSeries.X_pow_dvd_iff.mp hdvd j (by omega)

omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem qPoch_neg_eq_sum (a : R⟦X⟧) (n : ℕ) :
    qPoch (-a) n = ∑ k ∈ Finset.range (n + 1),
      X ^ k.choose 2 * qSeries.qBinom n k (X : R⟦X⟧) * a ^ k := by
  rw [qPoch, ← qSeries.qBinom_finite_thm (X : R⟦X⟧) a n]
  exact Finset.prod_congr rfl fun _ _ => by ring

omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem euler2_coeff_vanish (a : R⟦X⟧) (d k : ℕ) (hk : d < k.choose 2) :
    PowerSeries.coeff d (X ^ k.choose 2 * a ^ k * qPochInv (R := R) k) = 0 := by
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg hk.not_ge]

omit [DiscreteTopology R] in
/-- The Euler-second summands `X^{C(k,2)} · a^k · (X; X)_k⁻¹` form a summable family. -/
private theorem aux_fpsalg_a_summable_euler2 (a : R⟦X⟧) :
    Summable fun k : ℕ => (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochInv (R := R) k := by
  refine (WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  refine summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun k hk => ?_
  exact euler2_coeff_vanish a d k (aux_fpsalg_a_lt_choose2 (by simpa using hk))

/-- Termwise agreement, in degree `n`, between the finite q-binomial expansion of
`(-a; X)_{n+1}` and the Euler-second summands. -/
private theorem aux_fpsalg_a_coeff_term_eq (a : R⟦X⟧) (n k : ℕ) :
    PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * qSeries.qBinom (n + 1) k X * a ^ k) =
      PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochInv (R := R) k) := by
  rw [mul_assoc, show (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochInv (R := R) k
      = X ^ k.choose 2 * (qPochInv (R := R) k * a ^ k) from by ring,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · refine aux_fpsalg_a_coeff_mul_congr (N := n - k.choose 2 + 1) (by omega) fun i hi => ?_
    exact coeff_qBinom_eq_qPochInv (by have := aux_fpsalg_a_le_choose2 k; omega)
  · rfl

/-- FPS Euler second identity: `qPochInf(-a) = Σ_{k≥0} X^{C(k,2)} · a^k · (qPoch X k)⁻¹`
in `R⟦X⟧`. -/
theorem fps_euler_second (a : R⟦X⟧) :
    qPochInf (-a) = ∑' k : ℕ, X ^ k.choose 2 * a ^ k * qPochInv (R := R) k := by
  ext n
  have hcoeff :
      ∑' k : ℕ, PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochInv (R := R) k)
        = PowerSeries.coeff n
            (∑' k : ℕ, (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochInv (R := R) k) :=
    ((aux_fpsalg_a_summable_euler2 a).hasSum.map
      (PowerSeries.coeff n).toAddMonoidHom (WithPiTopology.continuous_coeff R n)).tsum_eq
  rw [coeff_qPochInf, qPoch_neg_eq_sum, ← hcoeff,
    tsum_eq_sum (s := Finset.range (n + 2)) fun k hk =>
      euler2_coeff_vanish a n k (aux_fpsalg_a_lt_choose2 (by simpa using hk)),
    map_sum]
  exact Finset.sum_congr rfl fun k _ => aux_fpsalg_a_coeff_term_eq a n k

end Euler2


section KeyIdentity

omit [DiscreteTopology R] in
/-- A family `m ↦ X ^ e m * g m` in `R⟦X⟧` is summable as soon as the exponents `e m`
eventually exceed every fixed degree: only finitely many terms contribute to each
coefficient. -/
theorem aux_fpsalg_b_summable_X_pow_mul {e : ℕ → ℕ}
    (he : ∀ d : ℕ, ∃ N : ℕ, ∀ m ≥ N, d < e m) (g : ℕ → R⟦X⟧) :
    Summable fun m : ℕ => (X : R⟦X⟧) ^ e m * g m := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  obtain ⟨N, hN⟩ := he d
  refine summable_of_ne_finset_zero (s := Finset.range N) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by have := hN m hm; omega)]

/-- The exponents `m * (m + k)` eventually exceed every fixed degree. -/
private theorem aux_fpsalg_b_exponent_mul (k d : ℕ) : ∃ N : ℕ, ∀ m ≥ N, d < m * (m + k) :=
  ⟨d + 1, fun m hm => lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right m (by omega))⟩

/-- The exponents `C(m, 2)` eventually exceed every fixed degree. -/
private theorem aux_fpsalg_b_exponent_choose_two (d : ℕ) :
    ∃ N : ℕ, ∀ m ≥ N, d < m.choose 2 := by
  refine ⟨d + 2, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [choose2_step]
  omega

/-- The key sum `S_k = ∑_m X^{m(m+k)} / ((X;X)_m (X;X)_{m+k})`. -/
def S_fps (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k)

omit [DiscreteTopology R] in
/-- The defining series for `S_fps k` is summable in `R⟦X⟧`. -/
theorem summable_S_fps (k : ℕ) :
    Summable (fun m : ℕ => X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k)) := by
  simpa [mul_assoc] using aux_fpsalg_b_summable_X_pow_mul (R := R)
    (aux_fpsalg_b_exponent_mul k) fun m => qPochInv m * qPochInv (m + k)

/-- Key auxiliary: `qPochInv(n-1) + X^n * qPochInv(n) = qPochInv(n)`.
    Equivalently, `(1 - X^{n+1}) * qPochInv(n+1) + X^{n+1} * qPochInv(n+1) = qPochInv(n+1)`. -/
private theorem qPochInv_split (n : ℕ) :
    qPochInv (R := R) n + X ^ (n + 1) * qPochInv (R := R) (n + 1) =
    qPochInv (R := R) (n + 1) := by
  rw [← qPochInv_succ_mul (R := R) n]; ring

/-- The intermediate sum `T_k = ∑ m, X^{m(m+k)} * qPochInv(m) * qPochInv(m+k+1)`. -/
private def T_fps (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k + 1)

omit [DiscreteTopology R] in
private theorem summable_T_fps (k : ℕ) :
    Summable (fun m : ℕ => X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k + 1)) := by
  simpa [mul_assoc] using aux_fpsalg_b_summable_X_pow_mul (R := R)
    (aux_fpsalg_b_exponent_mul k) fun m => qPochInv m * qPochInv (m + k + 1)

private theorem T_eq_S_add (k : ℕ) :
    T_fps (R := R) k = S_fps k + X ^ (k + 1) * S_fps (k + 1) := by
  unfold T_fps S_fps
  rw [← Summable.tsum_mul_left _ (summable_S_fps (R := R) (k + 1)),
    ← Summable.tsum_add (summable_S_fps (R := R) k)
      (Summable.mul_left _ (summable_S_fps (R := R) (k + 1)))]
  refine tsum_congr fun m => ?_
  simp only [← add_assoc]
  have hpow : (X : R⟦X⟧) ^ (k + 1) * X ^ (m * (m + k + 1)) =
      X ^ (m + k + 1) * X ^ (m * (m + k)) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [← qPochInv_succ_mul (R := R) (m + k), ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)),
    ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)), hpow]
  generalize (X : R⟦X⟧) ^ (m * (m + k)) = A
  ring

/-- The shifted form of `X^{k+1} · S_{k+2}` as a `HasSum` statement. -/
private theorem aux_fpsalg_b_hasSum_shift (k : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ ((n + 1) * (n + 1 + k)) * qPochInv (R := R) n * qPochInv (n + k + 2))
      (X ^ (k + 1) * S_fps (R := R) (k + 2)) := by
  have hfun : (fun n : ℕ => (X : R⟦X⟧) ^ (k + 1) *
      (X ^ (n * (n + (k + 2))) * qPochInv (R := R) n * qPochInv (n + (k + 2)))) =
      fun n : ℕ => X ^ ((n + 1) * (n + 1 + k)) * qPochInv (R := R) n * qPochInv (n + k + 2) := by
    funext n
    rw [show n + (k + 2) = n + k + 2 from by omega,
      show (n + 1) * (n + 1 + k) = k + 1 + n * (n + k + 2) from by ring, pow_add]
    ring
  exact hfun ▸ (summable_S_fps (R := R) (k + 2)).hasSum.mul_left _

private theorem X_mul_S_shift (k : ℕ) :
    X ^ (k + 1) * S_fps (R := R) (k + 2) =
    ∑' n : ℕ, X ^ ((n + 1) * (n + 1 + k)) * qPochInv (R := R) n * qPochInv (n + k + 2) :=
  (aux_fpsalg_b_hasSum_shift k).tsum_eq.symm

private theorem T_eq_S_add' (k : ℕ) :
    T_fps (R := R) k = S_fps (k + 1) + X ^ (k + 1) * S_fps (k + 2) := by
  have hA := (hasSum_nat_add_iff' (f := fun m : ℕ =>
    X ^ (m * (m + (k + 1))) * qPochInv (R := R) m * qPochInv (m + (k + 1))) 1).mpr
      (summable_S_fps (R := R) (k + 1)).hasSum
  refine HasSum.tsum_eq ((hasSum_nat_add_iff' 1).mp ?_)
  convert hA.add (aux_fpsalg_b_hasSum_shift (R := R) k) using 1
  · funext n
    rw [show n + 1 + k + 1 = n + k + 2 from by omega,
      show n + 1 + (k + 1) = n + k + 2 from by omega,
      show (n + 1) * (n + k + 2) = (n + 1) * (n + 1 + k) + (n + 1) from by ring, pow_add]
    conv_lhs => rw [← qPochInv_split (R := R) n]
    ring
  · simp only [S_fps, Finset.sum_range_one, Nat.zero_mul, Nat.zero_add, pow_zero, one_mul]
    ring

/-- The recurrence: `S_k − S_{k+1} = X^{k+1} (S_{k+2} − S_{k+1})`. -/
theorem S_fps_recurrence (k : ℕ) :
    S_fps (R := R) k - S_fps (k + 1) =
    X ^ (k + 1) * (S_fps (R := R) (k + 2) - S_fps (k + 1)) := by
  have h := (T_eq_S_add (R := R) k).symm.trans (T_eq_S_add' k)
  rw [mul_sub, sub_eq_sub_iff_add_eq_add]
  exact h.trans (add_comm _ _)

/-- `S_fps k` is independent of `k`: all values are equal to `S_fps 0`. -/
theorem S_fps_const (k : ℕ) : S_fps (R := R) k = S_fps 0 := by
  -- `S_j - S_{j+1}` is divisible by `X ^ N` for every `N`, hence zero.
  have key : ∀ N j : ℕ, ∃ g : R⟦X⟧, S_fps (R := R) j - S_fps (j + 1) = X ^ N * g := by
    intro N
    induction N with
    | zero => exact fun j => ⟨_, (one_mul _).symm⟩
    | succ N ih =>
      intro j
      obtain ⟨g, hg⟩ := ih (j + 1)
      refine ⟨-(X ^ j * g), ?_⟩
      rw [S_fps_recurrence j, ← neg_sub (S_fps (R := R) (j + 1)), hg]
      ring
  have hzero : ∀ j : ℕ, S_fps (R := R) j = S_fps (j + 1) := by
    intro j
    rw [← sub_eq_zero]
    ext d
    obtain ⟨g, hg⟩ := key (d + 1) j
    rw [hg, PowerSeries.coeff_X_pow_mul', if_neg (by omega), map_zero]
  induction k with
  | zero => rfl
  | succ k ih => rw [← hzero k, ih]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Every finite q-Pochhammer product is `1` plus a multiple of its argument. -/
private theorem aux_fpsalg_b_qPoch_eq_one_add (a : R⟦X⟧) (n : ℕ) :
    ∃ g : R⟦X⟧, qPoch a n = 1 + a * g := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨g - X ^ n - a * g * X ^ n, by rw [qPoch_succ, hg]; ring⟩

/-- Below degree `k + 1` the series `(X·X^k; X)_∞` is indistinguishable from `1`. -/
private theorem aux_fpsalg_b_coeff_qPochInf_X_pow {k j : ℕ} (hj : j < k + 1) :
    PowerSeries.coeff j (qPochInf ((X : R⟦X⟧) * X ^ k)) = PowerSeries.coeff j 1 := by
  obtain ⟨g, hg⟩ := aux_fpsalg_b_qPoch_eq_one_add ((X : R⟦X⟧) * X ^ k) (j + 1)
  rw [coeff_qPochInf, hg, map_add, ← pow_succ', PowerSeries.coeff_X_pow_mul',
    if_neg hj.not_ge, add_zero]

/-- For `d < k`, the `d`-th coefficient of `qPochInv k` equals the `d`-th coefficient of `qqInv`. -/
theorem coeff_qPochInv_eq_qqInv {k d : ℕ} (hkd : d < k) :
    PowerSeries.coeff d (qPochInv (R := R) k) = PowerSeries.coeff d (qqInv (R := R)) := by
  have hQ : ∀ j < k, PowerSeries.coeff j
      (qPochInf (X : R⟦X⟧) * (qPochInv (R := R) k - qqInv (R := R))) = 0 := fun j hj => by
    rw [mul_sub, qqInf_mul_qPochInv, qqInf_mul_qqInv, map_sub, sub_eq_zero,
      aux_fpsalg_b_coeff_qPochInf_X_pow (by omega)]
  rw [← sub_eq_zero, ← map_sub, show qPochInv (R := R) k - qqInv (R := R) =
    qqInv (R := R) * (qPochInf (X : R⟦X⟧) * (qPochInv (R := R) k - qqInv)) from by
      rw [← mul_assoc, qqInv_mul_qqInf, one_mul], PowerSeries.coeff_mul]
  exact Finset.sum_eq_zero fun p hp => by
    rw [hQ p.2 (by have := Finset.mem_antidiagonal.mp hp; omega), mul_zero]

/-- Taking the `d`-th coefficient commutes with a convergent `tsum` in `R⟦X⟧`. -/
private theorem aux_fpsalg_b_coeff_tsum {f : ℕ → R⟦X⟧} (hf : Summable f) (d : ℕ) :
    PowerSeries.coeff d (∑' m, f m) = ∑' m, PowerSeries.coeff d (f m) :=
  ((hf.hasSum.map (PowerSeries.coeff d).toAddMonoidHom
    (WithPiTopology.continuous_coeff R d)).tsum_eq).symm

/-- `qPochInv 0 = 1`. -/
private theorem aux_fpsalg_b_qPochInv_zero : qPochInv (R := R) 0 = 1 := by
  simpa using qPoch_mul_qPochInv (R := R) 0

/-- For `d < k`, the `d`-th coefficient of `S_fps k` equals the `d`-th coefficient of `qqInv`. -/
theorem coeff_S_fps_eq_qqInv (k : ℕ) (d : ℕ) (hkd : d < k) :
    PowerSeries.coeff d (S_fps (R := R) k) = PowerSeries.coeff d (qqInv (R := R)) := by
  rw [S_fps, aux_fpsalg_b_coeff_tsum (summable_S_fps k), tsum_eq_single 0 fun m hm => by
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul',
      if_neg (by have := Nat.pos_of_ne_zero hm; nlinarith)]]
  simpa [aux_fpsalg_b_qPochInv_zero] using coeff_qPochInv_eq_qqInv (R := R) hkd

/-- **Key identity**: `S_k = (qPochInf X)⁻¹` for all `k ≥ 0`. -/
theorem fps_key_identity (k : ℕ) : S_fps (R := R) k = qqInv := by
  ext d
  rw [S_fps_const k, ← S_fps_const (R := R) (d + 1)]
  exact coeff_S_fps_eq_qqInv (d + 1) d (Nat.lt_succ_self d)

end KeyIdentity


section Cauchy

/-- `qPochInf X * qPochInf(-a) = Σ_n X^{C(n,2)} a^n qPochInf(X · X^n)` in `R⟦X⟧`. -/
theorem qqInf_mul_euler2 (a : R⟦X⟧) :
    qPochInf (X : R⟦X⟧) * qPochInf (-a) =
    ∑' n : ℕ, X ^ n.choose 2 * a ^ n * qPochInf (X * X ^ n) := by
  have hs : Summable fun n : ℕ => X ^ n.choose 2 * a ^ n * qPochInv (R := R) n := by
    simpa [mul_assoc] using aux_fpsalg_b_summable_X_pow_mul (R := R)
      aux_fpsalg_b_exponent_choose_two fun n => a ^ n * qPochInv n
  rw [fps_euler_second a, ← Summable.tsum_mul_left _ hs]
  exact tsum_congr fun n => by rw [← qqInf_mul_qPochInv n]; ring

/-- The common core of the two Cauchy diagonal computations: after collecting the powers of `X`
the diagonal is `X ^ e` times the key sum `S_k`, and `S_k = qqInv` cancels `qPochInf X`. -/
private theorem aux_fpsalg_b_cauchy_core (k e : ℕ) :
    HasSum (fun m : ℕ => X ^ (e + m * (m + k)) * qPochInf (X : R⟦X⟧) *
      qPochInv (R := R) m * qPochInv (m + k)) (X ^ e : R⟦X⟧) := by
  have h : HasSum (fun m : ℕ => X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k))
      (qqInv (R := R)) := by
    rw [← fps_key_identity (R := R) k]
    exact (summable_S_fps k).hasSum
  have key := h.mul_left ((X : R⟦X⟧) ^ e * qPochInf X)
  rw [mul_assoc, qqInf_mul_qqInv, mul_one] at key
  have hfun : (fun m : ℕ => (X : R⟦X⟧) ^ e * qPochInf X *
      (X ^ (m * (m + k)) * qPochInv (R := R) m * qPochInv (m + k))) =
      fun m : ℕ => X ^ (e + m * (m + k)) * qPochInf (X : R⟦X⟧) *
        qPochInv (R := R) m * qPochInv (m + k) := by
    funext m; rw [pow_add]; ring
  exact hfun ▸ key

/-- Cauchy diagonal coefficient for non-negative index `k`: the `(m+k, m)` diagonal of the
double series sums to `X^{C(k,2)}` in `R⟦X⟧`. -/
theorem cauchy_coeff_nonneg (k : ℕ) :
    HasSum (fun m : ℕ =>
      X ^ (m + k).choose 2 * qPochInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochInv (R := R) m))
      (X ^ k.choose 2 : R⟦X⟧) := by
  convert aux_fpsalg_b_cauchy_core (R := R) k (k.choose 2) using 1
  funext m
  rw [← qqInf_mul_qPochInv (m + k), ← choose2_add m k]
  ring

/-- Cauchy diagonal coefficient for negative index `-(l+1)`: the `(n, n+l+1)` diagonal of the
double series sums to `X^{C(l+2,2)}` in `R⟦X⟧`. -/
theorem cauchy_coeff_neg (l : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ n.choose 2 * qPochInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochInv (R := R) (n + (l + 1))))
      (X ^ (l + 2).choose 2 : R⟦X⟧) := by
  convert aux_fpsalg_b_cauchy_core (R := R) (l + 1) ((l + 2).choose 2) using 1
  funext n
  rw [← qqInf_mul_qPochInv n, ← choose2_add' n l]
  ring

end Cauchy


section JTP

private theorem jtpProd_expand :
    @jtpProd = (∑' n : ℕ, X ^ n.choose 2 * z ^ n * qPochInf (X * X ^ n)) *
              (∑' m : ℕ, X ^ (m.choose 2 + m) * zinv ^ m * qPochInv m) := by
  convert congr_arg₂ (· * ·) (qqInf_mul_euler2 z) _ using 1
  convert fps_euler_second (X * zinv) using 1
  · exact tprod_congr fun _ => by ring
  · simp +decide [pow_add, mul_pow, mul_assoc, mul_comm, mul_left_comm]

open LaurentPolynomial in
/-- `z * zinv = 1` in `A⟦X⟧`. -/
private theorem z_mul_zinv : z * zinv = 1 := by
  rw [← map_mul, ← T_add]
  simp

open LaurentPolynomial in
/-- `z ^ n * zinv ^ n = 1` for all `n`. -/
private theorem z_pow_mul_zinv_pow (n : ℕ) : z ^ n * zinv ^ n = 1 := by
  rw [← mul_pow, z_mul_zinv, one_pow]

open LaurentPolynomial in
/-- `z ^ n = PS (T n)` for natural `n`. -/
private theorem z_pow_eq (n : ℕ) :
    z ^ n = (PowerSeries.C : LaurentPolynomial ℂ →+* _) (T (n : ℤ)) := by
  rw [← map_pow]
  congr 1
  simp

open LaurentPolynomial in
/-- `zinv ^ (m + 1) = PS (T (-(↑m + 1)))`. -/
private theorem zinv_pow_eq (m : ℕ) :
    zinv ^ (m + 1) = (PowerSeries.C : LaurentPolynomial ℂ →+* _) (T (-(↑m + 1))) := by
  rw [← map_pow]
  congr 1
  rw [T_pow]
  push_cast
  ring_nf

open LaurentPolynomial in
/-- Cancelling `zinv ^ m` against the first `m` factors of `z ^ (m + k)`. -/
private theorem z_pow_add_mul_zinv_pow (m k : ℕ) : z ^ (m + k) * zinv ^ m = z ^ k := by
  rw [pow_add, mul_right_comm, z_pow_mul_zinv_pow, one_mul]

open LaurentPolynomial in
/-- Cancelling `z ^ n` against the first `n` factors of `zinv ^ (n + l)`. -/
private theorem zinv_pow_add_mul_z_pow (n l : ℕ) : zinv ^ (n + l) * z ^ n = zinv ^ l := by
  rw [pow_add, mul_right_comm, mul_comm (zinv ^ n) (z ^ n), z_pow_mul_zinv_pow, one_mul]

open LaurentPolynomial in
/-- Non-negative diagonal of the Cauchy product: HasSum giving `z^k * X^{C(k,2)}`. -/
private theorem nonneg_diag_hasSum (k : ℕ) :
    HasSum (fun m : ℕ =>
      (X ^ (m + k).choose 2 * z ^ (m + k) * qPochInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * zinv ^ m * qPochInv m))
      (z ^ k * X ^ k.choose 2) := by
  have key : ∀ m : ℕ, (X ^ (m + k).choose 2 * z ^ (m + k) * qPochInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * zinv ^ m * qPochInv (R := LaurentPolynomial ℂ) m) =
      z ^ k * (X ^ (m + k).choose 2 * qPochInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochInv m)) := fun m => by
    rw [← z_pow_add_mul_zinv_pow m k]
    ring
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
  have key : ∀ n : ℕ, (X ^ n.choose 2 * z ^ n * qPochInf (X * X ^ n)) *
      (X ^ ((n + (l + 1)).choose 2 + (n + (l + 1))) * zinv ^ (n + (l + 1)) *
      qPochInv (R := LaurentPolynomial ℂ) (n + (l + 1))) =
      zinv ^ (l + 1) * (X ^ n.choose 2 * qPochInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochInv (n + (l + 1)))) := fun n => by
    rw [← zinv_pow_add_mul_z_pow n (l + 1)]
    ring
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
  right_inv := by
    intro s
    rcases s with ⟨k, m⟩ | ⟨l, n⟩ <;> simp
    omega

open LaurentPolynomial in
private abbrev a_n (n : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ n.choose 2 * z ^ n * qPochInf (X * X ^ n)

open LaurentPolynomial in
private abbrev b_m (m : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ (m.choose 2 + m) * zinv ^ m * qPochInv m

/-- If `d + 2 ≤ n` then `d < C(n, 2)`. -/
private theorem aux_fpsalg_c_lt_choose_two {d n : ℕ} (h : d + 2 ≤ n) : d < n.choose 2 := by
  rw [Nat.choose_two_right]
  refine Nat.lt_of_lt_of_le (Nat.lt_succ_self d) ((Nat.le_div_iff_mul_le two_pos).2 ?_)
  have h1 : d + 1 ≤ n - 1 := by omega
  nlinarith

open LaurentPolynomial in
/-- `a_n n` is divisible by `X ^ C(n, 2)`, so its lower coefficients vanish. -/
private theorem aux_fpsalg_c_coeff_a {d n : ℕ} (h : d < n.choose 2) :
    PowerSeries.coeff d (a_n n) = 0 := by
  rw [show a_n n = X ^ n.choose 2 * (z ^ n * qPochInf (X * X ^ n)) from by unfold a_n; ring,
    PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]

open LaurentPolynomial in
/-- `b_m m` is divisible by `X ^ (C(m, 2) + m)`, so its lower coefficients vanish. -/
private theorem aux_fpsalg_c_coeff_b {d m : ℕ} (h : d < m.choose 2 + m) :
    PowerSeries.coeff d (b_m m) = 0 := by
  rw [show b_m m = X ^ (m.choose 2 + m) * (zinv ^ m * qPochInv m) from by unfold b_m; ring,
    PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]

open LaurentPolynomial in
/-- `a_n i * b_m j` is divisible by `X ^ (C(i, 2) + (C(j, 2) + j))`. -/
private theorem aux_fpsalg_c_coeff_a_mul_b {d i j : ℕ}
    (h : d < i.choose 2 + (j.choose 2 + j)) :
    PowerSeries.coeff d (a_n i * b_m j) = 0 := by
  rw [show a_n i * b_m j = X ^ (i.choose 2 + (j.choose 2 + j)) *
      (z ^ i * qPochInf (X * X ^ i) * (zinv ^ j * qPochInv j)) from by unfold a_n b_m; ring,
    PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]

open LaurentPolynomial in
/-- The a_n sequence is summable. -/
private theorem summable_a : Summable a_n := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  exact aux_fpsalg_c_coeff_a (aux_fpsalg_c_lt_choose_two hn)

open LaurentPolynomial in
/-- The b_m sequence is summable. -/
private theorem summable_b : Summable b_m := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 1)) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  exact aux_fpsalg_c_coeff_b (by omega)

open LaurentPolynomial in
/-- The double product sequence is summable. -/
private theorem summable_ab :
    Summable (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 2) ×ˢ Finset.range (d + 1)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine aux_fpsalg_c_coeff_a_mul_b ?_
  rcases hp with h | h
  · have := aux_fpsalg_c_lt_choose_two h
    omega
  · omega

open LaurentPolynomial in
/-- HasSum for the double product giving jtpProd. -/
private theorem hasSum_ab_jtpProd :
    HasSum (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) jtpProd := by
  have h : jtpProd = ∑' p : ℕ × ℕ, a_n p.1 * b_m p.2 := by
    rw [jtpProd_expand]
    exact summable_a.hasSum.mul_eq summable_b.hasSum summable_ab.hasSum
  rw [h]
  exact summable_ab.hasSum

open LaurentPolynomial in
/-- The non-negative part of the theta series is summable. -/
private theorem summable_nonneg :
    Summable (fun k : ℕ => z ^ k * X ^ k.choose 2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  rw [mul_comm, PowerSeries.coeff_X_pow_mul', if_neg (aux_fpsalg_c_lt_choose_two hk).not_ge]

open LaurentPolynomial in
/-- The negative part of the theta series is summable. -/
private theorem summable_neg :
    Summable (fun l : ℕ => zinv ^ (l + 1) * X ^ (l + 2).choose 2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 1)) fun l hl => ?_
  rw [Finset.mem_range, not_lt] at hl
  rw [mul_comm, PowerSeries.coeff_X_pow_mul',
    if_neg (aux_fpsalg_c_lt_choose_two (show d + 2 ≤ l + 2 by omega)).not_ge]

open LaurentPolynomial in
/-- Summability of the non-negative diagonal rearrangement. -/
private theorem summable_nonneg_diag :
    Summable (fun p : ℕ × ℕ => a_n (p.2 + p.1) * b_m p.2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 2) ×ˢ Finset.range (d + 2)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine aux_fpsalg_c_coeff_a_mul_b ?_
  rcases hp with h | h
  · have := aux_fpsalg_c_lt_choose_two (show d + 2 ≤ p.2 + p.1 by omega)
    omega
  · omega

open LaurentPolynomial in
/-- Summability of the negative diagonal rearrangement. -/
private theorem summable_neg_diag :
    Summable (fun p : ℕ × ℕ => a_n p.2 * b_m (p.2 + p.1 + 1)) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 1) ×ˢ Finset.range (d + 1)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine aux_fpsalg_c_coeff_a_mul_b ?_
  rcases hp with h | h <;> omega

open LaurentPolynomial in
/-- Splitting a `HasSum` over `ℕ × ℕ` into the diagonals `(m + k, m)` and `(n, n + l + 1)`. -/
private theorem aux_fpsalg_c_hasSum_split_diag (f : ℕ × ℕ → (LaurentPolynomial ℂ)⟦X⟧)
    {a b : (LaurentPolynomial ℂ)⟦X⟧}
    (h1 : HasSum (fun p : ℕ × ℕ => f (p.2 + p.1, p.2)) a)
    (h2 : HasSum (fun p : ℕ × ℕ => f (p.2, p.2 + p.1 + 1)) b) :
    HasSum f (a + b) :=
  diagEquiv.symm.hasSum_iff.mp (h1.sum h2)

open LaurentPolynomial in
/-- A family indexed by `ℕ × ℕ` sums to the sum of its row sums. -/
private theorem aux_fpsalg_c_hasSum_of_rows {f : ℕ × ℕ → (LaurentPolynomial ℂ)⟦X⟧}
    {g : ℕ → (LaurentPolynomial ℂ)⟦X⟧} (hf : Summable f)
    (hrow : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m)) (g k)) :
    HasSum f (∑' k : ℕ, g k) := by
  rw [(hf.hasSum.prod_fiberwise hrow).tsum_eq]
  exact hf.hasSum

open LaurentPolynomial in
/-- HasSum for the non-negative diagonal (combined over all k). -/
private theorem hasSum_nonneg_part :
    HasSum (fun p : ℕ × ℕ => a_n (p.2 + p.1) * b_m p.2)
      (∑' k : ℕ, z ^ k * X ^ k.choose 2) :=
  aux_fpsalg_c_hasSum_of_rows summable_nonneg_diag nonneg_diag_hasSum

open LaurentPolynomial in
/-- HasSum for the negative diagonal (combined over all l). -/
private theorem hasSum_neg_part :
    HasSum (fun p : ℕ × ℕ => a_n p.2 * b_m (p.2 + p.1 + 1))
      (∑' l : ℕ, zinv ^ (l + 1) * X ^ (l + 2).choose 2) :=
  aux_fpsalg_c_hasSum_of_rows summable_neg_diag neg_diag_hasSum

open LaurentPolynomial in
/-- HasSum for the double product giving jtpSeries. -/
private theorem hasSum_ab_jtpSeries :
    HasSum (fun p : ℕ × ℕ => a_n p.1 * b_m p.2) jtpSeries := by
  have h : jtpSeries = (∑' k : ℕ, z ^ k * X ^ k.choose 2) +
      ∑' l : ℕ, zinv ^ (l + 1) * X ^ (l + 2).choose 2 := by
    unfold jtpSeries
    congr 1
    · exact tsum_congr fun n => by rw [z_pow_eq]
    · exact tsum_congr fun m => by rw [zinv_pow_eq]
  rw [h]
  exact aux_fpsalg_c_hasSum_split_diag _ hasSum_nonneg_part hasSum_neg_part

open LaurentPolynomial in
/-- jtpProd = jtpSeries via HasSum.mul, diagEquiv, and diagonal HasSum results. -/
theorem jacobiTripleProduct_fps : @jtpProd = @jtpSeries :=
  hasSum_ab_jtpProd.unique hasSum_ab_jtpSeries

end JTP

end qSeries.FPS

end
