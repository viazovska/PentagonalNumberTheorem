/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import QSeries.EulerIdentities
import QSeries.JTP_KeyIdentity

/-!
# Core lemmas for the Jacobi triple product proof

The proof strategy: Show $(q;q)_∞ (-z;q)_∞ (-q/z;q)_∞ = g(z)$ by:
1. Dividing both sides by $(-q/z;q)_∞$ (nonzero for ‖q/z‖ < 1)
2. Showing $g(z) / (-q/z;q)_∞ = (q;q)_∞ (-z;q)_∞$
3. This follows from the Cauchy product and the Euler 2nd identity

Key identity: $(q;q)_∞ / (q;q)_n = (q^{n+1};q)_∞$ (telescoping)
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-- Telescoping factorisation: $(q;q)_\infty = (q;q)_n \cdot (q \cdot q^n; q)_\infty$. -/
theorem qPochhammerInf_eq_mul {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf q q = qPochhammer q q n * qPochhammerInf (q * q ^ n) q := by
  induction n with
  | zero => norm_num [ qPochhammer ]
  | succ n ih =>
      rw [ ih, qPochhammer_succ ]
      rw [ mul_assoc, qPochhammerInf_recursion ] ; ring
      grind

/-- Euler's second identity evaluated at $z = -q^{n+1}$, giving $(q^{n+1}; q)_\infty$. -/
theorem euler_second_at_neg_qpow {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * (-q ^ (n + 1)) ^ m / qPochhammer q q m)
      (qPochhammerInf (q ^ (n + 1)) q) := by
  convert euler_second_identity hq _ using 1
  · norm_num
  · simpa using pow_lt_one₀ ( norm_nonneg q ) hq ( by omega )

/-- The product $(q;q)_\infty (-z;q)_\infty$ equals $\sum_n q^{\binom{n}{2}} z^n (q^{n+1};q)_\infty$, via Euler's second identity. -/
theorem qPochhammerInf_prod_hasSum {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q)
      (qPochhammerInf q q * qPochhammerInf (-z) q) := by
  convert HasSum.mul_left ( qPochhammerInf q q ) ( euler_second_identity hq hz ) using 1
  ext n; rw [ qPochhammerInf_eq_mul hq n ] ; ring
  grind +suggestions

/-- Key identity: the n-th coefficient of the product (q;q)_∞ (-z;q)_∞
expanded using Euler 2nd, multiplied by (q;q)_∞, gives the JTP coefficient.
Specifically: qPochhammerInf (q * q^n) q = qPochhammerInf (q^(n+1)) q. -/
theorem qPochhammerInf_shift {q : ℂ} (n : ℕ) :
    qPochhammerInf (q * q ^ n) q = qPochhammerInf (q ^ (n + 1)) q := by
  congr 1; ring

/-- The Jacobi triple product identity at $q = 0$, verified directly. -/
theorem jacobiTripleProduct_zero {z : ℂ} (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    qPochhammerInf 0 0 * qPochhammerInf (-z) 0 * qPochhammerInf (-0 / z) 0 =
    (∑' k : ℕ, z ^ k * (0 : ℂ) ^ k.choose 2) +
    (∑' m : ℕ, z⁻¹ ^ (m + 1) * (0 : ℂ) ^ (m + 2).choose 2) := by
  norm_num [ qPochhammerInf ]
  rw [ tprod_eq_prod ]
  any_goals exact { 0 }
  · rw [ tsum_eq_sum, tsum_eq_single 0 ] <;> norm_num
    any_goals exact { 0, 1 }
    · norm_num [ Finset.sum_pair ]
    · exact fun n hn => Or.inr <| Nat.ne_of_gt <| Nat.choose_pos <| by omega
    · intro b hb; rcases b with ( _ | _ | b ) <;> simp_all +decide [ Nat.choose ] 
  · aesop

/-- Euler's second identity evaluated at $z = -q/z$, giving $(-q/z; q)_\infty$. -/
theorem euler_second_at_qoz {q z : ℂ} (hq : ‖q‖ < 1) (hzq : ‖q‖ < ‖z‖)
    (hz' : z ≠ 0) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)
      (qPochhammerInf (-q / z) q) := by
  convert euler_second_identity hq _ using 1
  rotate_left
  rw [ neg_div ]
  · simpa [ hz' ] using div_lt_one ( norm_pos_iff.mpr hz' ) |>.2 hzq
  · exact funext fun n => by ring

set_option maxHeartbeats 800000 in
/-- The Jacobi triple product identity in the annulus $\|q\| < \|z\| < 1$. -/
theorem jacobiTripleProduct_annulus {q z : ℂ} (hq : ‖q‖ < 1)
    (hzq : ‖q‖ < ‖z‖) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q =
    (∑' k : ℕ, z ^ k * q ^ k.choose 2) +
    (∑' m : ℕ, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2) := by
  have hPQ : (qPochhammerInf q q * qPochhammerInf (-z) q) * qPochhammerInf (-q / z) q =
    (∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) *
    (∑' m : ℕ, q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
      congr 1
      · exact HasSum.tsum_eq ( qPochhammerInf_prod_hasSum hq hz ) ▸ rfl
      · convert ( euler_second_at_qoz hq hzq hz' ).tsum_eq.symm using 1
  have h_fubini : (∑' (n : ℕ), q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) *
    (∑' (m : ℕ), q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) = ∑' (p : ℕ × ℕ), q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q * (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) := by
      rw [ Summable.tsum_prod ]
      · simp +decide only [tsum_mul_left, tsum_mul_right]
      · have h_summable : Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) ∧ Summable (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
          constructor
          · convert qPochhammerInf_prod_hasSum hq hz |> HasSum.summable using 1
          · convert euler_second_at_qoz hq hzq hz' |> HasSum.summable using 1
        exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.1.norm ) ( h_summable.2.norm ) 
  have h_split : ∑' (p : ℕ × ℕ), q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q * (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) =
    ∑' (k : ℕ), ∑' (m : ℕ), q ^ (m + k).choose 2 * z ^ (m + k) * qPochhammerInf (q * q ^ (m + k)) q * (q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) +
    ∑' (l : ℕ), ∑' (n : ℕ), q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q * (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) * z⁻¹ ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1))) := by
      have h_split : ∀ {f : ℕ × ℕ → ℂ}, Summable f → ∑' (p : ℕ × ℕ), f p = ∑' (k : ℕ), ∑' (m : ℕ), f (m + k, m) + ∑' (l : ℕ), ∑' (n : ℕ), f (n, n + (l + 1)) := by
        intros f hf
        have h_split : ∑' (p : ℕ × ℕ), f p = ∑' (p : ℕ × ℕ), f (p.1 + p.2, p.2) + ∑' (p : ℕ × ℕ), f (p.1, p.1 + p.2 + 1) := by
          have h_split : ∑' (p : ℕ × ℕ), f p = ∑' (p : ℕ × ℕ), f (p.1 + p.2, p.2) + ∑' (p : ℕ × ℕ), f (p.1, p.1 + p.2 + 1) := by
            have h_partition : ∀ p : ℕ × ℕ, p.1 ≥ p.2 ↔ ∃ m n : ℕ, p = (m + n, n) := by
              exact fun p => ⟨ fun hp => ⟨ p.1 - p.2, p.2, by simp +decide [ Nat.sub_add_cancel hp ] ⟩, by rintro ⟨ m, n, rfl ⟩ ; simp +decide ⟩
            have h_partition' : ∀ p : ℕ × ℕ, p.1 < p.2 ↔ ∃ m n : ℕ, p = (m, m + n + 1) := by
              exact fun p => ⟨ fun hp => ⟨ p.1, p.2 - p.1 - 1, by ext <;> norm_num ; omega ⟩, by rintro ⟨ m, n, rfl ⟩ ; simp +decide ⟩
            have h_split : ∑' (p : ℕ × ℕ), f p = ∑' (p : ℕ × ℕ), f p * (if p.1 ≥ p.2 then 1 else 0) + ∑' (p : ℕ × ℕ), f p * (if p.1 < p.2 then 1 else 0) := by
              rw [ ← Summable.tsum_add ] ; congr ; ext p ; split_ifs <;> ring <;> omega
              · exact Summable.of_norm <| by simpa using hf.norm.of_nonneg_of_le ( fun p => by positivity ) fun p => by split_ifs <;> norm_num
              · exact Summable.of_norm <| by simpa using hf.norm.of_nonneg_of_le ( fun p => by positivity ) fun p => by split_ifs <;> norm_num
            convert h_split using 2
            · rw [ ← tsum_eq_tsum_of_ne_zero_bij ]
              use fun p => ( p.val.1 + p.val.2, p.val.2 )
              · norm_num [ Function.Injective ]
                intros; omega
              · intro p hp; specialize h_partition p; aesop
              · simp +decide [ h_partition ]
            · rw [ ← tsum_eq_tsum_of_ne_zero_bij ]
              use fun x => ( x.val.1, x.val.1 + x.val.2 + 1 )
              · norm_num [ Function.Injective ]
                intros; omega
              · intro p hp; specialize h_partition' p; aesop
              · simp +decide [ Nat.lt_succ_iff ]
          exact h_split
        convert h_split using 1
        erw [ Summable.tsum_prod, Summable.tsum_prod ]
        · simp +decide only [add_comm, add_assoc]
          rw [ ← Summable.tsum_comm ]
          convert hf.comp_injective ( show Function.Injective ( fun p : ℕ × ℕ => ( p.2, p.2 + ( p.1 + 1 ) ) ) from fun p q h => by aesop ) using 1
        · convert hf.comp_injective ( show Function.Injective ( fun p : ℕ × ℕ => ( p.1, p.1 + p.2 + 1 ) ) from fun p q h => by aesop ) using 1
        · convert hf.comp_injective ( show Function.Injective ( fun p : ℕ × ℕ => ( p.1 + p.2, p.2 ) ) from fun p q h => by aesop ) using 1
      apply h_split
      have h_summable : Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) ∧ Summable (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
        constructor
        · convert qPochhammerInf_prod_hasSum hq hz |> HasSum.summable using 1
        · convert euler_second_at_qoz hq hzq hz' |> HasSum.summable using 1
      exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.1.norm ) ( h_summable.2.norm ) 
  nontriviality
  have h_cauchy : ∀ k : ℕ, ∑' (m : ℕ), q ^ (m + k).choose 2 * z ^ (m + k) * qPochhammerInf (q * q ^ (m + k)) q * (q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) = z ^ k * q ^ k.choose 2 := by
    intro k
    have := cauchy_coeff_nonneg hq k
    simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_add, pow_mul, tsum_mul_left, tsum_mul_right ]
    rw [ ← this.tsum_eq, ← tsum_mul_left ] ; congr ; ext m ; ring
  have h_cauchy_neg : ∀ l : ℕ, ∑' (n : ℕ), q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q * (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) * z⁻¹ ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1))) = z⁻¹ ^ (l + 1) * q ^ (l + 2).choose 2 := by
    intro l
    have := cauchy_coeff_neg hq l
    simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_add, pow_mul, tsum_mul_left, tsum_mul_right ]
    rw [ ← this.tsum_eq ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left ] ; ring
    refine tsum_congr fun n => ?_ ; by_cases hn : n = 0 <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ]
  aesop

end

end qSeries