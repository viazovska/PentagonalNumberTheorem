/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import QSeries.EulerIdentities
import QSeries.JTP_Core

/-!
# Jacobi triple product identity

The **Jacobi triple product identity** states that for $\|q\| < 1$ and $z \neq 0$:
$$(q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty
  = \sum_{k \in \mathbb{Z}} z^k \, q^{k(k-1)/2}.$$

## Proof strategy

The proof uses:
1. Both sides satisfy the functional equation $H(qz) = H(z)/z$.
2. The Euler identities (first and second) provide series expansions.
3. The Cauchy identity (`qBinom_infinite_thm`) relates the product to sums.
4. Extension from the annulus ‖q‖ < ‖z‖ < 1 to the full punctured disk.

## Main results

* `qSeries.jacobiTripleProduct` — the Jacobi triple product identity.
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-- Summability of the non-negative part $\sum_{k \geq 0} z^k q^{\binom{k}{2}}$. -/
theorem summable_jacobi_nonneg {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => z ^ k * q ^ k.choose 2) := by
  refine Summable.of_norm ?_
  simp +zetaDelta at *
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hq.le))
    (summable_geometric_of_lt_one (by positivity) hz)

/-- Summability of the negative-index part $\sum_{m \geq 0} z^{-(m+1)} q^{\binom{m+2}{2}}$ for $\|q\| < 1$ and $z \neq 0$. -/
theorem summable_jacobi_neg {q z : ℂ} (hq : ‖q‖ < 1) (hz' : z ≠ 0) :
    Summable (fun m : ℕ => (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2) := by
  refine summable_of_ratio_norm_eventually_le (r := ‖q‖ + (1 - ‖q‖) / 2) (by linarith) ?_
  · have h_eventually : ∃ N, ∀ n ≥ N, ‖q‖ ^ (n + 2) * ‖z⁻¹‖ ≤ (‖q‖ + (1 - ‖q‖) / 2) := by
      have h_eventually : Filter.Tendsto (fun n : ℕ => ‖q‖ ^ (n + 2) * ‖z⁻¹‖) Filter.atTop (nhds 0) := by
        simpa using Filter.Tendsto.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg q ) hq |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2 ) tendsto_const_nhds
      simpa using h_eventually.eventually ( ge_mem_nhds <| by linarith [ norm_nonneg q ] )
    simp_all +decide [ Nat.choose_succ_succ, pow_succ, mul_assoc, mul_comm ]
    obtain ⟨ N, hN ⟩ := h_eventually; use N; intro n hn; convert mul_le_mul_of_nonneg_left ( hN n hn ) ( by positivity : 0 ≤ ( ‖z‖ ^ n ) ⁻¹ * ‖q‖ ^ ( 1 + n + ( n + n.choose 2 ) ) ) using 1 ; ring
    ring

/-- The Jacobi triple product function
$f(z) = (q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty$. -/
def jacobiProd (q z : ℂ) : ℂ :=
  qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q

/-- The bilateral Jacobi series (non-negative part). -/
def jacobiBilateralPos (q z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ k * q ^ k.choose 2

/-- The bilateral Jacobi series (negative part).
For $k = -(m+1)$ with $m \geq 0$, the exponent is $\binom{m+2}{2} = (m+1)(m+2)/2$. -/
def jacobiBilateralNeg (q z : ℂ) : ℂ :=
  ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2

/-- The full bilateral Jacobi series. -/
def jacobiBilateral (q z : ℂ) : ℂ :=
  jacobiBilateralPos q z + jacobiBilateralNeg q z

/-- **Telescoping for $(-z;q)_\infty$**: $(-z;q)_\infty = (1+z)(-zq;q)_\infty$. -/
theorem neg_qPochhammerInf_recursion {z q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf (-z) q = (1 + z) * qPochhammerInf (-(z * q)) q := by
  have h := qPochhammerInf_recursion (z := -z) hq
  rw [show (1 : ℂ) - -z = 1 + z from by ring,
      show -z * q = -(z * q) from by ring] at h
  exact h

/-- The product satisfies $f(qz) = f(z)/z$ when $q \neq 0$ and $z \neq 0$. -/
theorem jacobiProd_fe {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0) (hz : z ≠ 0) :
    jacobiProd q (q * z) = jacobiProd q z / z := by
  unfold jacobiProd
  have hqz : q * z ≠ 0 := mul_ne_zero hq' hz
  have h1 := neg_qPochhammerInf_recursion (z := z) hq
  have h2 := neg_qPochhammerInf_recursion (z := z⁻¹) hq
  rw [show -(q * z) = -(z * q) from by ring]
  rw [show -q / (q * z) = -(z⁻¹) from by field_simp]
  rw [show -(z⁻¹ * q) = -q / z from by field_simp] at h2
  rw [h1, h2]
  have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  field_simp
  ring

/-- The bilateral Jacobi series satisfies the same functional equation $f(qz) = f(z)/z$ as the triple product. -/
theorem jacobiBilateral_fe {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0) (hz : ‖z‖ < 1)
    (hz' : z ≠ 0) :
    jacobiBilateral q (q * z) = jacobiBilateral q z / z := by
  rw [ eq_div_iff hz', mul_comm ]
  set_option linter.unusedSimpArgs false in
  have h_pos : z * jacobiBilateralPos q (q * z) = ∑' k : ℕ, if k = 0 then 0 else z ^ k * q ^ k.choose 2 := by
    rw [ eq_comm, Summable.tsum_eq_zero_add ]
    · simp +decide [ Nat.choose_succ_succ, pow_succ', mul_pow, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left ]
      exact Or.inl ( tsum_congr fun n => by ring )
    · have h_summable : Summable (fun k : ℕ => z ^ k * q ^ k.choose 2) := by
        convert summable_jacobi_nonneg hq hz using 1
      rw [ ← summable_nat_add_iff 1 ] at * ; aesop
  set_option linter.unusedSimpArgs false in
  have h_neg : z * jacobiBilateralNeg q (q * z) = ∑' m : ℕ, z ^ (-m : ℤ) * q ^ (m + 1).choose 2 := by
    unfold jacobiBilateralNeg; simp +decide [ div_eq_mul_inv, pow_add, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left ] 
    simp +decide [ mul_assoc, mul_comm, Nat.choose_succ_succ ]
    simp +decide [ add_comm, add_left_comm, add_assoc, pow_add, mul_left_comm, tsum_mul_left, hq', hz' ]
    simp +decide [ mul_pow, mul_assoc, hq' ]
  convert congr_arg₂ ( · + · ) h_pos h_neg using 1
  · rw [ ← mul_add, jacobiBilateral ]
  · unfold jacobiBilateral jacobiBilateralPos jacobiBilateralNeg
    rw [ Summable.tsum_eq_zero_add ]
    · rw [ eq_comm, Summable.tsum_eq_zero_add ]
      · norm_num [ Nat.choose_succ_succ, pow_succ' ]
        rw [ eq_comm, Summable.tsum_eq_zero_add ]
        · norm_num [ add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right ]
          rw [ eq_comm, Summable.tsum_eq_zero_add ]
          · norm_num [ Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right ]
            grind
          · have := summable_jacobi_neg hq hz'
            rw [ ← summable_nat_add_iff 1 ] ; convert this using 2 ; norm_num [ Nat.choose_succ_succ, pow_succ' ] ; ring
        · refine Summable.of_norm ?_
          norm_num [ pow_add, pow_mul ]
          refine Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => ?_ ) ( summable_geometric_of_lt_one ( by positivity ) hz )
          exact le_trans ( mul_le_of_le_one_right ( by positivity ) ( mul_le_one₀ ( pow_le_one₀ ( by positivity ) hq.le ) ( pow_nonneg ( by positivity ) _ ) ( pow_le_one₀ ( by positivity ) hq.le ) ) ) ( mul_le_of_le_one_left ( by positivity ) hz.le )
      · rw [ ← summable_nat_add_iff 1 ]
        convert summable_jacobi_nonneg hq hz |> Summable.comp_injective <| Nat.succ_injective using 1
    · convert summable_jacobi_nonneg hq hz using 1

/-- Summability of the Euler second series $\sum_{n \geq 0} q^{\binom{n}{2}} z^n / (q;q)_n$ for all $z$ when $\|q\| < 1$. -/
theorem euler_second_summable_all {q z : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n) := by
  refine summable_of_ratio_norm_eventually_le (r := ‖q‖ + (1 - ‖q‖) / 2) (by linarith) ?_
  · have h_eventually : ∃ N, ∀ n ≥ N, ‖q‖ ^ n * ‖z‖ / ‖1 - q ^ (n + 1)‖ ≤ (‖q‖ + (1 - ‖q‖) / 2) := by
      have h_eventually : Filter.Tendsto (fun n : ℕ => ‖q‖ ^ n * ‖z‖ / ‖1 - q ^ (n + 1)‖) Filter.atTop (nhds 0) := by
        simpa using Filter.Tendsto.div ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) hq |> Filter.Tendsto.mul_const ‖z‖ ) ( Filter.Tendsto.norm ( tendsto_const_nhds.sub ( tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 ) ) ) ( by norm_num )
      exact Filter.eventually_atTop.mp ( h_eventually.eventually ( ge_mem_nhds <| by linarith [ norm_nonneg q ] ) )
    obtain ⟨ N, hN ⟩ := h_eventually; filter_upwards [ Filter.eventually_ge_atTop N ] with n hn; specialize hN n hn; simp_all +decide [ Nat.choose_succ_succ, pow_add, mul_assoc, mul_div_mul_comm ]
    convert mul_le_mul_of_nonneg_right hN ( show 0 ≤ ‖q‖ ^ n.choose 2 * ‖z‖ ^ n / ‖qPochhammer q q n‖ by positivity ) using 1 ; ring
    rw [ show qPochhammer q q ( 1 + n ) = qPochhammer q q n * ( 1 - q ^ ( n + 1 ) ) by rw [ add_comm, qPochhammer_succ ] ; ring ] ; norm_num ; ring

/-- The Euler second series satisfies the recursion $E(z) = (1+z) \cdot E(qz)$. -/
theorem euler_second_series_recursion {q z : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) =
    (1 + z) * (∑' n : ℕ, q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) := by
  have h_series : ∀ n : ℕ, (q ^ n.choose 2 * z ^ n / qPochhammer q q n) - (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) = z * (q ^ (n - 1).choose 2 * (z * q) ^ (n - 1) / qPochhammer q q (n - 1)) * (if n = 0 then 0 else 1) := by
    intro n; rcases n <;> simp_all +decide [ Nat.choose_succ_succ, pow_succ, mul_assoc, mul_div_mul_left ] ; ring
    rw [ show qPochhammer q q ( 1 + _ ) = qPochhammer q q ‹_› * ( 1 - q ^ ( ‹_› + 1 ) ) by
          rw [ add_comm, qPochhammer_succ ] ; ring; ] ; ring
    convert mul_div_mul_right _ _ ( show ( - ( q * q ^ ‹_› ) + 1 ) ≠ 0 from _ ) using 1 ; ring
    exact fun h => by rw [ add_eq_zero_iff_eq_neg ] at h; replace h := congr_arg Norm.norm h; norm_num at h; nlinarith [ pow_le_pow_of_le_one ( norm_nonneg q ) hq.le ( show ‹_› ≥ 0 by positivity ), norm_nonneg q ] 
  have h_series_sum : ∑' n : ℕ, (q ^ n.choose 2 * z ^ n / qPochhammer q q n) - ∑' n : ℕ, (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) = z * ∑' n : ℕ, (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) := by
    rw [ ← Summable.tsum_sub, tsum_congr h_series ]
    · rw [ ← tsum_mul_left ] ; rw [ Summable.tsum_eq_zero_add ] ; aesop
      rw [ ← summable_nat_add_iff 1 ]
      convert Summable.mul_left z ( euler_second_summable_all hq |> Summable.comp_injective <| Nat.cast_injective ) using 2 ; aesop
    · convert euler_second_summable_all hq using 1
    · convert euler_second_summable_all hq using 1
  linear_combination' h_series_sum

/-- Euler second identity for all $z$: the series $\sum_{n \geq 0} q^{\binom{n}{2}} z^n / (q;q)_n$ has sum $(-z;q)_\infty$. -/
theorem euler_second_identity_all {q z : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n)
      (qPochhammerInf (-z) q) := by
  have h_ind : ∀ N : ℕ, (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * (∑' n : ℕ, q ^ n.choose 2 * (z * q ^ N) ^ n / qPochhammer q q n) := by
    intro N
    induction N with
    | zero => aesop
    | succ N ih =>
        have h_rec : (∑' n : ℕ, q ^ n.choose 2 * (z * q ^ N) ^ n / qPochhammer q q n) = (1 + z * q ^ N) * (∑' n : ℕ, q ^ n.choose 2 * (z * q ^ (N + 1)) ^ n / qPochhammer q q n) := by
          convert euler_second_series_recursion hq using 1 ; ring
        rw [ Finset.prod_range_succ, ih, h_rec, mul_assoc ]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖z * q ^ N‖ < 1 := by
    have h_lim : Filter.Tendsto (fun N : ℕ => ‖z * q ^ N‖) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg q ) hq )
    exact ( h_lim.eventually ( gt_mem_nhds zero_lt_one ) ) |> fun h => h.exists
  have h_ind_step : (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
    rw [ h_ind N, euler_second_identity hq hN |> HasSum.tsum_eq ]
  have h_ind_step : qPochhammerInf (-z) q = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
    have h_ind_step : ∀ N : ℕ, qPochhammerInf (-z) q = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
      intro N
      induction N with
      | zero => simp_all +decide [ Finset.prod_range_succ, pow_succ' ]
      | succ N ih =>
          simp_all +decide [ Finset.prod_range_succ, pow_succ' ]
          rw [ show qPochhammerInf ( - ( z * q ^ N ) ) q = ( 1 - ( - ( z * q ^ N ) ) ) * qPochhammerInf ( - ( z * q ^ N ) * q ) q from qPochhammerInf_recursion hq ]
          ring
    exact h_ind_step N
  convert Summable.hasSum _ using 1
  · grind +qlia
  · convert euler_second_summable_all hq using 1

/-- Euler second identity evaluated at $q/z$: the series $\sum_{m \geq 0} q^{\binom{m}{2}+m} z^{-m} / (q;q)_m$ has sum $(-q/z;q)_\infty$. -/
theorem euler_second_at_qoz_all {q z : ℂ} (hq : ‖q‖ < 1) (hz' : z ≠ 0) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)
      (qPochhammerInf (-q / z) q) := by
  convert euler_second_identity_all hq |> HasSum.congr_fun <| fun n => ?_ using 1
  rotate_left
  exacts [ q * z⁻¹, by ring, by ring ]

set_option maxHeartbeats 800000 in
/-- **Jacobi triple product identity**: $(q;q)_\infty (-z;q)_\infty (-q/z;q)_\infty$ equals the bilateral theta series $\sum_{k \in \mathbb{Z}} z^k q^{k(k-1)/2}$ for $\|q\| < 1$, $\|z\| < 1$, and $z \neq 0$. -/
theorem jacobiTripleProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    jacobiProd q z = jacobiBilateral q z := by
  have hPQ : qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q = (∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) * (∑' m : ℕ, q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
    rw [ qPochhammerInf_prod_hasSum hq hz |>.tsum_eq, euler_second_at_qoz_all hq hz' |>.tsum_eq ]
  have h_fubini : (∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) * (∑' m : ℕ, q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) = ∑' p : ℕ × ℕ, q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q * (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) := by
    rw [ Summable.tsum_prod ]
    · simp +decide only [tsum_mul_left, tsum_mul_right]
    · have h_summable : Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) ∧ Summable (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
        constructor
        · convert qPochhammerInf_prod_hasSum hq hz |> HasSum.summable using 1
        · convert euler_second_at_qoz_all hq hz' |> HasSum.summable using 1
      exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.1.norm ) ( h_summable.2.norm ) 
  have h_split : ∑' p : ℕ × ℕ, q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q * (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) = (∑' k : ℕ, ∑' m : ℕ, q ^ (m + k).choose 2 * z ^ (m + k) * qPochhammerInf (q * q ^ (m + k)) q * (q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)) + (∑' l : ℕ, ∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q * (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) * z⁻¹ ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1)))) := by
    have h_split : ∀ {f : ℕ × ℕ → ℂ}, Summable f → ∑' p : ℕ × ℕ, f p = ∑' k : ℕ, ∑' m : ℕ, f (m + k, m) + ∑' l : ℕ, ∑' n : ℕ, f (n, n + (l + 1)) := by
      intro f hf
      have h_split : ∑' p : ℕ × ℕ, f p = ∑' p : ℕ × ℕ, f (p.1 + p.2, p.2) + ∑' p : ℕ × ℕ, f (p.1, p.1 + p.2 + 1) := by
        have h_split : ∑' p : ℕ × ℕ, f p = ∑' p : ℕ × ℕ, f (p.1 + p.2, p.2) + ∑' p : ℕ × ℕ, f (p.1, p.1 + p.2 + 1) := by
          have h_partition : ∀ p : ℕ × ℕ, p ∈ {p : ℕ × ℕ | p.1 ≥ p.2} ↔ ∃ q : ℕ × ℕ, p = (q.1 + q.2, q.2) := by
            exact fun p => ⟨ fun hp => ⟨ ⟨ p.1 - p.2, p.2 ⟩, by simp +decide [ Nat.sub_add_cancel hp ] ⟩, by rintro ⟨ q, rfl ⟩ ; simp +decide ⟩
          have h_partition' : ∀ p : ℕ × ℕ, p ∈ {p : ℕ × ℕ | p.1 < p.2} ↔ ∃ q : ℕ × ℕ, p = (q.1, q.1 + q.2 + 1) := by
            simp +zetaDelta at *
            exact fun a b => ⟨ fun h => ⟨ b - a - 1, by omega ⟩, fun ⟨ x, hx ⟩ => by omega ⟩
          have h_split : ∑' p : ℕ × ℕ, f p = ∑' p : ℕ × ℕ, f p * (if p.1 ≥ p.2 then 1 else 0) + ∑' p : ℕ × ℕ, f p * (if p.1 < p.2 then 1 else 0) := by
            rw [ ← Summable.tsum_add ] ; congr ; ext p ; split_ifs <;> ring <;> omega
            · exact Summable.of_norm <| by simpa using hf.norm.of_nonneg_of_le ( fun p => by positivity ) fun p => by split_ifs <;> norm_num
            · exact Summable.of_norm <| by simpa using hf.norm.of_nonneg_of_le ( fun p => by positivity ) fun p => by split_ifs <;> norm_num
          convert h_split using 2
          · rw [ ← tsum_eq_tsum_of_ne_zero_bij ]
            use fun p => ( p.val.1 + p.val.2, p.val.2 )
            · norm_num [ Function.Injective ]
              intros; omega
            · intro p hp; specialize h_partition p; aesop
            · simp +decide [ Nat.le_add_left ]
          · rw [ ← tsum_eq_tsum_of_ne_zero_bij ]
            use fun p => ( p.val.1, p.val.1 + p.val.2 + 1 )
            · norm_num [ Function.Injective ]
              intros; subst_vars; exact ⟨ rfl, by omega ⟩ 
            · intro p hp; specialize h_partition' p; aesop
            · simp +decide [ Nat.lt_succ_iff ]
        convert h_split using 1
      convert h_split using 1
      rw [ Summable.tsum_prod, Summable.tsum_prod ]
      · simp +decide only [add_comm, add_assoc]
        rw [ Summable.tsum_comm ]
        exact hf.comp_injective fun x y h => by aesop
      · convert hf.comp_injective ( show Function.Injective ( fun p : ℕ × ℕ => ( p.1, p.1 + p.2 + 1 ) ) from fun p q h => by aesop ) using 1
      · convert hf.comp_injective ( show Function.Injective ( fun p : ℕ × ℕ => ( p.1 + p.2, p.2 ) ) from fun p q h => by aesop ) using 1
    apply h_split
    have h_summable : Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) ∧ Summable (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
      constructor
      · exact qPochhammerInf_prod_hasSum hq hz |> HasSum.summable
      · convert euler_second_at_qoz_all hq hz' |> HasSum.summable using 1
    exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.1.norm ) ( h_summable.2.norm ) 
  have h_cauchy : ∀ k : ℕ, ∑' m : ℕ, q ^ (m + k).choose 2 * z ^ (m + k) * qPochhammerInf (q * q ^ (m + k)) q * (q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) = z ^ k * q ^ k.choose 2 := by
    intro k
    have := cauchy_coeff_nonneg hq k
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, tsum_mul_left, tsum_mul_right ]
    convert congr_arg ( fun x => z ^ k * x ) this.tsum_eq using 1 ; ring
    rw [ ← tsum_mul_left ] ; congr ; ext m ; ring
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, hz' ]
  have h_cauchy_neg : ∀ l : ℕ, ∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q * (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) * z⁻¹ ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1))) = z⁻¹ ^ (l + 1) * q ^ (l + 2).choose 2 := by
    intro l
    have := cauchy_coeff_neg hq l
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, tsum_mul_left, tsum_mul_right ]
    rw [ ← this.tsum_eq ]
    rw [ ← tsum_mul_left ] ; congr ; ext n ; ring
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, hz' ]
  unfold jacobiProd jacobiBilateral jacobiBilateralPos jacobiBilateralNeg; aesop

end

end qSeries