import QSeries.EulerIdentities
import QSeries.JTP_Core

/-!
# Jacobi triple product identity

The **Jacobi triple product identity** states that for $\|q\| < 1$ and $z \neq 0$:
$$(q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty
  = \sum_{k \in \mathbb{Z}} z^k \, q^{k(k-1)/2}.$$

## Proof strategy

The proof runs directly on the whole punctured disk `0 < ‖z‖ < 1`:
1. Expand `(q;q)_∞ (-z;q)_∞` as a series via `qPochhammerInf_prod_hasSum`
   (second Euler identity + telescoping).
2. Expand `(-q/z;q)_∞` via `euler_second_at_qoz_all`, the *extended* second
   Euler identity valid for all `z ≠ 0` — this removes any annulus restriction.
3. Form the Cauchy product over `ℕ × ℕ` and reorder by diagonals.
4. Evaluate each diagonal coefficient with the key identity
   `S_k = 1/(q;q)_∞` (`cauchy_coeff_nonneg`, `cauchy_coeff_neg`).

## Main results

* `qSeries.jacobiTripleProduct` — the Jacobi triple product identity.
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-! ## Bilateral series

For $k \in \mathbb{Z}$, the exponent is $k(k-1)/2$. Split into:
- Non-negative part ($k \geq 0$): $z^k q^{\binom{k}{2}}$ where $\binom{k}{2} = k(k-1)/2$.
- Negative part ($k = -(m+1)$, $m \geq 0$): $z^{-(m+1)} q^{(m+1)(m+2)/2} = z^{-(m+1)} q^{\binom{m+2}{2}}$.
-/

/-! ## The triple product -/

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

/-! ## Extended Euler 2nd identity (for all z) -/

/-
Summability of the Euler 2nd series for all z (not just ‖z‖ < 1).
-/
theorem euler_second_summable_all {q z : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n) := by
  refine' summable_of_ratio_norm_eventually_le _ _;
  exact ( ‖q‖ + ( 1 - ‖q‖ ) / 2 );
  · linarith;
  · -- We'll use the fact that |q| < 1 to find such an N.
    have h_eventually : ∃ N, ∀ n ≥ N, ‖q‖ ^ n * ‖z‖ / ‖1 - q ^ (n + 1)‖ ≤ (‖q‖ + (1 - ‖q‖) / 2) := by
      have h_eventually : Filter.Tendsto (fun n : ℕ => ‖q‖ ^ n * ‖z‖ / ‖1 - q ^ (n + 1)‖) Filter.atTop (nhds 0) := by
        simpa using Filter.Tendsto.div ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) hq |> Filter.Tendsto.mul_const ‖z‖ ) ( Filter.Tendsto.norm ( tendsto_const_nhds.sub ( tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 ) ) ) ( by norm_num );
      exact Filter.eventually_atTop.mp ( h_eventually.eventually ( ge_mem_nhds <| by linarith [ norm_nonneg q ] ) );
    obtain ⟨ N, hN ⟩ := h_eventually; filter_upwards [ Filter.eventually_ge_atTop N ] with n hn; specialize hN n hn; simp_all +decide [ Nat.choose_succ_succ, pow_add, mul_assoc, mul_div_mul_comm ] ;
    convert mul_le_mul_of_nonneg_right hN ( show 0 ≤ ‖q‖ ^ n.choose 2 * ‖z‖ ^ n / ‖qPochhammer q q n‖ by positivity ) using 1 ; ring;
    rw [ show qPochhammer q q ( 1 + n ) = qPochhammer q q n * ( 1 - q ^ ( n + 1 ) ) by rw [ add_comm, qPochhammer_succ ] ; ring ] ; norm_num ; ring

/-
The Euler 2nd series satisfies the recursion S(z) = (1+z) * S(qz).
    This is a purely algebraic identity on formal series.
-/
theorem euler_second_series_recursion {q z : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) =
    (1 + z) * (∑' n : ℕ, q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) := by
  have h_series : ∀ n : ℕ, (q ^ n.choose 2 * z ^ n / qPochhammer q q n) - (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) = z * (q ^ (n - 1).choose 2 * (z * q) ^ (n - 1) / qPochhammer q q (n - 1)) * (if n = 0 then 0 else 1) := by
    intro n; rcases n <;> simp_all +decide [ Nat.choose_succ_succ, pow_succ, mul_assoc, mul_div_mul_left ] ; ring;
    rw [ show qPochhammer q q ( 1 + _ ) = qPochhammer q q ‹_› * ( 1 - q ^ ( ‹_› + 1 ) ) by
          rw [ add_comm, qPochhammer_succ ] ; ring; ] ; ring;
    convert mul_div_mul_right _ _ ( show ( - ( q * q ^ ‹_› ) + 1 ) ≠ 0 from _ ) using 1 ; ring;
    exact fun h => by rw [ add_eq_zero_iff_eq_neg ] at h; replace h := congr_arg Norm.norm h; norm_num at h; nlinarith [ pow_le_pow_of_le_one ( norm_nonneg q ) hq.le ( show ‹_› ≥ 0 by positivity ), norm_nonneg q ] ;
  have h_series_sum : ∑' n : ℕ, (q ^ n.choose 2 * z ^ n / qPochhammer q q n) - ∑' n : ℕ, (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) = z * ∑' n : ℕ, (q ^ n.choose 2 * (z * q) ^ n / qPochhammer q q n) := by
    rw [ ← Summable.tsum_sub, tsum_congr h_series ];
    · rw [ ← tsum_mul_left ] ; rw [ Summable.tsum_eq_zero_add ] ; aesop;
      rw [ ← summable_nat_add_iff 1 ];
      convert Summable.mul_left z ( euler_second_summable_all hq |> Summable.comp_injective <| Nat.cast_injective ) using 2 ; aesop;
    · convert euler_second_summable_all hq using 1;
    · convert euler_second_summable_all hq using 1;
  linear_combination' h_series_sum

/-
**Extended Euler 2nd identity**: valid for ALL z ∈ ℂ (not just ‖z‖ < 1).
    $(-z;q)_\infty = \sum_{n \geq 0} q^{\binom{n}{2}} z^n / (q;q)_n$
-/
theorem euler_second_identity_all {q z : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n)
      (qPochhammerInf (-z) q) := by
  have h_ind : ∀ N : ℕ, (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * (∑' n : ℕ, q ^ n.choose 2 * (z * q ^ N) ^ n / qPochhammer q q n) := by
    intro N
    induction' N with N ih
    aesop;
    -- Apply the recursion step to the sum.
    have h_rec : (∑' n : ℕ, q ^ n.choose 2 * (z * q ^ N) ^ n / qPochhammer q q n) = (1 + z * q ^ N) * (∑' n : ℕ, q ^ n.choose 2 * (z * q ^ (N + 1)) ^ n / qPochhammer q q n) := by
      convert euler_second_series_recursion hq using 1 ; ring;
    rw [ Finset.prod_range_succ, ih, h_rec, mul_assoc ];
  -- Choose N such that ‖z * q^N‖ < 1.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖z * q ^ N‖ < 1 := by
    have h_lim : Filter.Tendsto (fun N : ℕ => ‖z * q ^ N‖) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg q ) hq );
    exact ( h_lim.eventually ( gt_mem_nhds zero_lt_one ) ) |> fun h => h.exists;
  -- By the induction hypothesis, we have:
  have h_ind_step : (∑' n : ℕ, q ^ n.choose 2 * z ^ n / qPochhammer q q n) = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
    rw [ h_ind N, euler_second_identity hq hN |> HasSum.tsum_eq ];
  have h_ind_step : qPochhammerInf (-z) q = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
    have h_ind_step : ∀ N : ℕ, qPochhammerInf (-z) q = (∏ k ∈ Finset.range N, (1 + z * q ^ k)) * qPochhammerInf (-(z * q ^ N)) q := by
      intro N; induction' N with N ih <;> simp_all +decide [ Finset.prod_range_succ, pow_succ' ] ; ring;
      rw [ show qPochhammerInf ( - ( z * q ^ N ) ) q = ( 1 - ( - ( z * q ^ N ) ) ) * qPochhammerInf ( - ( z * q ^ N ) * q ) q from qPochhammerInf_recursion hq ] ; ring;
    exact h_ind_step N;
  convert Summable.hasSum _ using 1;
  · grind +qlia;
  · convert euler_second_summable_all hq using 1

/-
Euler 2nd at q/z, valid for all z ≠ 0.
-/
theorem euler_second_at_qoz_all {q z : ℂ} (hq : ‖q‖ < 1) (hz' : z ≠ 0) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)
      (qPochhammerInf (-q / z) q) := by
  convert euler_second_identity_all hq |> HasSum.congr_fun <| fun n => ?_ using 1;
  rotate_left;
  exacts [ q * z⁻¹, by ring, by ring ]

/-! ## The Jacobi triple product identity -/

/-
**Jacobi triple product identity.**
-/
set_option maxHeartbeats 800000 in
theorem jacobiTripleProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    jacobiProd q z = jacobiBilateral q z := by
  have hPQ : qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q = (∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) * (∑' m : ℕ, q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
    rw [ qPochhammerInf_prod_hasSum hq hz |>.tsum_eq, euler_second_at_qoz_all hq hz' |>.tsum_eq ];
  have h_fubini : (∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) * (∑' m : ℕ, q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) = ∑' p : ℕ × ℕ, q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q * (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) := by
    rw [ Summable.tsum_prod ];
    · simp +decide only [tsum_mul_left, tsum_mul_right];
    · have h_summable : Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) ∧ Summable (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
        constructor;
        · convert qPochhammerInf_prod_hasSum hq hz |> HasSum.summable using 1;
        · convert euler_second_at_qoz_all hq hz' |> HasSum.summable using 1;
      exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.1.norm ) ( h_summable.2.norm ) ;
  have h_split : ∑' p : ℕ × ℕ, q ^ p.1.choose 2 * z ^ p.1 * qPochhammerInf (q * q ^ p.1) q * (q ^ p.2.choose 2 * q ^ p.2 * z⁻¹ ^ p.2 / qPochhammer q q p.2) = (∑' k : ℕ, ∑' m : ℕ, q ^ (m + k).choose 2 * z ^ (m + k) * qPochhammerInf (q * q ^ (m + k)) q * (q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)) + (∑' l : ℕ, ∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q * (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) * z⁻¹ ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1)))) := by
    have h_split : ∀ {f : ℕ × ℕ → ℂ}, Summable f → ∑' p : ℕ × ℕ, f p = ∑' k : ℕ, ∑' m : ℕ, f (m + k, m) + ∑' l : ℕ, ∑' n : ℕ, f (n, n + (l + 1)) := by
      intro f hf;
      have h_split : ∑' p : ℕ × ℕ, f p = ∑' p : ℕ × ℕ, f (p.1 + p.2, p.2) + ∑' p : ℕ × ℕ, f (p.1, p.1 + p.2 + 1) := by
        have h_split : ∑' p : ℕ × ℕ, f p = ∑' p : ℕ × ℕ, f (p.1 + p.2, p.2) + ∑' p : ℕ × ℕ, f (p.1, p.1 + p.2 + 1) := by
          have h_partition : ∀ p : ℕ × ℕ, p ∈ {p : ℕ × ℕ | p.1 ≥ p.2} ↔ ∃ q : ℕ × ℕ, p = (q.1 + q.2, q.2) := by
            exact fun p => ⟨ fun hp => ⟨ ⟨ p.1 - p.2, p.2 ⟩, by simp +decide [ Nat.sub_add_cancel hp ] ⟩, by rintro ⟨ q, rfl ⟩ ; simp +decide ⟩
          have h_partition' : ∀ p : ℕ × ℕ, p ∈ {p : ℕ × ℕ | p.1 < p.2} ↔ ∃ q : ℕ × ℕ, p = (q.1, q.1 + q.2 + 1) := by
            simp +zetaDelta at *;
            exact fun a b => ⟨ fun h => ⟨ b - a - 1, by omega ⟩, fun ⟨ x, hx ⟩ => by omega ⟩
          have h_split : ∑' p : ℕ × ℕ, f p = ∑' p : ℕ × ℕ, f p * (if p.1 ≥ p.2 then 1 else 0) + ∑' p : ℕ × ℕ, f p * (if p.1 < p.2 then 1 else 0) := by
            rw [ ← Summable.tsum_add ] ; congr ; ext p ; split_ifs <;> ring <;> linarith;
            · exact Summable.of_norm <| by simpa using hf.norm.of_nonneg_of_le ( fun p => by positivity ) fun p => by split_ifs <;> norm_num;
            · exact Summable.of_norm <| by simpa using hf.norm.of_nonneg_of_le ( fun p => by positivity ) fun p => by split_ifs <;> norm_num;
          convert h_split using 2;
          · rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
            use fun p => ( p.val.1 + p.val.2, p.val.2 );
            · norm_num [ Function.Injective ];
              intros; omega;
            · intro p hp; specialize h_partition p; aesop;
            · simp +decide [ Nat.le_add_left ];
          · rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
            use fun p => ( p.val.1, p.val.1 + p.val.2 + 1 );
            · norm_num [ Function.Injective ];
              intros; subst_vars; exact ⟨ rfl, by linarith ⟩ ;
            · intro p hp; specialize h_partition' p; aesop;
            · simp +decide [ Nat.lt_succ_iff ];
        convert h_split using 1;
      convert h_split using 1;
      erw [ Summable.tsum_prod, Summable.tsum_prod ];
      · simp +decide only [add_comm, add_assoc];
        rw [ Summable.tsum_comm ];
        exact hf.comp_injective fun x y h => by aesop;
      · convert hf.comp_injective ( show Function.Injective ( fun p : ℕ × ℕ => ( p.1, p.1 + p.2 + 1 ) ) from fun p q h => by aesop ) using 1;
      · convert hf.comp_injective ( show Function.Injective ( fun p : ℕ × ℕ => ( p.1 + p.2, p.2 ) ) from fun p q h => by aesop ) using 1;
    apply h_split;
    have h_summable : Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q) ∧ Summable (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) := by
      constructor;
      · exact qPochhammerInf_prod_hasSum hq hz |> HasSum.summable;
      · convert euler_second_at_qoz_all hq hz' |> HasSum.summable using 1;
    exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.1.norm ) ( h_summable.2.norm ) ;
  have h_cauchy : ∀ k : ℕ, ∑' m : ℕ, q ^ (m + k).choose 2 * z ^ (m + k) * qPochhammerInf (q * q ^ (m + k)) q * (q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m) = z ^ k * q ^ k.choose 2 := by
    intro k
    have := cauchy_coeff_nonneg hq k
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, tsum_mul_left, tsum_mul_right ];
    convert congr_arg ( fun x => z ^ k * x ) this.tsum_eq using 1 ; ring;
    rw [ ← tsum_mul_left ] ; congr ; ext m ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, hz' ];
  have h_cauchy_neg : ∀ l : ℕ, ∑' n : ℕ, q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q * (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) * z⁻¹ ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1))) = z⁻¹ ^ (l + 1) * q ^ (l + 2).choose 2 := by
    intro l
    have := cauchy_coeff_neg hq l
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, tsum_mul_left, tsum_mul_right ];
    rw [ ← this.tsum_eq ];
    rw [ ← tsum_mul_left ] ; congr ; ext n ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, hz' ];
  unfold jacobiProd jacobiBilateral jacobiBilateralPos jacobiBilateralNeg; aesop;

end

end qSeries
