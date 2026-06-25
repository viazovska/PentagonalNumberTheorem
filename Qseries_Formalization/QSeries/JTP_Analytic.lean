/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import Mathlib
import QSeries.JacobiTripleProduct

/-!
# Locally uniform convergence and analytic Jacobi triple product

We prove that both sides of the Jacobi triple product (JTP) identity converge
locally uniformly for $\|q\| < 1$ on $\{z \neq 0\}$, and deduce the **analytic JTP**:
the identity holds for **all** $\|q\| < 1$ and $z \neq 0$ (removing the earlier
restriction $\|z\| < 1$).

## Main results

* `qSeries.summable_jacobi_nonneg_all` — Summability of the nonneg bilateral
  sum for **all** $z$ when $\|q\| < 1$.
* `qSeries.jacobiProd_tendstoLocallyUniformlyOn` — The product side converges
  locally uniformly on $\{z \neq 0\}$.
* `qSeries.jacobiBilateral_tendstoLocallyUniformlyOn` — The series side
  converges locally uniformly on $\{z \neq 0\}$.
* `qSeries.jacobiTripleProduct_analytic` — The analytic JTP for all
  $\|q\| < 1$ and $z \neq 0$.
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-- The nonneg bilateral sum $\sum_{k \ge 0} z^k q^{\binom{k}{2}}$ converges
for **all** $z \in \mathbb{C}$ when $\|q\| < 1$. -/
theorem summable_jacobi_nonneg_all {q z : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => z ^ k * q ^ k.choose 2) := by
  refine summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num) ?_
  · have h_lim : Filter.Tendsto (fun n => ‖z‖ * ‖q‖ ^ n) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq)
    filter_upwards [h_lim.eventually (gt_mem_nhds <| show 0 < 1 / 2 by norm_num)] with n hn
    norm_num [Nat.choose_succ_succ, pow_succ, mul_assoc, mul_left_comm, mul_comm] at *
    rw [show n + n.choose 2 = n.choose 2 + n by ring, pow_add]
    nlinarith [show 0 ≤ ‖z‖ ^ n * ‖q‖ ^ n.choose 2 by positivity]

/-- Summability of the Weierstrass M-test bound $R^k \|q\|^{\binom{k}{2}}$ for any real $R$. -/
theorem summable_Mtest_nonneg {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    Summable (fun k : ℕ => R ^ k * ‖q‖ ^ k.choose 2) := by
  have h_ratio_test : Filter.Tendsto (fun k : ℕ => ‖R‖ * ‖q‖ ^ k) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg q ) hq )
  refine summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num) ?_
  · filter_upwards [ h_ratio_test.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ) ] with n hn
    convert mul_le_mul_of_nonneg_right hn.le ( show 0 ≤ ‖R ^ n * ‖q‖ ^ n.choose 2‖ by positivity ) using 1 ; norm_num [ Nat.choose_succ_succ, pow_succ' ] ; ring

/-- Summability of the Weierstrass M-test bound $(R')^{m+1} \|q\|^{\binom{m+2}{2}}$ for any real $R'$. -/
theorem summable_Mtest_neg {q : ℂ} (hq : ‖q‖ < 1) (R' : ℝ) :
    Summable (fun m : ℕ => R' ^ (m + 1) * ‖q‖ ^ (m + 2).choose 2) := by
  have h_ratio : Filter.Tendsto (fun m : ℕ => |R'| * ‖q‖ ^ (m + 2)) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) hq |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2 )
  refine summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num) ?_
  · filter_upwards [ h_ratio.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ) ] with n hn ; norm_num [ Nat.choose ] at *
    convert mul_le_mul_of_nonneg_right hn.le ( show 0 ≤ |R'| ^ ( n + 1 ) * ‖q‖ ^ ( 1 + n + ( n + n.choose 2 ) ) by positivity ) using 1 ; ring

/-- Extended product expansion for all $z$. -/
theorem qPochhammerInf_prod_hasSum_all {q z : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q)
      (qPochhammerInf q q * qPochhammerInf (-z) q) := by
  convert HasSum.mul_left (qPochhammerInf q q) (euler_second_identity_all hq) using 1
  ext n
  by_cases hn : qPochhammer q q n = 0
  · exact absurd hn <| qPochhammer_z_q_ne_zero hq (by linarith) n
  · simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    congr 1
    rw [qPochhammerInf_eq_mul hq n]
    field_simp

/-- The nonneg partial sums $\sum_{k < N} z^k q^{\binom{k}{2}}$ converge uniformly on $\{z : \|z\| \le R\}$ by the Weierstrass M-test. -/
theorem nonneg_tendstoUniformlyOn_ball {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N z => ∑ k ∈ Finset.range N, z ^ k * q ^ k.choose 2)
      (fun z => ∑' k : ℕ, z ^ k * q ^ k.choose 2)
      atTop (Metric.closedBall 0 R) := by
  convert tendstoUniformlyOn_tsum_nat _ _ using 1
  generalize_proofs at *
  exact inferInstance
  exact fun n => R ^ n * ‖q‖ ^ n.choose 2
  exact summable_Mtest_nonneg hq R
  intro n x hx
  simp [hx]
  exact mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( norm_nonneg _ ) ( by simpa using hx ) _ ) ( by positivity )

/-- The negative-index partial sums converge uniformly on $\{z : \|z^{-1}\| \le R'\}$. -/
theorem neg_tendstoUniformlyOn_ball {q : ℂ} (hq : ‖q‖ < 1) (R' : ℝ) (hR' : 0 ≤ R') :
    TendstoUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2)
      (fun z => ∑' m : ℕ, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2)
      atTop {z : ℂ | ‖z⁻¹‖ ≤ R'} := by
  have := @tendstoUniformlyOn_tsum_nat
  convert this ( summable_Mtest_neg hq R' ) _ using 1
  · infer_instance
  · simp +zetaDelta at *
    exact fun n x hx => mul_le_mul_of_nonneg_right ( by simpa using pow_le_pow_left₀ ( by positivity ) hx _ ) ( by positivity )

/-- Convert Finset-indexed `TendstoUniformlyOn` to ℕ-indexed via `Finset.range`. -/
lemma tendstoUniformlyOn_prod_range_of_finset {α β : Type*}
    [CommMonoid β] [UniformSpace β] {f : ℕ → α → β} {g : α → β} {s : Set α}
    (h : TendstoUniformlyOn (fun (S : Finset ℕ) (x : α) => ∏ i ∈ S, f i x) g
         Filter.atTop s) :
    TendstoUniformlyOn (fun (n : ℕ) (x : α) => ∏ i ∈ Finset.range n, f i x) g
         Filter.atTop s := by
  intro U hU
  have h1 := h U hU
  rw [Filter.Eventually] at h1 ⊢
  have h_range : Filter.Tendsto Finset.range (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter (Finset ℕ)) := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    exact ⟨(s.sup id) + 1, fun n hn x hx =>
      Finset.mem_range.mpr (by have := Finset.le_sup (f := id) hx; simp at this; omega)⟩
  exact h_range.eventually h1

/-- The partial Pochhammer products $(a;q)_n$ converge locally uniformly in $a$ when $\|q\| < 1$. -/
theorem qPochhammer_tendstoLocallyUniformly {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformly
      (fun n a => qPochhammer a q n)
      (fun a => qPochhammerInf a q) atTop := by
  unfold qPochhammer qPochhammerInf
  have h_uniform : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn (fun n a => ∏ k ∈ Finset.range n, (1 - a * q ^ k)) (fun a => ∏' k : ℕ, (1 - a * q ^ k)) Filter.atTop K := by
    intro K hK
    have h_uniform : Summable (fun k : ℕ => (SupSet.sSup (Set.image (fun a => ‖a‖) K)) * ‖q‖ ^ k) := by
      exact Summable.mul_left _ <| summable_geometric_of_lt_one ( norm_nonneg q ) hq
    have := @Summable.hasProdUniformlyOn_one_add
    specialize this hK h_uniform ( show ∀ᶠ i in cofinite, ∀ x ∈ K, ‖-x * q ^ i‖ ≤ sSup ( Set.image ( fun a => ‖a‖ ) K ) * ‖q‖ ^ i from ?_ ) ( show ∀ i, ContinuousOn ( fun x => -x * q ^ i ) K from ?_ )
    · filter_upwards [ Filter.eventually_cofinite_ne 0 ] with i hi x hx using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( show ‖x‖ ≤ sSup ( Set.image ( fun a => ‖a‖ ) K ) from le_csSup ( by exact IsCompact.bddAbove ( hK.image ( continuous_norm ) ) ) ( Set.mem_image_of_mem _ hx ) ) ( by positivity ) 
    · exact fun i => ContinuousOn.mul ( continuousOn_id.neg ) ( continuousOn_const )
    · convert tendstoUniformlyOn_prod_range_of_finset this.tendstoUniformlyOn using 1
      · exact funext fun n => funext fun x => Finset.prod_congr rfl fun _ _ => by ring
      · exact funext fun x => tprod_congr fun i => by ring
  rw [ Metric.tendstoLocallyUniformly_iff ]
  intro ε hε x
  have := h_uniform ( Metric.closedBall x 1 ) ( ProperSpace.isCompact_closedBall x 1 )
  rw [ Metric.tendstoUniformlyOn_iff ] at this
  exact ⟨ Metric.closedBall x 1, Metric.closedBall_mem_nhds _ zero_lt_one, this ε hε ⟩

/-- The partial sums of the bilateral Jacobi series converge locally uniformly on $\{z \neq 0\}$ for fixed $\|q\| < 1$. -/
theorem jacobiBilateral_tendstoLocallyUniformlyOn {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun N z =>
        (∑ k ∈ Finset.range N, z ^ k * q ^ k.choose 2) +
        (∑ m ∈ Finset.range N, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2))
      (fun z => jacobiBilateral q z) atTop {z : ℂ | z ≠ 0} := by
  refine TendstoLocallyUniformlyOn.add ?_ ?_
  · apply TendstoLocallyUniformly.tendstoLocallyUniformlyOn
    have h_nonneg : ∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn (fun N z => ∑ k ∈ Finset.range N, z ^ k * q ^ k.choose 2) (fun z => ∑' k : ℕ, z ^ k * q ^ k.choose 2) atTop (Metric.closedBall 0 R) := by
      grind +suggestions
    rw [ Metric.tendstoLocallyUniformly_iff ]
    intro ε hε x; specialize h_nonneg ( ‖x‖ + 1 ) ( by positivity ) ; rw [ Metric.tendstoUniformlyOn_iff ] at h_nonneg
    exact ⟨ Metric.closedBall 0 ( ‖x‖ + 1 ), Metric.closedBall_mem_nhds_of_mem ( by norm_num ), h_nonneg ε hε ⟩
  ·
    have h_neg : ∀ z₀ : ℂ, z₀ ≠ 0 → ∃ r > 0, TendstoUniformlyOn (fun N z => ∑ m ∈ Finset.range N, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2) (jacobiBilateralNeg q) atTop (Metric.ball z₀ r ∩ {z | z ≠ 0}) := by
      intro z₀ hz₀
      obtain ⟨r, hr_pos, hr⟩ : ∃ r > 0, ∀ z ∈ Metric.ball z₀ r, ‖z⁻¹‖ ≤ 2 / ‖z₀‖ := by
        have := Metric.continuousAt_iff.mp ( show ContinuousAt ( fun z : ℂ => ‖z⁻¹‖ ) z₀ from ContinuousAt.norm <| ContinuousAt.inv₀ continuousAt_id hz₀ )
        obtain ⟨ δ, δ_pos, H ⟩ := this ( ‖z₀⁻¹‖ ) ( norm_pos_iff.mpr <| inv_ne_zero hz₀ ) ; exact ⟨ δ, δ_pos, fun z hz => by have := H hz; norm_num at *; ring_nf at *; linarith [ abs_lt.mp this ] ⟩ 
      refine ⟨ r, hr_pos, ?_ ⟩
      have := @neg_tendstoUniformlyOn_ball q hq ( 2 / ‖z₀‖ ) ( by positivity )
      exact this.mono fun x hx => hr x hx.1
    intro ε hε
    intro z₀ hz₀
    obtain ⟨r, hr₀, hr⟩ := h_neg z₀ hz₀
    use Metric.ball z₀ r ∩ {z | z ≠ 0}
    simp_all +decide [ Metric.mem_nhdsWithin_iff ]
    exact ⟨ ⟨ ⟨ r, hr₀, fun x hx => hx.1 ⟩, ⟨ 1, zero_lt_one ⟩ ⟩, by rcases Filter.eventually_atTop.mp ( hr ε hε ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn y hy₁ hy₂ => hN n hn y ⟨ hy₁, hy₂ ⟩ ⟩ ⟩

/-- Uniform convergence of the product of two bounded sequences in a normed ring. -/
lemma TendstoUniformlyOn.mul_of_bounded {s : Set ℂ}
    {f₁ f₂ : ℕ → ℂ → ℂ} {F₁ F₂ : ℂ → ℂ}
    (h₁ : TendstoUniformlyOn f₁ F₁ atTop s)
    (h₂ : TendstoUniformlyOn f₂ F₂ atTop s)
    (hb₁ : ∃ C, ∀ n, ∀ z ∈ s, ‖f₁ n z‖ ≤ C)
    (hb₂ : ∃ C, ∀ z ∈ s, ‖F₂ z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => f₁ n z * f₂ n z) (fun z => F₁ z * F₂ z) atTop s := by
  by_cases hs : s.Nonempty
  · rw [ Metric.tendstoUniformlyOn_iff ] at *
    obtain ⟨ C₁, hC₁ ⟩ := hb₁
    obtain ⟨ C₂, hC₂ ⟩ := hb₂
    have h_bound₁ : ∀ n, ∀ z ∈ s, ‖f₁ n z‖ ≤ C₁ := by
      assumption
    have h_bound₂ : ∀ z ∈ s, ‖F₂ z‖ ≤ C₂ := by
      assumption
    have h_diff : ∀ n, ∀ z ∈ s, ‖F₁ z * F₂ z - f₁ n z * f₂ n z‖ ≤ ‖F₁ z - f₁ n z‖ * ‖F₂ z‖ + ‖f₁ n z‖ * ‖F₂ z - f₂ n z‖ := by
      intro n z hz; rw [ ← norm_mul, ← norm_mul ] ; convert norm_add_le ( ( F₁ z - f₁ n z ) * F₂ z ) ( f₁ n z * ( F₂ z - f₂ n z ) ) using 2 ; ring
    intro ε hε
    obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ n ≥ N₁, ∀ z ∈ s, ‖F₁ z - f₁ n z‖ < ε / (2 * (C₂ + 1)) := by
      simpa [dist_eq_norm] using h₁ ( ε / ( 2 * ( C₂ + 1 ) ) ) ( div_pos hε ( mul_pos zero_lt_two ( add_pos_of_nonneg_of_pos ( le_trans ( norm_nonneg _ ) ( h_bound₂ _ hs.choose_spec ) ) zero_lt_one ) ) )
    obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ n ≥ N₂, ∀ z ∈ s, ‖F₂ z - f₂ n z‖ < ε / (2 * (C₁ + 1)) := by
      simpa [dist_eq_norm] using h₂ ( ε / ( 2 * ( C₁ + 1 ) ) ) ( div_pos hε ( mul_pos zero_lt_two ( add_pos_of_nonneg_of_pos ( le_trans ( norm_nonneg _ ) ( h_bound₁ 0 _ hs.choose_spec ) ) zero_lt_one ) ) )
    filter_upwards [ Filter.eventually_ge_atTop N₁, Filter.eventually_ge_atTop N₂ ] with n hn₁ hn₂ z hz
    rw [dist_eq_norm]
    refine lt_of_le_of_lt ( h_diff n z hz ) ?_
    refine lt_of_le_of_lt ( add_le_add ( mul_le_mul_of_nonneg_left ( h_bound₂ z hz ) ( norm_nonneg _ ) ) ( mul_le_mul_of_nonneg_right ( h_bound₁ n z hz ) ( norm_nonneg _ ) ) ) ?_
    have := hN₁ n hn₁ z hz; have := hN₂ n hn₂ z hz; rw [ lt_div_iff₀ ] at * <;> nlinarith [ norm_nonneg ( F₁ z - f₁ n z ), norm_nonneg ( F₂ z - f₂ n z ), show 0 ≤ C₁ by exact le_trans ( norm_nonneg _ ) ( h_bound₁ 0 z hz ), show 0 ≤ C₂ by exact le_trans ( norm_nonneg _ ) ( h_bound₂ z hz ) ] 
  · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hs, TendstoUniformlyOn ]

/-- The partial Pochhammer products are uniformly bounded on any closed ball. -/
lemma qPochhammer_bounded_on_closedBall {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    ∃ C, ∀ n, ∀ a ∈ Metric.closedBall (0 : ℂ) R, ‖qPochhammer a q n‖ ≤ C := by
  use Real.exp (R / (1 - ‖q‖))
  intro n a ha
  have h_prod_le : ‖qPochhammer a q n‖ ≤ ∏ k ∈ Finset.range n, (1 + R * ‖q‖ ^ k) := by
    have h_bound : ∀ k ∈ Finset.range n, ‖1 - a * q ^ k‖ ≤ 1 + R * ‖q‖ ^ k := by
      intros k hk; exact le_trans (norm_sub_le _ _) (by simpa [norm_mul] using add_le_add_left (mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.mp ha) (pow_nonneg (norm_nonneg q) k)) 1) 
    simpa [ qPochhammer ] using Finset.prod_le_prod ( fun _ _ => norm_nonneg _ ) h_bound
  have h_exp_bound : ∏ k ∈ Finset.range n, (1 + R * ‖q‖ ^ k) ≤ Real.exp (∑ k ∈ Finset.range n, R * ‖q‖ ^ k) := by
    rw [ Real.exp_sum ] ; exact Finset.prod_le_prod ( fun _ _ => by nlinarith [ show 0 ≤ R by exact le_trans ( norm_nonneg a ) ( mem_closedBall_zero_iff.mp ha ), show 0 ≤ ‖q‖ ^ ‹_› by positivity ] ) fun _ _ => by rw [ add_comm ] ; exact Real.add_one_le_exp _
  refine le_trans h_prod_le <| h_exp_bound.trans <| Real.exp_le_exp.mpr ?_
  rw [ ← Finset.mul_sum _ _ _, div_eq_mul_inv ]
  exact mul_le_mul_of_nonneg_left ( by rw [ ← tsum_geometric_of_lt_one ( by positivity ) hq ] ; exact Summable.sum_le_tsum ( Finset.range n ) ( fun _ _ => by positivity ) ( by exact summable_geometric_of_lt_one ( by positivity ) hq ) ) ( by linarith [ norm_nonneg a, mem_closedBall_zero_iff.mp ha ] )

/-- The Pochhammer products $(a;q)_n$ converge uniformly on any closed ball as $n \to \infty$. -/
lemma qPochhammer_tendstoUniformlyOn_closedBall {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    TendstoUniformlyOn (fun n a => qPochhammer a q n)
      (fun a => qPochhammerInf a q) atTop (Metric.closedBall 0 R) := by
  have h_uniform : ∀ {s : Set ℂ}, IsCompact s → TendstoLocallyUniformlyOn (fun n a => qPochhammer a q n) (fun a => qPochhammerInf a q) atTop s → TendstoUniformlyOn (fun n a => qPochhammer a q n) (fun a => qPochhammerInf a q) atTop s := by
    grind +suggestions
  apply h_uniform
  · exact ProperSpace.isCompact_closedBall _ _
  · convert qPochhammer_tendstoLocallyUniformly hq |> fun h => h.tendstoLocallyUniformlyOn using 1

/-- The infinite Pochhammer product $\mathrm{qPochhammerInf}$ is uniformly bounded on any closed ball. -/
lemma qPochhammerInf_bounded_on_closedBall {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    ∃ C, ∀ a ∈ Metric.closedBall (0 : ℂ) R, ‖qPochhammerInf a q‖ ≤ C := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ∀ a ∈ Metric.closedBall 0 R, ‖qPochhammer a q n‖ ≤ C :=
    qPochhammer_bounded_on_closedBall hq R
  use C + 1
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ a ∈ Metric.closedBall 0 R, ‖qPochhammerInf a q - qPochhammer a q n‖ < 1 := by
    have := qPochhammer_tendstoUniformlyOn_closedBall hq R
    rw [ Metric.tendstoUniformlyOn_iff ] at this
    simpa [dist_eq_norm] using this 1 zero_lt_one
  intro a ha; specialize hN N le_rfl a ha; specialize hC N a ha; exact le_trans ( by simpa using norm_add_le ( qPochhammerInf a q - qPochhammer a q N ) ( qPochhammer a q N ) ) ( by linarith )

/-- For `z` in the closed ball of radius `‖z₀‖ / 2` around `z₀ ≠ 0`,
`-q / z` lies in the closed ball of radius `2 * ‖q‖ / ‖z₀‖` around `0`. -/
lemma neg_q_div_mem_closedBall {q z₀ z : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : z ∈ Metric.closedBall z₀ (‖z₀‖ / 2)) :
    -q / z ∈ Metric.closedBall (0 : ℂ) (2 * ‖q‖ / ‖z₀‖) := by
  simp +zetaDelta at *
  rw [ div_le_div_iff₀ ] <;> try positivity
  · have := norm_sub_norm_le z₀ z; rw [ dist_eq_norm' ] at hz; nlinarith [ norm_nonneg q, norm_nonneg z, norm_nonneg z₀ ] 
  · contrapose! hz₀; simp_all +decide [ dist_eq_norm ]
    exact norm_le_zero_iff.mp (by linarith [norm_nonneg z₀])

/-- The Pochhammer products `qPochhammer (-z) q n` converge uniformly to
`qPochhammerInf (-z) q` on any `Metric.closedBall z₀ r` when `‖q‖ < 1`. -/
lemma qPochhammer_neg_tendstoUniformlyOn_closedBall {q : ℂ} (hq : ‖q‖ < 1) (z₀ : ℂ) (r : ℝ) :
    TendstoUniformlyOn (fun n z => qPochhammer (-z) q n)
      (fun z => qPochhammerInf (-z) q) atTop (Metric.closedBall z₀ r) := by
  have h_subset : TendstoUniformlyOn (fun n z => qPochhammer z q n) (fun z => qPochhammerInf z q) atTop (Metric.closedBall 0 (‖z₀‖ + r)) :=
    qPochhammer_tendstoUniformlyOn_closedBall hq (‖z₀‖ + r)
  intro ε hε
  filter_upwards [h_subset ε hε] with n hn
  intro x hx; specialize hn (-x); simp_all +decide [Metric.mem_closedBall, dist_eq_norm]
  exact hn (by linarith [norm_sub_norm_le x z₀])

/-- The Pochhammer products `qPochhammer (-q / z) q n` converge uniformly to
`qPochhammerInf (-q / z) q` on `Metric.closedBall z₀ (‖z₀‖ / 2)` for `z₀ ≠ 0`,
`‖q‖ < 1`. -/
lemma qPochhammer_neg_q_div_tendstoUniformlyOn {q : ℂ} (hq : ‖q‖ < 1) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    TendstoUniformlyOn (fun n z => qPochhammer (-q / z) q n)
      (fun z => qPochhammerInf (-q / z) q) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) := by
  have h_neg_q_div_mem_closedBall : ∀ z ∈ Metric.closedBall z₀ (‖z₀‖ / 2), -q / z ∈ Metric.closedBall 0 (2 * ‖q‖ / ‖z₀‖) :=
    fun z hz => neg_q_div_mem_closedBall hz₀ hz
  rw [ Metric.tendstoUniformlyOn_iff ]
  have := Metric.tendstoUniformlyOn_iff.mp ( qPochhammer_tendstoUniformlyOn_closedBall hq ( 2 * ‖q‖ / ‖z₀‖ ) )
  exact fun ε hε => by filter_upwards [ this ε hε ] with n hn x hx using hn _ ( h_neg_q_div_mem_closedBall x hx ) 

/-- The partial products `qPochhammer q q n * qPochhammer (-z) q n * qPochhammer (-q / z) q n`
converge locally uniformly to `jacobiProd q z` on `{z : ℂ | z ≠ 0}` when `‖q‖ < 1`. -/
theorem jacobiProd_tendstoLocallyUniformlyOn {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun n z => qPochhammer q q n * qPochhammer (-z) q n * qPochhammer (-q / z) q n)
      (fun z => jacobiProd q z) atTop {z : ℂ | z ≠ 0} := by
  have h_suff : ∀ z₀ : ℂ, z₀ ≠ 0 → TendstoUniformlyOn (fun n z => qPochhammer q q n * qPochhammer (-z) q n * qPochhammer (-q / z) q n) (fun z => jacobiProd q z) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) := by
    intro z₀ hz₀
    set R₁ := ‖z₀‖ + ‖z₀‖ / 2
    set R₂ := 2 * ‖q‖ / ‖z₀‖
    have h_neg : TendstoUniformlyOn (fun n z => qPochhammer (-z) q n) (fun z => qPochhammerInf (-z) q) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) := by
      apply qPochhammer_neg_tendstoUniformlyOn_closedBall hq z₀ (‖z₀‖ / 2)
    have h_div : TendstoUniformlyOn (fun n z => qPochhammer (-q / z) q n) (fun z => qPochhammerInf (-q / z) q) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) := by
      convert qPochhammer_neg_q_div_tendstoUniformlyOn hq hz₀ using 1
    have h_qq : TendstoUniformlyOn (fun n z => qPochhammer q q n) (fun z => qPochhammerInf q q) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) := by
      rw [ Metric.tendstoUniformlyOn_iff ]
      intro ε hε
      have := qPochhammer_tendstoUniformlyOn_closedBall hq 1
      rw [ Metric.tendstoUniformlyOn_iff ] at this
      filter_upwards [ this ε hε ] with n hn using fun x hx => by simpa using hn q ( by simpa using hq.le ) 
    have h_BC := TendstoUniformlyOn.mul_of_bounded h_neg h_div (by
    obtain ⟨ C, hC ⟩ := qPochhammer_bounded_on_closedBall hq R₁
    use C
    intro n z hz
    convert hC n ( -z ) _ using 1
    simp +zetaDelta at *
    exact le_trans ( norm_le_of_mem_closedBall hz ) ( by linarith [ norm_nonneg z₀ ] )) (by
    exact qPochhammerInf_bounded_on_closedBall hq R₂ |> fun ⟨ C, hC ⟩ => ⟨ C, fun z hz => hC _ <| neg_q_div_mem_closedBall hz₀ hz ⟩)
    have h_ABC : TendstoUniformlyOn (fun n z => qPochhammer q q n * (qPochhammer (-z) q n * qPochhammer (-q / z) q n)) (fun z => qPochhammerInf q q * (qPochhammerInf (-z) q * qPochhammerInf (-q / z) q)) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) := by
      apply_rules [ TendstoUniformlyOn.mul_of_bounded ]
      · have := qPochhammer_bounded_on_closedBall hq 1
        exact ⟨ this.choose, fun n z hz => this.choose_spec n q <| by simpa using hq.le ⟩
      · obtain ⟨ C₁, hC₁ ⟩ := qPochhammerInf_bounded_on_closedBall hq R₁
        obtain ⟨ C₂, hC₂ ⟩ := qPochhammerInf_bounded_on_closedBall hq R₂
        use C₁ * C₂
        intro z hz
        have hz₁ : ‖-z‖ ≤ R₁ := by
          simp +zetaDelta at *
          exact le_trans ( norm_le_of_mem_closedBall hz ) ( by nlinarith [norm_nonneg z₀] )
        have hz₂ : ‖-q / z‖ ≤ R₂ := by
          exact neg_q_div_mem_closedBall hz₀ hz |> fun h => by simpa using h.out
        exact (by
        simpa only [ norm_mul ] using mul_le_mul ( hC₁ _ <| mem_closedBall_zero_iff.mpr hz₁ ) ( hC₂ _ <| mem_closedBall_zero_iff.mpr hz₂ ) ( by positivity ) ( by exact le_trans ( by positivity ) ( hC₁ _ <| mem_closedBall_zero_iff.mpr hz₁ ) ))
    simpa only [ ← mul_assoc, jacobiProd ] using h_ABC
  intro ε hε
  intro z₀ hz₀
  refine ⟨ Metric.closedBall z₀ ( ‖z₀‖ / 2 ) ∩ { z | z ≠ 0 }, ?_, ?_ ⟩
  · exact mem_nhdsWithin_of_mem_nhds ( Filter.inter_mem ( Metric.closedBall_mem_nhds _ <| half_pos <| norm_pos_iff.mpr hz₀ ) <| isOpen_ne.mem_nhds hz₀ )
  · have := h_suff z₀ hz₀ ε hε
    exact this.mono fun n hn y hy => hn y hy.1

/-- The bilateral series satisfies $g(qz) = g(z)/z$ for **all** $z \neq 0$. -/
theorem jacobiBilateral_fe_all {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0)
    (hz' : z ≠ 0) :
    jacobiBilateral q (q * z) = jacobiBilateral q z / z := by
  have h_split : jacobiBilateral q (q * z) =
      jacobiBilateralPos q (q * z) + jacobiBilateralNeg q (q * z) := rfl
  have h_pos : jacobiBilateralPos q (q * z) = (jacobiBilateralPos q z - 1) / z := by
    unfold jacobiBilateralPos
    rw [eq_div_iff hz']; symm
    simp +decide [pow_succ, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left]
    rw [← Summable.sum_add_tsum_nat_add 1]
    · norm_num [pow_succ', mul_pow, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left]
      norm_num [Nat.choose_succ_succ, pow_add, mul_assoc, mul_comm, mul_left_comm]
    · convert summable_jacobi_nonneg_all hq using 1
  have h_neg : jacobiBilateralNeg q (q * z) = (jacobiBilateralNeg q z + 1) / z := by
    unfold jacobiBilateralNeg
    simp +decide [*, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ,
                   tsum_mul_left]; ring
    rw [Summable.tsum_eq_zero_add]; norm_num [hq', hz']; ring
    · simp +decide [hq', mul_assoc, mul_comm, mul_left_comm, pow_add, pow_one, pow_mul,
                     tsum_mul_left, tsum_mul_right]; ring
      rw [← tsum_mul_left]; rw [← tsum_mul_left]; congr; ext x
      rw [show (3 + x).choose 2 = (2 + x).choose 2 + (2 + x) by
            simp +arith +decide [Nat.choose]]; ring
      simp +decide [mul_assoc, mul_comm, mul_left_comm, hq']
    · have := summable_jacobi_neg hq (show q * z ≠ 0 by aesop)
      convert this.mul_left (q * z) using 2; ring
      simp +decide [hq', hz', mul_assoc, mul_comm q]
  rw [h_split, h_pos, h_neg,
      show jacobiBilateral q z = jacobiBilateralPos q z + jacobiBilateralNeg q z from rfl]
  ring

/-- Iterating the product-side FE $N$ times. -/
theorem jacobiProd_iterate {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0)
    (hz : z ≠ 0) (N : ℕ) :
    jacobiProd q z = z ^ N * q ^ N.choose 2 * jacobiProd q (q ^ N * z) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [ih, pow_succ']
      rw [show jacobiProd q (q ^ N * z) =
            jacobiProd q (q * (q ^ N * z)) * (q ^ N * z) by
        rw [eq_comm, jacobiProd_fe]
        · rw [div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hq') hz)]
        · exact hq
        · assumption
        · aesop]; ring
      rw [show (1 + N).choose 2 = N.choose 2 + N by
        rw [Nat.add_comm, Nat.choose_succ_succ]; norm_num; ring]; ring

/-- Iterating the series-side FE $N$ times. -/
theorem jacobiBilateral_iterate {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0)
    (hz : z ≠ 0) (N : ℕ) :
    jacobiBilateral q z =
      z ^ N * q ^ N.choose 2 * jacobiBilateral q (q ^ N * z) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      have h_fe : jacobiBilateral q (q * (q ^ N * z)) =
          jacobiBilateral q (q ^ N * z) / (q ^ N * z) :=
        jacobiBilateral_fe_all hq hq' (mul_ne_zero (pow_ne_zero _ hq') hz)
      simp_all +decide [Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm,
                         mul_left_comm, div_eq_mul_inv]
      simp +decide [pow_add, mul_assoc, mul_left_comm, hq']

/-- **Analytic Jacobi triple product identity.**
For $\|q\| < 1$ and $z \neq 0$:
$$(q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty
  \;=\; \sum_{k \in \mathbb{Z}} z^k \, q^{k(k-1)/2}.$$

This extends the basic JTP (which required $\|z\| < 1$) to **all** $z \neq 0$
using the functional equation $f(qz) = f(z)/z$ satisfied by both sides. -/
theorem jacobiTripleProduct_analytic {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    jacobiProd q z = jacobiBilateral q z := by
  by_cases hq' : q = 0
  · subst hq'
    unfold jacobiProd jacobiBilateral jacobiBilateralPos jacobiBilateralNeg qPochhammerInf
    norm_num [Finset.sum_range_succ', Nat.choose]
    rw [tprod_eq_prod, tsum_eq_sum]
    any_goals exact {0, 1}
    · norm_num [Finset.prod, Finset.sum]
    · rintro (_ | _ | b) <;> simp +decide [Nat.choose]
    · aesop
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖q ^ N * z‖ < 1 := by
      simpa using (summable_geometric_of_lt_one (by positivity) hq) |> fun h =>
        h.mul_right _ |> fun h =>
        h.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one) |> fun h => h.exists
    rw [jacobiProd_iterate hq hq' hz N,
        jacobiBilateral_iterate hq hq' hz N,
        jacobiTripleProduct hq hN (by aesop)]

end

end qSeries