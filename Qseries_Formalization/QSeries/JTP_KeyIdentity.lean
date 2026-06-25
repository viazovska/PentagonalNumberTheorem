/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import QSeries.EulerIdentities

/-!
# Key identity for the Jacobi triple product

We prove that for ‖q‖ < 1 and all k ≥ 0:

$$S_k(q) := \sum_{m=0}^{\infty} \frac{q^{m(m+k)}}{(q;q)_m (q;q)_{m+k}} = \frac{1}{(q;q)_\infty}$$

The proof uses a recurrence:
  S_k - S_{k+1} = q^{k+1} (S_{k+2} - S_{k+1})

This forces all differences to be zero (since S_k → 1/(q;q)_∞),
so all S_k are equal to 1/(q;q)_∞.
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-- The key sum S_k(q) = Σ_{m≥0} q^{m(m+k)} / ((q;q)_m (q;q)_{m+k}). -/
def S_sum (q : ℂ) (k : ℕ) : ℂ :=
  ∑' m : ℕ, q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))

/-- The summand of S_k. -/
def S_summand (q : ℂ) (k : ℕ) (m : ℕ) : ℂ :=
  q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))

/-- Unfolds `S_sum` as the tsum of `S_summand`. -/
theorem S_sum_eq_tsum (q : ℂ) (k : ℕ) :
    S_sum q k = ∑' m, S_summand q k m := rfl

/-- The series defining $S_k(q)$ is summable for $\|q\| < 1$. -/
theorem summable_S_summand {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (S_summand q k) := by
  have h_summable : Summable (fun m : ℕ => (q ^ (m * (m + k))) / (qPochhammer q q m * qPochhammer q q (m + k))) := by
    have h_bound : ∃ C > 0, ∀ m : ℕ, ‖qPochhammer q q m * qPochhammer q q (m + k)‖ ≥ C := by
      have h_prod_nonzero : ∃ C > 0, ∀ m : ℕ, ‖qPochhammer q q m‖ ≥ C := by
        have h_prod_conv : Summable (fun j : ℕ => ‖q ^ j‖) := by
          simpa using summable_geometric_of_lt_one ( norm_nonneg q ) hq
        have h_prod_conv : ∃ C > 0, ∀ m : ℕ, ‖∏ j ∈ Finset.range m, (1 - q ^ (j + 1))‖ ≥ C := by
          have h_prod_conv : ∃ C > 0, ∀ m : ℕ, ‖∏ j ∈ Finset.range m, (1 - q ^ (j + 1))‖ ≥ Real.exp (-∑ j ∈ Finset.range m, ‖q ^ (j + 1)‖ / (1 - ‖q ^ (j + 1)‖)) := by
            have h_prod_conv : ∀ m : ℕ, ‖∏ j ∈ Finset.range m, (1 - q ^ (j + 1))‖ ≥ Real.exp (-∑ j ∈ Finset.range m, ‖q ^ (j + 1)‖ / (1 - ‖q ^ (j + 1)‖)) := by
              intros m
              have h_prod_conv : ∀ j ∈ Finset.range m, ‖1 - q ^ (j + 1)‖ ≥ Real.exp (-‖q ^ (j + 1)‖ / (1 - ‖q ^ (j + 1)‖)) := by
                intros j hj
                have h_exp : ‖1 - q ^ (j + 1)‖ ≥ 1 - ‖q ^ (j + 1)‖ := by
                  simpa using norm_sub_norm_le ( 1 : ℂ ) ( q ^ ( j + 1 ) )
                have h_exp : ∀ x : ℝ, 0 ≤ x ∧ x < 1 → 1 - x ≥ Real.exp (-x / (1 - x)) := by
                  intros x hx
                  have h_exp : Real.exp (-x / (1 - x)) ≤ 1 - x := by
                    rw [ neg_div, Real.exp_neg ]
                    rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith [ Real.add_one_le_exp ( x / ( 1 - x ) ), mul_div_cancel₀ x ( by linarith [hx.2] : ( 1 - x ) ≠ 0 ) ]
                  exact h_exp
                exact le_trans ( h_exp _ ⟨ by positivity, by simpa using pow_lt_one₀ ( by positivity ) hq ( by omega ) ⟩ ) ‹‖1 - q ^ ( j + 1 )‖ ≥ 1 - ‖q ^ ( j + 1 )‖›
              simpa [ neg_div, Real.exp_neg, Real.exp_sum ] using Finset.prod_le_prod ( fun _ _ => by positivity ) h_prod_conv
            exact ⟨ 1, zero_lt_one, h_prod_conv ⟩
          have h_prod_conv : Summable (fun j : ℕ => ‖q ^ (j + 1)‖ / (1 - ‖q ^ (j + 1)‖)) := by
            have h_prod_conv : Summable (fun j : ℕ => ‖q ^ (j + 1)‖ / (1 - ‖q‖)) := by
              exact Summable.mul_right _ ( by simpa using summable_nat_add_iff 1 |>.2 ‹Summable fun j : ℕ => ‖q ^ j‖› )
            refine .of_nonneg_of_le ( fun j => div_nonneg ( norm_nonneg _ ) ( sub_nonneg.mpr ( by simpa using pow_le_one₀ ( norm_nonneg q ) hq.le ) ) ) ( fun j => ?_ ) h_prod_conv
            gcongr
            · linarith
            · simpa using pow_le_of_le_one ( norm_nonneg q ) hq.le ( by norm_num )
          have h_prod_conv : ∃ C > 0, ∀ m : ℕ, Real.exp (-∑ j ∈ Finset.range m, ‖q ^ (j + 1)‖ / (1 - ‖q ^ (j + 1)‖)) ≥ C := by
            exact ⟨ Real.exp ( -∑' j : ℕ, ‖q ^ ( j + 1 )‖ / ( 1 - ‖q ^ ( j + 1 )‖ ) ), Real.exp_pos _, fun m => Real.exp_le_exp.mpr <| neg_le_neg <| Summable.sum_le_tsum ( Finset.range m ) ( fun _ _ => div_nonneg ( norm_nonneg _ ) <| sub_nonneg.mpr <| by simpa using pow_le_one₀ ( norm_nonneg _ ) hq.le ) h_prod_conv ⟩
          grind
        obtain ⟨ C, hC₀, hC ⟩ := h_prod_conv; use C, hC₀; intro m; specialize hC m; simp_all +decide [ qPochhammer ] 
        simpa only [ pow_succ' ] using hC
      obtain ⟨ C, hC₀, hC ⟩ := h_prod_nonzero; exact ⟨ C ^ 2, sq_pos_of_pos hC₀, fun m => by simpa only [ sq, norm_mul ] using mul_le_mul ( hC m ) ( hC ( m + k ) ) ( by positivity ) ( by positivity ) ⟩ 
    have h_summable : Summable (fun m : ℕ => ‖q ^ (m * (m + k))‖ / h_bound.choose) := by
      refine Summable.mul_right _ ?_
      have h_summable : Summable (fun m : ℕ => ‖q‖ ^ (m ^ 2)) := by
        exact Summable.comp_injective ( summable_geometric_of_lt_one ( norm_nonneg q ) hq ) fun a b h => by simpa using h
      exact Summable.of_nonneg_of_le ( fun m => by positivity ) ( fun m => by simpa using pow_le_pow_of_le_one ( by positivity ) hq.le ( by nlinarith ) ) h_summable
    refine .of_norm <| h_summable.of_nonneg_of_le ( fun m => by positivity ) ( fun m => ?_ )
    simpa using div_le_div_of_nonneg_left ( by positivity ) ( by linarith [ h_bound.choose_spec.1 ] ) ( h_bound.choose_spec.2 m )
  convert h_summable using 1

/-- As $k \to \infty$, $S_k(q)$ converges to $1/(q;q)_\infty$. -/
theorem S_sum_tendsto {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (S_sum q) atTop (𝓝 (1 / qPochhammerInf q q)) := by
  have h_m_zero : Filter.Tendsto (fun k => 1 / qPochhammer q q k) Filter.atTop (nhds (1 / qPochhammerInf q q)) := by
    convert tendsto_const_nhds.div ( tendsto_qPochhammer hq ) _ using 1 ; norm_num
    convert qPochhammerInf_z_q_ne_zero hq hq using 1
  have h_bound : ∃ C > 0, ∀ m ≥ 1, ∀ k : ℕ, ‖qPochhammer q q m * qPochhammer q q (m + k)‖ ≥ C := by
    have h_qPochhammer_bound : ∃ C > 0, ∀ m ≥ 1, ‖qPochhammer q q m‖ ≥ C := by
      have h_bound : Filter.Tendsto (fun m => ‖qPochhammer q q m‖) Filter.atTop (nhds (‖qPochhammerInf q q‖)) := by
        convert Filter.Tendsto.norm ( tendsto_qPochhammer hq ) using 1
      have h_bound : ‖qPochhammerInf q q‖ > 0 := by
        exact norm_pos_iff.mpr ( qPochhammerInf_z_q_ne_zero hq hq )
      have := Metric.tendsto_atTop.mp ‹_› ( ‖qPochhammerInf q q‖ / 2 ) ( half_pos h_bound )
      obtain ⟨ N, hN ⟩ := this
      use min (‖qPochhammerInf q q‖ / 2) (Finset.min' (Finset.image (fun m => ‖qPochhammer q q m‖) (Finset.range (N + 1))) (by
      exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ⟩))
      generalize_proofs at *
      simp_all +decide [ Finset.min' ]
      refine ⟨ ?_, ?_ ⟩
      · intro i hi; exact qPochhammer_q_q_ne_zero hq i
      · exact fun m hm => if hm' : m ≤ N then Or.inr ⟨ m, hm', le_rfl ⟩ else Or.inl <| by linarith [ abs_lt.mp ( hN m ( le_of_not_ge hm' ) ) ] 
    obtain ⟨ C, hC₀, hC ⟩ := h_qPochhammer_bound; use C * C; exact ⟨ mul_pos hC₀ hC₀, fun m hm k => by simpa [ mul_assoc ] using mul_le_mul ( hC m hm ) ( hC ( m + k ) ( by omega ) ) ( by positivity ) ( by positivity ) ⟩ 
  have h_sum_zero : Filter.Tendsto (fun k => ∑' m : ℕ, (if m = 0 then 0 else q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)))) Filter.atTop (nhds 0) := by
    have h_dominated : ∀ m ≥ 1, Filter.Tendsto (fun k => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))) Filter.atTop (nhds 0) := by
      intro m hm
      have h_lim : Filter.Tendsto (fun k => q ^ (m * (m + k))) Filter.atTop (nhds 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun k => by nlinarith ) tendsto_natCast_atTop_atTop
      rw [ tendsto_zero_iff_norm_tendsto_zero ] at *
      exact squeeze_zero ( fun _ => by positivity ) ( fun k => by simpa using div_le_div_of_nonneg_left ( by positivity ) ( by linarith [ h_bound.choose_spec.1 ] ) ( h_bound.choose_spec.2 m hm k ) ) ( by simpa using h_lim.div_const h_bound.choose )
    have h_dominated_convergence : Filter.Tendsto (fun k => ∑' m : ℕ, (if m = 0 then 0 else q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)))) Filter.atTop (nhds (∑' m : ℕ, (if m = 0 then 0 else 0))) := by
      refine' ( tendsto_tsum_of_dominated_convergence _ _ _ )
      use fun k => if k = 0 then 0 else ‖q‖ ^ ( k * k ) / h_bound.choose
      · rw [ ← summable_nat_add_iff 1 ]
        exact Summable.mul_right _ <| Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by exact pow_le_pow_of_le_one ( by positivity ) hq.le <| by nlinarith ) <| summable_geometric_of_lt_one ( by positivity ) hq
      · intro k; by_cases hk : k = 0 <;> simp +decide [ hk, h_dominated ] 
        exact h_dominated k ( Nat.pos_of_ne_zero hk )
      · refine Filter.Eventually.of_forall fun n k => ?_
        split_ifs <;> simp_all +decide [ div_eq_mul_inv ]
        refine mul_le_mul ?_ ?_ ?_ ?_
        · exact pow_le_pow_of_le_one ( norm_nonneg _ ) hq.le ( by nlinarith )
        · have := h_bound.choose_spec.2 k ( Nat.pos_of_ne_zero ‹_› ) n
          simpa [ mul_comm ] using inv_anti₀ ( h_bound.choose_spec.1 ) this
        · positivity
        · positivity
    aesop
  convert h_m_zero.add h_sum_zero using 2 <;> norm_num [ S_sum ]
  rw [ Summable.tsum_eq_add_tsum_ite ]
  any_goals exact Nat.zero
  · norm_num [ qPochhammer ]
  · convert summable_S_summand hq _ using 1

set_option maxHeartbeats 400000 in
/-- The recurrence $S_k - S_{k+1} = q^{k+1}(S_{k+2} - S_{k+1})$ satisfied by $S_k(q)$. -/
theorem S_sum_recurrence {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    S_sum q k - S_sum q (k + 1) = q ^ (k + 1) * (S_sum q (k + 2) - S_sum q (k + 1)) := by
  have h_split : ∑' m : ℕ, (q ^ (m * (m + k)) * (1 - q ^ m - q ^ (m + k + 1))) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) = q ^ (k + 1) * (S_sum q (k + 2) - S_sum q (k + 1)) := by
    have h_split : ∑' m : ℕ, q ^ (m * (m + k)) * (1 - q ^ m) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) = ∑' m : ℕ, q ^ ((m + 1) * (m + 1 + k)) / (qPochhammer q q m * qPochhammer q q (m + k + 2)) := by
      rw [ Summable.tsum_eq_zero_add ]
      · norm_num [ qPochhammer_succ ]
        refine tsum_congr fun m => ?_
        convert mul_div_mul_right _ _ ( show ( 1 - q ^ ( m + 1 ) ) ≠ 0 from sub_ne_zero_of_ne <| Ne.symm <| by exact ne_of_apply_ne Norm.norm <| by norm_num; exact ne_of_lt <| pow_lt_one₀ ( by positivity ) hq <| by positivity ) using 1 ; ring
        rw [ show 1 + m + k = m + k + 1 by ring ] ; rw [ qPochhammer_succ ] ; ring
      · have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k + 1))) := by
          have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))) := by
            convert summable_S_summand hq k using 1
          have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)) * (1 / (1 - q ^ (m + k + 1)))) := by
            have h_summable : ∃ C > 0, ∀ m : ℕ, ‖1 / (1 - q ^ (m + k + 1))‖ ≤ C := by
              have h_summable : ∃ C > 0, ∀ m : ℕ, ‖1 - q ^ (m + k + 1)‖ ≥ C := by
                have h_lim : Filter.Tendsto (fun m : ℕ => ‖1 - q ^ (m + k + 1)‖) Filter.atTop (nhds 1) := by
                  exact le_trans ( Filter.Tendsto.norm ( tendsto_const_nhds.sub ( tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat _ |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat _ ) ) ) ( by norm_num )
                have := h_lim.eventually ( lt_mem_nhds <| show 1 > 1 / 2 by norm_num )
                obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp this
                use min (1 / 2) (Finset.min' (Finset.image (fun m => ‖1 - q ^ (m + k + 1)‖) (Finset.range (N + 1))) (by
                exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ⟩))
                generalize_proofs at *
                simp +zetaDelta at *
                exact ⟨ fun m hm => sub_ne_zero_of_ne <| ne_of_apply_ne Norm.norm <| by norm_num; exact ne_of_gt <| pow_lt_one₀ ( norm_nonneg q ) hq <| by omega, fun m => if hm : m ≤ N then Or.inr <| Finset.min'_le _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <| by omega else Or.inl <| le_of_lt <| hN m <| le_of_not_ge hm ⟩
              exact ⟨ 1 / h_summable.choose, one_div_pos.mpr h_summable.choose_spec.1, fun m => by simpa using inv_anti₀ h_summable.choose_spec.1 ( h_summable.choose_spec.2 m ) ⟩
            obtain ⟨ C, hC₀, hC ⟩ := h_summable
            have h_prod_summable : Summable (fun m : ℕ => ‖q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))‖ * C) := by
              exact Summable.mul_right _ ( h_summable.norm )
            have h_comparison : ∀ m : ℕ, ‖q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)) * (1 / (1 - q ^ (m + k + 1)))‖ ≤ ‖q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))‖ * C := by
              exact fun m => by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_left ( hC m ) ( norm_nonneg _ ) 
            have h_comparison_test : Summable (fun m : ℕ => ‖q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)) * (1 / (1 - q ^ (m + k + 1)))‖) := by
              exact Summable.of_nonneg_of_le ( fun m => norm_nonneg _ ) h_comparison h_prod_summable
            exact h_comparison_test.of_norm
          convert h_summable using 2 ; norm_num [ qPochhammer_succ ] ; ring
          grind
        convert h_summable.sub ( show Summable fun m : ℕ => q ^ ( m * ( m + k ) ) * q ^ m / ( qPochhammer q q m * qPochhammer q q ( m + k + 1 ) ) from ?_ ) using 2 ; ring
        have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) * q ^ m) := by
          exact Summable.of_norm <| by simpa using h_summable.norm.of_nonneg_of_le ( fun m => by positivity ) fun m => by simpa using mul_le_mul_of_nonneg_left ( pow_le_one₀ ( by positivity ) hq.le ) ( by positivity ) 
        exact h_summable.congr fun m => by ring
    convert congr_arg₂ ( · + · ) h_split ( show ∑' m : ℕ, - ( q ^ ( m * ( m + k ) ) * q ^ ( m + k + 1 ) ) / ( qPochhammer q q m * qPochhammer q q ( m + k + 1 ) ) = -q ^ ( k + 1 ) * S_sum q ( k + 1 ) from ?_ ) using 1
    · rw [ ← Summable.tsum_add ] ; congr ; ext m ; ring
      · have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k + 1))) := by
          have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))) := by
            convert summable_S_summand hq k using 1
          have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)) * (1 / (1 - q ^ (m + k + 1)))) := by
            refine .of_norm ?_
            have h_summable : ∃ C > 0, ∀ m : ℕ, ‖1 / (1 - q ^ (m + k + 1))‖ ≤ C := by
              have h_summable : ∃ C > 0, ∀ m : ℕ, ‖1 - q ^ (m + k + 1)‖ ≥ C := by
                have h_lim : Filter.Tendsto (fun m : ℕ => ‖1 - q ^ (m + k + 1)‖) Filter.atTop (nhds 1) := by
                  exact le_trans ( Filter.Tendsto.norm ( tendsto_const_nhds.sub ( tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat _ |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat _ ) ) ) ( by norm_num )
                have := h_lim.eventually ( lt_mem_nhds <| show 1 > 1 / 2 by norm_num )
                obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp this
                use min (1 / 2) (Finset.min' (Finset.image (fun m => ‖1 - q ^ (m + k + 1)‖) (Finset.range (N + 1))) (by
                exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ⟩))
                generalize_proofs at *
                simp +zetaDelta at *
                exact ⟨ fun m hm => sub_ne_zero_of_ne <| ne_of_apply_ne Norm.norm <| by norm_num; exact ne_of_gt <| pow_lt_one₀ ( norm_nonneg q ) hq <| by omega, fun m => if hm : m ≤ N then Or.inr <| Finset.min'_le _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <| by omega else Or.inl <| le_of_lt <| hN m <| le_of_not_ge hm ⟩
              exact ⟨ 1 / h_summable.choose, one_div_pos.mpr h_summable.choose_spec.1, fun m => by simpa using inv_anti₀ h_summable.choose_spec.1 ( h_summable.choose_spec.2 m ) ⟩
            obtain ⟨ C, hC₀, hC ⟩ := h_summable
            exact Summable.of_nonneg_of_le ( fun m => norm_nonneg _ ) ( fun m => by simpa [ abs_mul, abs_div ] using mul_le_mul_of_nonneg_left ( hC m ) ( by positivity ) ) ( h_summable.norm.mul_right C )
          convert h_summable using 2 ; norm_num [ qPochhammer_succ ] ; ring
          grind
        convert h_summable.sub ( show Summable fun m : ℕ => q ^ ( m * ( m + k ) ) * q ^ m / ( qPochhammer q q m * qPochhammer q q ( m + k + 1 ) ) from ?_ ) using 2 ; ring
        have h_summable : Summable (fun m : ℕ => q ^ m * (q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k + 1)))) := by
          exact Summable.of_norm <| by simpa using Summable.of_nonneg_of_le ( fun m => by positivity ) ( fun m => mul_le_of_le_one_left ( by positivity ) <| pow_le_one₀ ( by positivity ) hq.le ) <| h_summable.norm
        grind +locals
      · have h_summable : Summable (fun m : ℕ => q ^ (m * (m + k + 1)) / (qPochhammer q q m * qPochhammer q q (m + k + 1))) := by
          have := summable_S_summand hq (k + 1)
          convert this using 1
        convert h_summable.mul_left ( -q ^ ( k + 1 ) ) using 2 ; ring
    · unfold S_sum; ring
      norm_num [ mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left ] ; ring
    · unfold S_sum; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left ] 
      exact tsum_congr fun n => by ring
  rw [ ← h_split, S_sum, S_sum, ← Summable.tsum_sub ]
  · refine tsum_congr fun m => ?_
    rw [ div_sub_div, div_eq_div_iff ]
    · rw [ show m + ( k + 1 ) = m + k + 1 by ring, qPochhammer_succ ] ; ring
    · simp_all +decide [ qPochhammer_q_q_ne_zero ]
    · exact mul_ne_zero ( qPochhammer_q_q_ne_zero hq m ) ( qPochhammer_q_q_ne_zero hq ( m + k + 1 ) )
    · exact mul_ne_zero ( qPochhammer_q_q_ne_zero hq m ) ( qPochhammer_q_q_ne_zero hq ( m + k ) )
    · exact mul_ne_zero ( qPochhammer_q_q_ne_zero hq _ ) ( qPochhammer_q_q_ne_zero hq _ )
  · convert summable_S_summand hq k using 1
  · convert summable_S_summand hq ( k + 1 ) using 1

/-- All $S_k(q)$ are equal to $1/(q;q)_\infty$ for $\|q\| < 1$. -/
theorem S_sum_eq {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    S_sum q k = 1 / qPochhammerInf q q := by
  have h_ind : ∀ k : ℕ, S_sum q k - S_sum q (k + 1) = 0 := by
    intro k
    have h_induction : ∀ n : ℕ, ‖S_sum q k - S_sum q (k + 1)‖ ≤ ‖q‖ ^ (n * (2 * k + n + 1) / 2) * ‖S_sum q (k + n) - S_sum q (k + n + 1)‖ := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
          have h_induction_step : ‖S_sum q (k + n) - S_sum q (k + n + 1)‖ ≤ ‖q‖ ^ (k + n + 1) * ‖S_sum q (k + n + 1) - S_sum q (k + n + 2)‖ := by
            have := S_sum_recurrence hq ( k + n )
            rw [ this, norm_mul, norm_pow, norm_sub_rev ]
          convert le_trans ih ( mul_le_mul_of_nonneg_left h_induction_step <| by positivity ) using 1 ; ring
          rw [ show ( 2 + n * 3 + n * k * 2 + n ^ 2 + k * 2 ) / 2 = n + k + ( n + n * k * 2 + n ^ 2 ) / 2 + 1 by exact Nat.div_eq_of_eq_mul_left zero_lt_two <| by linarith [ Nat.div_mul_cancel ( show 2 ∣ n + n * k * 2 + n ^ 2 from even_iff_two_dvd.mp <| by simp +arith +decide [ parity_simps ] ) ] ] ; ring
    have h_diff_zero : Filter.Tendsto (fun n => S_sum q (k + n) - S_sum q (k + n + 1)) Filter.atTop (nhds 0) := by
      convert Filter.Tendsto.sub ( S_sum_tendsto hq |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => Nat.le_add_left _ _ ) Filter.tendsto_id ) ( S_sum_tendsto hq |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => Nat.le_succ_of_le <| Nat.le_add_left _ _ ) Filter.tendsto_id ) using 2 ; norm_num
    have h_exp_zero : Filter.Tendsto (fun n => ‖q‖ ^ (n * (2 * k + n + 1) / 2)) Filter.atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg q ) hq |> Filter.Tendsto.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 2 * x + 1, fun n hn => Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by nlinarith ⟩
    exact norm_le_zero_iff.mp ( le_of_tendsto_of_tendsto' tendsto_const_nhds ( by simpa using h_exp_zero.mul ( h_diff_zero.norm ) ) h_induction )
  have h_const : ∀ k : ℕ, S_sum q k = S_sum q 0 := by
    exact fun n => Nat.recOn n rfl fun n ih => by linear_combination' ih - h_ind n
  convert tendsto_nhds_unique ( tendsto_const_nhds.congr ( by aesop ) ) ( S_sum_tendsto hq ) using 1
  exact h_const k

private lemma choose2_step (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- Key arithmetic: C(m+k,2) + C(m,2) + m = C(k,2) + m*(m+k). -/
lemma choose2_add (m k : ℕ) :
    (m + k).choose 2 + m.choose 2 + m = k.choose 2 + m * (m + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 from by omega, choose2_step, choose2_step]
    nlinarith [ih]

/-- Variant: C(n,2) + C(n+l+1,2) + n+l+1 = C(l+2,2) + n*(n+l+1). -/
lemma choose2_add' (n l : ℕ) :
    n.choose 2 + (n + (l + 1)).choose 2 + (n + (l + 1)) = (l + 2).choose 2 + n * (n + (l + 1)) := by
  induction n with
  | zero =>
    simp only [zero_add, Nat.zero_mul, add_zero, Nat.choose_zero_succ]
    have : (l + 2).choose 2 = (l + 1).choose 2 + (l + 1) := by
      rw [show l + 2 = (l + 1) + 1 from by omega]; exact choose2_step (l+1)
    omega
  | succ n ih =>
    rw [choose2_step, show n + 1 + (l + 1) = (n + (l + 1)) + 1 from by omega, choose2_step]
    nlinarith [ih]

/-- Telescoping: (q;q)_∞ = (q;q)_n * (q^{n+1};q)_∞. -/
private lemma qPochhammerInf_eq_mul' {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf q q = qPochhammer q q n * qPochhammerInf (q * q ^ n) q := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [ih, qPochhammer_succ, mul_assoc]
    congr 1
    rw [qPochhammerInf_recursion hq]
    ring

/-- qPochhammerInf (q * q^n) q = (q;q)_∞ / (q;q)_n -/
lemma qPochhammerInf_shift_div {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf (q * q ^ n) q = qPochhammerInf q q / qPochhammer q q n := by
  rw [eq_div_iff (qPochhammer_q_q_ne_zero hq n), mul_comm]
  exact (qPochhammerInf_eq_mul' hq n).symm

/-- The sum over $m$ of the $z^k$ cross-terms in the JTP double product has sum $q^{\binom{k}{2}}$. -/
theorem cauchy_coeff_nonneg {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun m : ℕ =>
      q ^ (m + k).choose 2 * qPochhammerInf (q * q ^ (m + k)) q *
      (q ^ m.choose 2 * q ^ m / qPochhammer q q m))
      (q ^ k.choose 2) := by
  have h_sum : HasSum (fun m => q ^ ((m + k).choose 2 + m.choose 2 + m) * qPochhammerInf q q / (qPochhammer q q (m + k) * qPochhammer q q m)) (q ^ k.choose 2) := by
    have h_sum : HasSum (fun m => q ^ (k.choose 2 + m * (m + k)) * qPochhammerInf q q / (qPochhammer q q (m + k) * qPochhammer q q m)) (q ^ k.choose 2) := by
      have h_sum : HasSum (fun m => q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))) (1 / qPochhammerInf q q) := by
        convert S_sum_eq hq k using 1
        exact ⟨ fun h => h.tsum_eq, fun h => h ▸ Summable.hasSum ( summable_S_summand hq k ) ⟩
      convert h_sum.mul_left ( q ^ k.choose 2 * qPochhammerInf q q ) using 1 <;> ring
      · ac_rfl
      · rw [ mul_assoc, mul_inv_cancel₀ ( qPochhammerInf_z_q_ne_zero hq hq ), mul_one ]
    convert h_sum using 3 ; rw [ choose2_add ]
  convert h_sum using 2 ; push_cast [ qPochhammerInf_shift_div hq ] ; ring

/-- The sum over $n$ of the $z^{-(l+1)}$ cross-terms in the JTP double product has sum $q^{\binom{l+2}{2}}$. -/
theorem cauchy_coeff_neg {q : ℂ} (hq : ‖q‖ < 1) (l : ℕ) :
    HasSum (fun n : ℕ =>
      q ^ n.choose 2 * qPochhammerInf (q * q ^ n) q *
      (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1))))
      (q ^ (l + 2).choose 2) := by
  have h_simp : HasSum (fun n : ℕ => q ^ (n.choose 2 + (n + (l + 1)).choose 2 + (n + (l + 1))) * qPochhammerInf q q / (qPochhammer q q n * qPochhammer q q (n + (l + 1)))) (q ^ (l + 2).choose 2) := by
    convert HasSum.mul_left ( q ^ ( l + 2 ).choose 2 * qPochhammerInf q q ) ( summable_S_summand hq ( l + 1 ) |> Summable.hasSum ) using 1
    · ext; rw [ S_summand ] ; rw [ choose2_add' ] ; ring
    · rw [ show ( ∑' n : ℕ, S_summand q ( l + 1 ) n ) = 1 / qPochhammerInf q q from ?_ ]
      · rw [ mul_assoc, mul_one_div_cancel ( qPochhammerInf_z_q_ne_zero hq hq ), mul_one ]
      · convert S_sum_eq hq ( l + 1 ) using 1
  convert h_simp using 2 ; rw [ qPochhammerInf_shift_div hq ] ; ring

end

end qSeries