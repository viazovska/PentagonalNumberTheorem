/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import Mathlib
import EulerPentagonalNumberTheorem_Franklin.Defs
import EulerPentagonalNumberTheorem_Franklin.Helpers
open Finset
/-!
# Pentagonal Number Theorem — Lemmas

This file contains the key lemmas for the Pentagonal Number Theorem,
following Franklin's involution argument.

## Main results

* `distinct_parts_disjoint_union`: the partition classes α/β/special are disjoint with union
* `special_partition_char`: characterization of special partitions
* `franklin_involution_bijection`: Franklin's involution is a bijection
* `parity_flip`: Franklin's involution flips even/odd parity
* `signed_partition_main`: pe(n) - po(n) = (-1)^k for pentagonal n, 0 otherwise
-/
/-- **Example 6 (Source, table)**: `pe(5) = 2`.
The two even-size distinct partitions of 5 are `{4,1}` and `{3,2}`. -/
theorem pe_5 : pe 5 = 2 := by native_decide
/-- **Example 6 (Source, table)**: `po(5) = 1`.
The one odd-size distinct partition of 5 is `{5}`. -/
theorem po_5 : po 5 = 1 := by native_decide
/-- **Example 6 (Source, table)**: `pe(7) = 3`, `po(7) = 2`. -/
theorem pe_7 : pe 7 = 3 := by native_decide
theorem po_7 : po 7 = 2 := by native_decide
/-- α-partitions and β-partitions are disjoint. -/
theorem DPalpha_inter_DPbeta (n : ℕ) :
    distinctPartitionsAlpha n ∩ distinctPartitionsBeta n = ∅ := by
  ext S
  simp [distinctPartitionsAlpha, distinctPartitionsBeta]
  grind
/-- α-partitions and special partitions are disjoint. -/
theorem DPalpha_inter_DPspecial (n : ℕ) :
    distinctPartitionsAlpha n ∩ distinctPartitionsSpecial n = ∅ := by
  unfold distinctPartitionsAlpha distinctPartitionsSpecial
  grind
/-- β-partitions and special partitions are disjoint. -/
theorem DPbeta_inter_DPspecial (n : ℕ) :
    distinctPartitionsBeta n ∩ distinctPartitionsSpecial n = ∅ := by
  simp [distinctPartitionsBeta, distinctPartitionsSpecial]
  grind
/-- Every distinct partition is in exactly one of α, β, or special. -/
theorem DP_eq_union (n : ℕ) :
    distinctPartitions n =
    distinctPartitionsAlpha n ∪ distinctPartitionsBeta n ∪ distinctPartitionsSpecial n := by
  apply Finset.ext
  intro S
  simp [distinctPartitionsAlpha, distinctPartitionsBeta, distinctPartitionsSpecial]
  grind
/-- The set smkSet(k) has exactly k elements. -/
theorem SmkSet_card (k : ℕ) (hk : 1 ≤ k) : (smkSet k).card = k := by
  unfold smkSet; rw [ Nat.card_Icc ] ; omega
/-- The sum of smkSet(k) equals (3k²-k)/2. -/
theorem SmkSet_sum (k : ℕ) (hk : 1 ≤ k) : (smkSet k).sum id = (3 * k ^ 2 - k) / 2 := by
  erw [ Finset.sum_Ico_eq_sum_range ]
  rw [ Nat.sub_add_cancel ( by omega ), two_mul ]
  simp +arith +decide [ Finset.sum_add_distrib ]
  rw [ two_mul, add_tsub_cancel_left, Finset.sum_add_distrib ]
  exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( Nat.sub_eq_of_eq_add ( by norm_num; exact Nat.recOn k ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith ) ) )
/-- The set spkSet(k) has exactly k elements. -/
theorem SpkSet_card (k : ℕ) (hk : 1 ≤ k) : (spkSet k).card = k := by
  simp [spkSet]
  rw [ two_mul, Nat.add_sub_cancel ]
/-- The sum of spkSet(k) equals (3k²+k)/2. -/
theorem SpkSet_sum (k : ℕ) (hk : 1 ≤ k) : (spkSet k).sum id = (3 * k ^ 2 + k) / 2 := by
  erw [ Finset.sum_Ico_eq_sum_range ]
  norm_num [ two_mul, add_assoc, Finset.sum_add_distrib ]
  exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( Nat.recOn k ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith ) )
/-- For non-pentagonal n ≥ 1, there are no special partitions. -/
theorem DPspecial_empty_of_nonpent (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 - k)
    (h2 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 + k) :
    distinctPartitionsSpecial n = ∅ := by
      by_contra h_nonempty
      obtain ⟨S, hS⟩ : ∃ S ∈ distinctPartitionsSpecial n, S ≠ ∅ := by
        obtain ⟨ S, hS ⟩ := Finset.nonempty_of_ne_empty h_nonempty; use S; simp_all +decide [ distinctPartitionsSpecial ] 
        rintro rfl; simp_all +decide [ distinctPartitions ] 
        grind +splitImp
      obtain ⟨b, m, s, hb, hm, hs, hD⟩ : ∃ b m s, partBase S = b ∧ partMax S = m ∧ partSlope S = s ∧ partMax S - partSlope S + 1 ≤ partBase S ∧ (partBase S = partSlope S ∨ partBase S = partSlope S + 1) := by
        unfold distinctPartitionsSpecial at hS; aesop
      have hS_eq : S = Finset.Icc b m := by
        refine Finset.Subset.antisymm ?_ ?_
        · intro x hx; have := Finset.mem_Icc.mpr ⟨ hb ▸ partBase_le S ( Finset.nonempty_of_ne_empty hS.2 ) hx, hm ▸ le_partMax S ( Finset.nonempty_of_ne_empty hS.2 ) hx ⟩ ; aesop
        · intro x hx; have := Finset.mem_Icc.mp hx; simp_all +decide [ partBase, partMax ] 
          have h_consecutive : ∀ j, j < s → m - j ∈ S := by
            exact fun j hj => ctr_mem_of_lt _ _ _ ( by aesop )
          convert h_consecutive ( m - x ) _ using 1
          · rw [ Nat.sub_sub_self ( by omega ) ]
          · omega
      have hm_eq : m = b + s - 1 := by
        have hm_eq : consecutiveTopRun S m = m - b + 1 := by
          have h_consecutiveTopRun : ∀ {k : ℕ}, k ≤ m → consecutiveTopRun (Finset.Icc b m) k = if k < b then 0 else k - b + 1 := by
            intro k hk; induction k <;> simp_all +decide [ Nat.succ_eq_add_one, consecutiveTopRun ]
            · grind
            · grind
          grind
        unfold partSlope at hs; simp_all +decide 
      have hn_eq : n = (b + m) * s / 2 := by
        have hn_eq : n = Finset.sum (Finset.Icc b m) id := by
          have hn_eq : n = S.sum id := by
            exact Eq.symm ( Finset.mem_filter.mp ( Finset.mem_filter.mp hS.1 |>.1 ) |>.2 )
          rw [hn_eq, hS_eq]
        rw [ hn_eq, hm_eq ]
        erw [ Finset.sum_Ico_eq_sum_range ]
        rcases s with ( _ | s ) <;> simp +arith +decide [ Nat.mul_succ, Finset.sum_add_distrib ] at *
        · omega
        · exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( Nat.recOn s ( by norm_num [ add_assoc, Finset.sum_range_succ ] ; ring ) fun n ihn => by norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith ) )
      rcases s with ( _ | _ | s ) <;> simp_all +decide
      · simp_all +decide [ ← two_mul, Nat.mul_div_cancel_left ]
        exact h1 1 le_rfl ( by norm_num; linarith [ show b = 1 from by { unfold distinctPartitionsSpecial at hS; aesop } ] )
      · rcases hD.2 with ( rfl | rfl ) <;> ring_nf at *
        · exact h1 ( s + 2 ) ( by omega ) ( by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.div_mul_cancel ( show 2 ∣ 10 + s * 11 + s ^ 2 * 3 from even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ) ] )
        · exact h2 ( s + 2 ) ( by omega ) ( by linarith [ Nat.div_mul_cancel ( show 2 ∣ 14 + s * 13 + s ^ 2 * 3 from even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ) ] )
/-- For n = (3k²-k)/2 (pentagonal minus), the only special partition is smkSet(k). -/
theorem DPspecial_pent_minus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 - k) :
    distinctPartitionsSpecial n = {smkSet k} := by
      unfold distinctPartitionsSpecial
      ext S
      constructor
      · simp +zetaDelta at *
        intro hS h
        obtain ⟨hS_empty, hS_nonempty⟩ := h
        · simp_all +decide [ distinctPartitions ]
          rw [ eq_tsub_iff_add_eq_of_le ] at hn <;> nlinarith
        · have hS_eq_SmkSet : S = Finset.Icc (partBase S) (partMax S) := by
            refine Finset.Subset.antisymm ?_ ?_
            · exact fun x hx => Finset.mem_Icc.mpr ⟨ partBase_le _ ( by tauto ) hx, le_partMax _ ( by tauto ) hx ⟩
            · intros m hm
              have h_consecutive : ∀ j, j < partSlope S → partMax S - j ∈ S := by
                apply ctr_mem_of_lt
              convert h_consecutive ( partMax S - m ) _ using 1
              · rw [ Nat.sub_sub_self ( Finset.mem_Icc.mp hm |>.2 ) ]
              · grind
          have hS_sum : S.sum id = (3 * partBase S ^ 2 - partBase S) / 2 ∨ S.sum id = (3 * (partBase S - 1) ^ 2 + (partBase S - 1)) / 2 := by
            have hS_sum : S.sum id = (partMax S - partBase S + 1) * (partBase S + partMax S) / 2 := by
              have h_sum_formula : ∀ a b : ℕ, a ≤ b → (Finset.Icc a b).sum id = (b - a + 1) * (a + b) / 2 := by
                intros a b hab
                have h_sum_formula : (Finset.Icc a b).sum id = ∑ i ∈ Finset.range (b - a + 1), (a + i) := by
                  erw [ Finset.sum_Ico_eq_sum_range ]
                  rw [ Nat.sub_add_comm hab ]
                  rfl
                rw [ h_sum_formula, Finset.sum_add_distrib ]
                norm_num [ Finset.sum_range_id ]
                exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( by nlinarith only [ Nat.sub_add_cancel hab, Nat.div_mul_cancel ( show 2 ∣ ( b - a + 1 ) * ( b - a ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ] ) )
              grind
            have hS_max : partMax S = 2 * partBase S - 1 ∨ partMax S = 2 * partBase S - 2 := by
              have hS_max : partSlope S = partMax S - partBase S + 1 := by
                have hS_slope : ∀ m ∈ S, consecutiveTopRun S m = m - partBase S + 1 := by
                  intro m hm
                  revert hm
                  induction m with
                  | zero => intro hm; exact absurd ( DP_zero_not_mem n S hS ) ( by simp +decide [ hm ] )
                  | succ m ih => intro hm; grind +suggestions
                exact hS_slope _ ( partMax_mem _ ( by tauto ) )
              grind
            rcases hS_max with h | h <;> rw [ hS_sum, h ] <;> rcases partBase S with ( _ | _ | partBase ) <;> simp +arith +decide [ Nat.mul_succ ] at *
            · grind
            · exact Or.inr ( by rw [ show 2 * partBase - partBase = partBase by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring )
          have hS_sum_eq_n : S.sum id = n := by
            exact DP_sum n S hS
          rcases hS_sum with h | h <;> rw [ h ] at hS_sum_eq_n
          · have h_eq : 3 * partBase S ^ 2 - partBase S = 3 * k ^ 2 - k := by
              linarith [ Nat.div_mul_cancel ( show 2 ∣ 3 * partBase S ^ 2 - partBase S from even_iff_two_dvd.mp ( by rw [ Nat.even_sub ( by nlinarith only [ hk ] ) ] ; simp +arith +decide [ parity_simps ] ) ) ]
            have h_partBase_eq_k : partBase S = k := by
              rw [ Nat.sub_eq_iff_eq_add ] at h_eq
              · nlinarith only [ h_eq, Nat.sub_add_cancel ( show k ≤ 3 * k ^ 2 from by nlinarith only [ hk ] ), hk ]
              · nlinarith only [ hk ]
            have h_partMax_eq_2k_minus_1 : partMax S = 2 * k - 1 := by
              have h_partMax_eq_2k_minus_1 : S.sum id = (partMax S + partBase S) * (partMax S - partBase S + 1) / 2 := by
                have h_sum_formula : ∀ a b : ℕ, a ≤ b → (Finset.Icc a b).sum id = (b + a) * (b - a + 1) / 2 := by
                  intros a b hab
                  have h_sum_formula : (Finset.Icc a b).sum id = ∑ i ∈ Finset.range (b - a + 1), (a + i) := by
                    erw [ Finset.sum_Ico_eq_sum_range ]
                    rw [ Nat.sub_add_comm hab ]
                    rfl
                  rw [ h_sum_formula, Finset.sum_add_distrib ]
                  norm_num [ Finset.sum_range_id ]
                  exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( by nlinarith only [ Nat.sub_add_cancel hab, Nat.div_mul_cancel ( show 2 ∣ ( b - a + 1 ) * ( b - a ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ] ) )
                grind +extAll
              rw [ eq_comm, Nat.div_eq_iff_eq_mul_left zero_lt_two ] at h_partMax_eq_2k_minus_1
              · rw [ h ] at h_partMax_eq_2k_minus_1
                rw [ Nat.div_mul_cancel ] at h_partMax_eq_2k_minus_1
                · rw [ eq_tsub_iff_add_eq_of_le ] at h_partMax_eq_2k_minus_1
                  · rw [ h_partBase_eq_k ] at h_partMax_eq_2k_minus_1
                    exact eq_tsub_of_add_eq ( by nlinarith only [ Nat.sub_add_cancel ( show k ≤ partMax S from by linarith [ partBase_le_partMax S ( by tauto ) ] ), h_partMax_eq_2k_minus_1, hk ] )
                  · nlinarith only [ hk, h_partBase_eq_k ]
                · grind
              · norm_num [ ← even_iff_two_dvd, mul_add, parity_simps ]
                grind
            exact hS_eq_SmkSet.trans ( by rw [ h_partBase_eq_k, h_partMax_eq_2k_minus_1 ] ; rfl )
          · have hk_eq_partBase_minus_1 : k = partBase S - 1 := by
              rw [ Nat.div_eq_iff_eq_mul_left zero_lt_two ] at hS_sum_eq_n
              · rw [ eq_tsub_iff_add_eq_of_le ] at hn
                · nlinarith only [ hn, hS_sum_eq_n, Nat.sub_add_cancel ( show 1 ≤ partBase S from by omega ) ]
                · nlinarith only [ hk ]
              · norm_num [ ← even_iff_two_dvd, parity_simps ]
            grind
      · simp +zetaDelta at *
        rintro rfl
        constructor
        · rw [ mem_DP ]
          constructor
          · exact Finset.Icc_subset_Icc ( by omega ) ( Nat.sub_le_of_le_add <| by nlinarith [ Nat.sub_add_cancel ( by nlinarith : k ≤ 3 * k ^ 2 ) ] )
          · convert SmkSet_sum k hk using 1
            rw [ ← hn, Nat.mul_div_cancel_left _ ( by decide ) ]
        · have h_base : partBase (smkSet k) = k := by
            unfold partBase smkSet
            split_ifs <;> simp_all +decide [ Finset.min' ]
            · exact le_antisymm ( Finset.inf'_le _ <| Finset.left_mem_Icc.mpr <| Nat.le_sub_one_of_lt <| by omega ) ( Finset.le_inf' _ _ fun x hx => Finset.mem_Icc.mp hx |>.1 )
            · omega
          have h_max : partMax (smkSet k) = 2 * k - 1 := by
            unfold partMax; simp +decide [ smkSet ] 
            split_ifs <;> simp_all +decide [ Finset.max' ]
            · exact le_antisymm ( Finset.sup'_le _ _ fun x hx => Finset.mem_Icc.mp hx |>.2 ) ( Finset.le_sup' ( fun x => x ) ( Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ) )
            · omega
          have h_slope : partSlope (smkSet k) = k := by
            have h_consecutiveTopRun : ∀ m ∈ smkSet k, consecutiveTopRun (smkSet k) m = m - k + 1 := by
              intro m hm; induction m <;> simp_all +decide [ smkSet ]
              grind +suggestions
            convert h_consecutiveTopRun ( 2 * k - 1 ) _ using 1
            · exact h_max ▸ rfl
            · omega
            · exact Finset.mem_Icc.mpr ⟨ Nat.le_sub_one_of_lt ( by omega ), Nat.sub_le_sub_right ( by omega ) _ ⟩
          grind +qlia
/-- For n = (3k²+k)/2 (pentagonal plus), the only special partition is spkSet(k). -/
theorem DPspecial_pent_plus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 + k) :
    distinctPartitionsSpecial n = {spkSet k} := by
      have hSpkSet_in_DPspecial : spkSet k ∈ distinctPartitionsSpecial n := by
        refine Finset.mem_filter.mpr ⟨ ?_, ?_ ⟩
        · refine Finset.mem_filter.mpr ⟨ ?_, ?_ ⟩
          · exact Finset.mem_powerset.mpr ( Finset.Icc_subset_Icc ( by omega ) ( by nlinarith ) )
          · convert SpkSet_sum k hk using 1
            rw [ ← hn, Nat.mul_div_cancel_left _ ( by decide ) ]
        · have h_base : partBase (spkSet k) = k + 1 := by
            unfold partBase spkSet
            simp +decide [ Finset.min', hk ]
            split_ifs <;> simp_all +decide [ two_mul, Finset.inf'_eq_csInf_image ]
          have h_max : partMax (spkSet k) = 2 * k := by
            unfold partMax spkSet
            split_ifs <;> simp_all +decide [ Finset.max' ]
            · exact le_antisymm ( Finset.sup'_le _ _ fun x hx => by linarith [ Finset.mem_Icc.mp hx ] ) ( Finset.le_sup' ( fun x => x ) ( Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ) )
            · omega
          have h_slope : partSlope (spkSet k) = k := by
            have h_consecutiveTopRun : ∀ m ∈ Finset.Icc (k + 1) (2 * k), consecutiveTopRun (spkSet k) m = m - k := by
              intro m hm; induction m <;> simp_all +decide [ Nat.mul_succ, Finset.mem_Icc ] 
              split_ifs <;> simp_all +decide [ spkSet ]
              grind +suggestions
            convert h_consecutiveTopRun ( 2 * k ) ( Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ) using 1
            · exact h_max ▸ rfl
            · rw [ two_mul, Nat.add_sub_cancel ]
          grind
      ext S
      simp_all +decide [ distinctPartitionsSpecial ]
      constructor
      · rintro ⟨ hS₁, hS₂ | hS₂ ⟩
        · simp_all +decide [ distinctPartitions ]
        · obtain ⟨hS_subset, hS_sum⟩ := (mem_DP n S).mp hS₁
          have hS_eq_SpkSet : S = Finset.Icc (partMax S - partSlope S + 1) (partMax S) := by
            have hS_eq_SpkSet : ∀ x ∈ S, partMax S - partSlope S + 1 ≤ x ∧ x ≤ partMax S := by
              intros x hx
              have hx_le_partMax : x ≤ partMax S := by
                exact Finset.le_max' _ _ hx |> le_trans <| by unfold partMax; aesop
              have hx_ge_partMax_minus_partSlope_plus_1 : partMax S - partSlope S + 1 ≤ x := by
                exact lt_of_lt_of_le hS₂.2.1 ( partBase_le S hS₂.1 hx )
              exact ⟨hx_ge_partMax_minus_partSlope_plus_1, hx_le_partMax⟩
            refine Finset.eq_of_subset_of_card_le ( fun x hx => Finset.mem_Icc.mpr ( hS_eq_SpkSet x hx ) ) ?_
            have hS_card : S.card ≥ partSlope S := by
              have hS_card : Finset.card (Finset.image (fun j => partMax S - j) (Finset.range (partSlope S))) ≤ Finset.card S := by
                refine Finset.card_le_card ?_
                intro x hx
                obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp hx
                convert ctr_mem_of_lt S ( partMax S ) j ( Finset.mem_range.mp hj ) using 1
              rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ Finset.mem_range.mp hx, Finset.mem_range.mp hy, Nat.sub_le ( partMax S ) ( partSlope S ), show partSlope S ≤ partMax S from partSlope_le_partMax S ( DP_zero_not_mem n S hS₁ ) ], Finset.card_range ] at hS_card
            simp +zetaDelta at *
            omega
          have hS_eq_SpkSet_interval : partMax S = 2 * k ∧ partSlope S = k := by
            have hS_eq_SpkSet_interval : (partMax S - partSlope S + 1 + partMax S) * partSlope S / 2 = n := by
              have hS_eq_SpkSet_interval : S.sum id = (partMax S - partSlope S + 1 + partMax S) * partSlope S / 2 := by
                conv_lhs => rw [ hS_eq_SpkSet ]
                have h_sum_formula : ∀ a b : ℕ, a ≤ b → (Finset.Icc a b).sum id = (a + b) * (b - a + 1) / 2 := by
                  intros a b hab
                  have h_sum_formula : (Finset.Icc a b).sum id = ∑ i ∈ Finset.range (b - a + 1), (a + i) := by
                    erw [ Finset.sum_Ico_eq_sum_range ]
                    rw [ Nat.sub_add_comm hab ]
                    rfl
                  rw [ h_sum_formula, Finset.sum_add_distrib ]
                  norm_num [ Finset.sum_range_id ]
                  exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( by nlinarith only [ Nat.sub_add_cancel hab, Nat.div_mul_cancel ( show 2 ∣ ( b - a + 1 ) * ( b - a ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ] ) )
                convert h_sum_formula _ _ _ using 2
                · rw [ tsub_add_eq_tsub_tsub, tsub_tsub_cancel_of_le ]
                  · grind
                  · apply partSlope_le_partMax
                    exact fun h => by have := hS_subset h; norm_num at this
                · grind
              exact hS_eq_SpkSet_interval ▸ hS_sum
            have hS_eq_SpkSet_interval : partMax S = 2 * partSlope S := by
              have hS_eq_SpkSet_interval : partBase S = partMax S - partSlope S + 1 := by
                unfold partBase partMax partSlope at *
                grind +suggestions
              cases hS₂.2.2 <;> simp +decide [ ‹_› ] at *
              · have h_contra : partMax S = 2 * partSlope S - 1 := by
                  grind
                rw [ h_contra ] at ‹ ( partMax S - partSlope S + 1 + partMax S ) * partSlope S / 2 = n ›
                rw [ show 2 * partSlope S - 1 - partSlope S = partSlope S - 1 by omega ] at *
                rcases x : partSlope S with ( _ | _ | k ) <;> simp +decide [ x ] at *
                · grind +revert
                · norm_num [ Nat.mul_succ ] at *
                  rename_i h₁ h₂
                  rename_i m
                  rw [ Nat.div_eq_iff_eq_mul_left zero_lt_two ] at h₂
                  · nlinarith only [ hn, h₂, show m = k + 2 by nlinarith only [ hn, h₂ ] ]
                  · norm_num [ ← even_iff_two_dvd, parity_simps ]
                    exact Nat.even_or_odd k
              · omega
            norm_num [ hS_eq_SpkSet_interval ] at *
            norm_num [ two_mul ] at *
            rw [ Nat.div_eq_iff_eq_mul_left zero_lt_two ] at hS_eq_SpkSet_interval
            · have hS_eq_SpkSet_interval : partSlope S = k := by
                nlinarith only [ hn, hS_eq_SpkSet_interval, hk ]
              rw [ hS_eq_SpkSet ] at *
              norm_num [ partMax ] at *
              split_ifs <;> simp_all +decide [ Finset.max' ]
              · exact le_antisymm ( Finset.sup'_le _ _ fun x hx => by linarith [ Finset.mem_Icc.mp hx ] ) ( Finset.le_sup' ( fun x => x ) ( Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ) )
              · exact absurd hS_eq_SpkSet ( Ne.symm <| Finset.Nonempty.ne_empty ⟨ k + 1, Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ⟩ )
            · norm_num [ ← even_iff_two_dvd, mul_add, parity_simps ]
              exact Nat.even_or_odd _ |> Or.symm
          rw [ hS_eq_SpkSet, hS_eq_SpkSet_interval.1, hS_eq_SpkSet_interval.2 ]
          unfold spkSet; simp +decide [ two_mul ] 
      · aesop
/-- The Franklin α-operation maps α-partitions into β-partitions. -/
theorem alphaOp_mem_DPbeta (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    alphaOp S ∈ distinctPartitionsBeta n := by
      refine Finset.mem_filter.mpr ⟨ ?_, ?_ ⟩
      · have h_sum : (alphaOp S).sum id = n := by
          rw [ alphaOp_sum n S hS, DP_sum n S ( DPalpha_mem_DP n S hS ) ]
        refine Finset.mem_filter.mpr ⟨ ?_, ?_ ⟩
        · simp_all +decide [ Finset.subset_iff ]
          intro x hx; have := h_sum ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hx; simp_all +decide [ alphaOp ] 
          rcases hx with ( rfl | ⟨ hx₁, hx₂, hx₃ ⟩ ) <;> [ exact Nat.succ_pos _; exact DP_pos_mem n S ( DPalpha_mem_DP n S hS ) hx₃ ]
        · exact h_sum
      · have h_alphaOp_base : partBase (alphaOp S) ≥ partBase S + 1 := by
          unfold partBase alphaOp
          split_ifs <;> simp_all +decide [ Finset.min' ]
          exact ⟨ ⟨ partMax S, partMax_mem S ‹_›, le_rfl ⟩, fun a ha₁ ha₂ ha₃ => ⟨ partBase S, partBase_mem S ‹_›, lt_of_le_of_ne ( partBase_le S ‹_› ha₃ ) ( Ne.symm ha₂ ) ⟩ ⟩
        have h_alphaOp_slope : partSlope (alphaOp S) = partBase S :=
          alphaOp_partSlope n S hS
        have h_alphaOp_max : partMax (alphaOp S) = partMax S + 1 :=
          alphaOp_partMax n S hS
        have h_alphaOp_card : (alphaOp S).card > 0 := by
          unfold alphaOp; aesop
        have := DPalpha_max_ge_2base n S hS
        omega
/-- The Franklin β-operation maps β-partitions into α-partitions. -/
theorem betaOp_mem_DPalpha (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    betaOp S ∈ distinctPartitionsAlpha n := by
      have h_beta_op_in_DP : betaOp S ∈ distinctPartitions n := by
        have h_betaOp_subset : betaOp S ⊆ Finset.Icc 1 n := by
          unfold betaOp; simp +decide [ *, Finset.subset_iff ] 
          intro x hx hx'
          rcases hx' with ( rfl | rfl | hx' )
          · refine ⟨ ?_, ?_ ⟩
            · apply partSlope_pos
              · exact Finset.nonempty_of_ne_empty ( by rintro rfl; contradiction )
              · exact DP_zero_not_mem n S ( DPbeta_mem_DP n S hS )
            · refine le_trans ( partSlope_le_partMax _ ?_ ) ?_
              · exact DP_zero_not_mem n S ( DPbeta_mem_DP n S hS )
              · exact DP_le_mem n S ( DPbeta_mem_DP n S hS ) ( partMax_mem S ( DPbeta_nonempty n S hS ) )
          · have h_partMax_le_n : partMax S ≤ n := by
              have h_partMax_le_n : ∀ x ∈ S, x ≤ n := by
                exact fun x hx => DP_le_mem n S ( DPbeta_mem_DP n S hS ) hx
              unfold partMax; aesop
            exact ⟨ Nat.sub_pos_of_lt ( by linarith [ DPbeta_max_ge_2slope_add_1 n S hS ] ), Nat.sub_le_of_le_add <| by omega ⟩
          · exact ⟨ DP_pos_mem n S ( DPbeta_mem_DP n S hS ) hx', DP_le_mem n S ( DPbeta_mem_DP n S hS ) hx' ⟩
        exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_betaOp_subset, betaOp_sum n S hS ▸ DP_sum n S ( DPbeta_mem_DP n S hS ) ⟩
      have h_beta_op_card : 0 < (betaOp S).card := by
        unfold betaOp
        by_cases h : partSlope S = partMax S <;> simp_all +decide [ Finset.Nonempty ]
        · exact ⟨ 0, by linarith [ DPbeta_max_ge_2slope_add_1 n S hS, partSlope_pos S ( DPbeta_nonempty n S hS ) ( DP_zero_not_mem n S ( DPbeta_mem_DP n S hS ) ) ], Or.inl rfl ⟩
        · exact ⟨ partSlope S, h, Or.inl rfl ⟩
      have h_beta_op_base : partBase (betaOp S) = partSlope S := by
        grind +suggestions
      have h_beta_op_slope : partSlope (betaOp S) ≥ partSlope S := by
        have h_beta_op_slope : ∀ j < partSlope S, partMax (betaOp S) - j ∈ betaOp S := by
          intros j hj
          have h_beta_op_slope : partMax (betaOp S) - j ∈ S ∨ partMax (betaOp S) - j = partSlope S ∨ partMax (betaOp S) - j = partMax S - partSlope S := by
            rw [ show partMax ( betaOp S ) = partMax S - 1 from betaOp_partMax n S hS ]
            have h_beta_op_slope : ∀ j < partSlope S, partMax S - j ∈ S := by
              apply ctr_mem_of_lt
            grind
          have h_beta_op_slope : partMax (betaOp S) - j ≠ partMax S := by
            rw [ betaOp_partMax ]
            exact ne_of_lt ( Nat.lt_of_le_of_lt ( Nat.sub_le _ _ ) ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < partMax S from Nat.pos_of_ne_zero ( by
                                                                                                    have := DPbeta_nonempty n S hS; simp_all +decide [ partMax ] 
                                                                                                    exact ne_of_gt ( lt_of_lt_of_le ( DP_pos_mem n S ( DPbeta_mem_DP n S hS ) ( Finset.max'_mem _ this ) ) ( Nat.le_refl _ ) ) ) ) ) ) )
            exacts [ n, hS ]
          unfold betaOp at *; aesop
        contrapose! h_beta_op_slope
        use partSlope (betaOp S)
        exact ⟨ h_beta_op_slope, by
          apply ctr_not_mem_boundary
          · exact DP_zero_not_mem n _ h_beta_op_in_DP
          · exact partMax_mem _ ( Finset.card_pos.mp h_beta_op_card ) ⟩
      simp_all +decide [ distinctPartitionsAlpha ]
      have h_beta_op_slope_set : partMax (betaOp S) = partMax S - 1 :=
        betaOp_partMax n S hS
      have h_beta_op_slope_set : 2 * partSlope S + 1 ≤ partMax S :=
        DPbeta_max_ge_2slope_add_1 n S hS
      omega
/-- The β-operation is a left inverse of the α-operation. -/
theorem betaOp_alphaOp (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    betaOp (alphaOp S) = S := by
      unfold betaOp; simp +decide [ *, Finset.ext_iff ] 
      unfold alphaOp; simp +decide [ *, Finset.ext_iff ] 
      have h_partMax : partMax (insert (partMax S + 1) ((S.erase (partBase S)).erase (partMax S - partBase S + 1))) = partMax S + 1 := by
        convert alphaOp_partMax n S hS using 1
      have h_partSlope : partSlope (insert (partMax S + 1) ((S.erase (partBase S)).erase (partMax S - partBase S + 1))) = partBase S := by
        convert alphaOp_partSlope n S hS using 1
      have h_partBase : partBase S ≤ partMax S := by
        apply partBase_le_partMax; exact DPalpha_nonempty n S hS
      grind +suggestions
/-- The α-operation is a left inverse of the β-operation. -/
theorem alphaOp_betaOp (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    alphaOp (betaOp S) = S := by
      unfold betaOp; simp +decide [ *, Finset.ext_iff ] 
      have h_simplify : ¬partSlope S ∈ S ∧ ¬(partMax S - partSlope S) ∈ S ∧ partMax S ∈ S := by
        exact ⟨ DPbeta_slope_not_mem n S hS, DPbeta_m_sub_s_not_mem n S hS, partMax_mem S ( DPbeta_nonempty n S hS ) ⟩
      unfold alphaOp; simp +decide [ *, Finset.ext_iff ] 
      have h_max : partMax ((insert (partSlope S) (insert (partMax S - partSlope S) S)).erase (partMax S)) = partMax S - 1 := by
        convert betaOp_partMax n S hS using 1
      have h_base : partBase ((insert (partSlope S) (insert (partMax S - partSlope S) S)).erase (partMax S)) = partSlope S := by
        apply betaOp_partBase n S hS
      have h_erase : partMax S - 1 - partSlope S + 1 = partMax S - partSlope S := by
        rw [ tsub_right_comm, tsub_add_cancel_of_le ]
        exact Nat.sub_pos_of_lt ( by linarith [ DPbeta_max_ge_2slope_add_1 n S hS ] )
      grind
/-- Franklin's involution gives a bijection: |α(n)| = |β(n)|. -/
theorem DPalpha_card_eq_DPbeta_card (n : ℕ) :
    (distinctPartitionsAlpha n).card = (distinctPartitionsBeta n).card := by
  fapply Finset.card_bij
  use fun S hS => alphaOp S
  · exact fun a ha => alphaOp_mem_DPbeta n a ha
  · intro a₁ ha₁ a₂ ha₂ h; have := betaOp_alphaOp n a₁ ha₁; have := betaOp_alphaOp n a₂ ha₂; aesop
  · exact fun b hb => ⟨ betaOp b, betaOp_mem_DPalpha n b hb, alphaOp_betaOp n b hb ⟩
/-- The α-operation preserves the number of parts. -/
theorem alphaOp_card (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    (alphaOp S).card + 1 = S.card := by
      unfold alphaOp
      rw [ Finset.card_insert_of_notMem, Finset.card_erase_of_mem, Finset.card_erase_of_mem ]
      · rcases x : Finset.card S with ( _ | _ | k ) <;> simp_all +arith +decide
        · unfold distinctPartitionsAlpha at hS; aesop
        · obtain ⟨ k, hk ⟩ := Finset.card_eq_one.mp x
          simp_all +decide [ distinctPartitionsAlpha ]
          unfold partBase partSlope partMax at hS ; simp_all +decide
          rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ consecutiveTopRun ]
          unfold distinctPartitions at hS; aesop
      · exact partBase_mem S ( DPalpha_nonempty n S hS )
      · exact Finset.mem_erase_of_ne_of_mem (DPalpha_base_ne_m_sub_b_add_1 n S hS).symm ( DPalpha_m_sub_b_add_1_mem n S hS )
      · have := partMax_succ_not_mem S ( DPalpha_nonempty n S hS ) ; aesop
/-- The β-operation preserves the number of parts. -/
theorem betaOp_card (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    (betaOp S).card = S.card + 1 := by
      have h_slope_not_mem : partSlope S ∉ S :=
        DPbeta_slope_not_mem n S hS
      have h_m_sub_slope_not_mem : partMax S - partSlope S ∉ S :=
        DPbeta_m_sub_s_not_mem n S hS
      have h_slope_ne_m_sub_slope : partSlope S ≠ partMax S - partSlope S :=
        DPbeta_slope_ne_m_sub_slope n S hS
      have h_m_mem : partMax S ∈ S := by
        exact partMax_mem _ ( DPbeta_nonempty _ _ hS )
      unfold betaOp; aesop
/-- |{S ∈ α(n) : |S| odd}| = |{S ∈ β(n) : |S| even}|. -/
theorem DPalpha_odd_card_eq_DPbeta_even_card (n : ℕ) :
    ((distinctPartitionsAlpha n).filter (fun S => S.card % 2 = 1)).card =
    ((distinctPartitionsBeta n).filter (fun S => S.card % 2 = 0)).card := by
      refine Finset.card_bij ( fun S hS => alphaOp S ) ?_ ?_ ?_
      · grind +suggestions
      · intro a₁ ha₁ a₂ ha₂ h_eq
        have := betaOp_alphaOp n a₁ (by
        aesop)
        have := betaOp_alphaOp n a₂ (by
        exact Finset.mem_filter.mp ha₂ |>.1)
        aesop
      · simp +zetaDelta at *
        exact fun S hS hS' => ⟨ betaOp S, ⟨ betaOp_mem_DPalpha n S hS, by rw [ betaOp_card n S hS ] ; omega ⟩, alphaOp_betaOp n S hS ⟩
/-- |{S ∈ α(n) : |S| even}| = |{S ∈ β(n) : |S| odd}|. -/
theorem DPalpha_even_card_eq_DPbeta_odd_card (n : ℕ) :
    ((distinctPartitionsAlpha n).filter (fun S => S.card % 2 = 0)).card =
    ((distinctPartitionsBeta n).filter (fun S => S.card % 2 = 1)).card := by
      rw [ Finset.card_filter, Finset.card_filter ]
      apply Finset.sum_bij (fun S _ => alphaOp S)
      · exact fun S hS => alphaOp_mem_DPbeta n S hS
      · exact fun a₁ ha₁ a₂ ha₂ h => by have := betaOp_alphaOp n a₁ ha₁; have := betaOp_alphaOp n a₂ ha₂; aesop
      · exact fun S hS => ⟨ betaOp S, betaOp_mem_DPalpha n S hS, alphaOp_betaOp n S hS ⟩
      · intro S hS; have := alphaOp_card n S hS; split_ifs <;> omega
/-- pe(n) - po(n) equals the signed count of special partitions. -/
theorem pe_minus_po_eq_special (n : ℕ) :
    (pe n : ℤ) - po n =
    ((distinctPartitionsSpecial n).filter (fun S => S.card % 2 = 0)).card -
    ((distinctPartitionsSpecial n).filter (fun S => S.card % 2 = 1)).card := by
      simp +decide [ pe, po, distinctPartitionsEven, distinctPartitionsOdd ]
      have h_card_diff : (Finset.filter (fun S => S.card % 2 = 0) (distinctPartitions n)).card = (Finset.filter (fun S => S.card % 2 = 0) (distinctPartitionsAlpha n)).card + (Finset.filter (fun S => S.card % 2 = 0) (distinctPartitionsBeta n)).card + (Finset.filter (fun S => S.card % 2 = 0) (distinctPartitionsSpecial n)).card := by
        rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ]
        · congr with S ; simp +decide [ DP_eq_union ]
          grind
        · simp +contextual [ Finset.disjoint_left ]
          simp_all +decide [ Finset.ext_iff, distinctPartitionsAlpha, distinctPartitionsBeta, distinctPartitionsSpecial ]
          grind
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.notMem_empty x <| DPalpha_inter_DPbeta n ▸ Finset.mem_inter_of_mem ( Finset.mem_filter.mp hx₁ |>.1 ) ( Finset.mem_filter.mp hx₂ |>.1 )
      have h_card_diff_odd : (Finset.filter (fun S => S.card % 2 = 1) (distinctPartitions n)).card = (Finset.filter (fun S => S.card % 2 = 1) (distinctPartitionsAlpha n)).card + (Finset.filter (fun S => S.card % 2 = 1) (distinctPartitionsBeta n)).card + (Finset.filter (fun S => S.card % 2 = 1) (distinctPartitionsSpecial n)).card := by
        rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ]
        · congr with S ; simp +decide [ DP_eq_union ]
          tauto
        · simp_all +decide [ Finset.disjoint_left ]
          intro S hS hS'; cases hS <;> simp_all +decide [ Finset.ext_iff ] 
          · exact Finset.notMem_empty S ( DPalpha_inter_DPspecial n ▸ Finset.mem_inter_of_mem ( by tauto ) hS' )
          · exact Finset.notMem_empty S ( DPbeta_inter_DPspecial n ▸ Finset.mem_inter_of_mem ( by tauto ) hS' )
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.notMem_empty x <| DPalpha_inter_DPbeta n ▸ Finset.mem_inter.mpr ⟨ Finset.mem_filter.mp hx₁ |>.1, Finset.mem_filter.mp hx₂ |>.1 ⟩
      nontriviality
      rw [ h_card_diff, h_card_diff_odd ]
      rw [ DPalpha_even_card_eq_DPbeta_odd_card, DPalpha_odd_card_eq_DPbeta_even_card ] ; ring
      grind
/-- **Lemma 24 (Source), case n = 0**: `p_e(0) − p_o(0) = 1`. -/
theorem pe_minus_po_zero : (pe 0 : ℤ) - po 0 = 1 := by native_decide
/-- For non-pentagonal n ≥ 1, pe(n) - po(n) = 0. -/
theorem pe_minus_po_nonpent (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 - k)
    (h2 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 + k) :
    (pe n : ℤ) - po n = 0 := by
      convert pe_minus_po_eq_special n using 1
      rw [ DPspecial_empty_of_nonpent n hn h1 h2 ] ; norm_num
/-- For n = (3k²-k)/2, pe(n) - po(n) = (-1)^k. -/
theorem pe_minus_po_pent_minus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 - k) :
    (pe n : ℤ) - po n = (-1) ^ k := by
      rw [ pe_minus_po_eq_special, DPspecial_pent_minus n k hk hn ]
      rw [ Finset.filter_singleton, Finset.filter_singleton ] ; norm_num [ SmkSet_card k hk ]
      cases Nat.mod_two_eq_zero_or_one k <;> simp +decide [ *, Nat.even_iff ]
      rw [ ← Nat.mod_add_div k 2, ‹k % 2 = _› ] ; norm_num [ pow_add, pow_mul ]
/-- For n = (3k²+k)/2, pe(n) - po(n) = (-1)^k. -/
theorem pe_minus_po_pent_plus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 + k) :
    (pe n : ℤ) - po n = (-1) ^ k := by
      rw [ pe_minus_po_eq_special, DPspecial_pent_plus n k hk hn ]
      rw [ Finset.filter_singleton, Finset.filter_singleton ]
      rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;>
        norm_num [ Nat.add_mod, Nat.mul_mod, SpkSet_card _ hk ]
      exact (Odd.neg_one_pow ⟨c, rfl⟩).symm
