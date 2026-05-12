import Mathlib
import Aristotle.Defs
open Finset
set_option maxHeartbeats 4000000
/-! # Helper lemmas for Franklin's involution -/
/-! ## consecutiveTopRun basics -/
@[simp]
lemma ctr_zero (S : Finset ℕ) : consecutiveTopRun S 0 = if (0 : ℕ) ∈ S then 1 else 0 := by
  simp [consecutiveTopRun]
@[simp]
lemma ctr_succ (S : Finset ℕ) (m : ℕ) :
    consecutiveTopRun S (m + 1) = if m + 1 ∈ S then 1 + consecutiveTopRun S m else 0 := by
  simp [consecutiveTopRun]
lemma ctr_not_mem (S : Finset ℕ) (m : ℕ) (h : m ∉ S) : consecutiveTopRun S m = 0 := by
  induction' m with m ih <;> simp_all +arith +decide
lemma ctr_pos_of_mem (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : 0 < consecutiveTopRun S m := by
  cases m <;> simp_all +decide [ Nat.succ_ne_zero, consecutiveTopRun ]
lemma ctr_le (S : Finset ℕ) (m : ℕ) (h : (0 : ℕ) ∉ S) : consecutiveTopRun S m ≤ m := by
  induction' m with m ih;
  · aesop;
  · rw [ consecutiveTopRun ] ; split_ifs <;> simp_all +arith +decide
/-
Elements in the top run are in S: if j < consecutiveTopRun S m, then m - j ∈ S.
-/
lemma ctr_mem_of_lt (S : Finset ℕ) (m j : ℕ) (hj : j < consecutiveTopRun S m) :
    m - j ∈ S := by
      induction' m with m ih generalizing j;
      · unfold consecutiveTopRun at hj; aesop;
      · by_cases h : m + 1 ∈ S <;> simp_all +decide [ Nat.sub_add_comm ];
        rcases j with ( _ | j ) <;> simp_all +decide [ Nat.sub_add_comm ];
        exact ih _ ( by linarith )
/-
The element just below the top run is not in S.
-/
lemma ctr_not_mem_boundary (S : Finset ℕ) (m : ℕ) (h0 : (0 : ℕ) ∉ S) (hm : m ∈ S) :
    m - consecutiveTopRun S m ∉ S := by
      -- By induction on m. If m = 0: ctr S 0 = 1 (since 0 ∈ S). We need 0 - 1 ∉ S, but 0 - 1 = 0 in ℕ, and 0 ∈ S. Hmm wait, we have h0 : 0 ∉ S, but hm : m = 0 ∈ S contradicts h0. So base case is vacuous. If m = k+1: ctr S (k+1) = 1 + ctr S k (since k+1 ∈ S). We need (k+1) - (1 + ctr S k) ∉ S. If k ∉ S, then ctr S k = 0, so we need k ∉ S, which holds. If k ∈ S, then by IH k - ctr S k ∉ S, and (k+1) - (1 + ctr S k) = k - ctr S k, so we're done.
      induction' m with m ih;
      · contradiction;
      · by_cases h : m ∈ S <;> simp_all +decide [ Nat.sub_sub, add_comm ];
        rw [ ctr_not_mem ] <;> aesop
/-! ## DP basics -/
lemma mem_DP (n : ℕ) (S : Finset ℕ) :
    S ∈ DP n ↔ S ⊆ Icc 1 n ∧ S.sum id = n := by
      -- By definition of DP, S ∈ DP n if and only if S is a subset of Icc 1 n and the sum of its elements is n.
      simp [DP]
lemma DP_pos_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ DP n) {x : ℕ} (hx : x ∈ S) :
    1 ≤ x := by
      exact Finset.mem_Icc.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hS |>.1 ) hx ) |>.1
lemma DP_le_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ DP n) {x : ℕ} (hx : x ∈ S) :
    x ≤ n := by
      exact Finset.mem_Icc.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hS |>.1 ) hx ) |>.2
lemma DP_zero_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ DP n) : (0 : ℕ) ∉ S := by
  exact fun h => by have := DP_pos_mem n S hS h; linarith;
lemma DP_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ DP n) : S.sum id = n := by
  exact Finset.mem_filter.mp hS |>.2
/-! ## DPalpha / DPbeta membership -/
lemma DPalpha_mem_DP (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) : S ∈ DP n := by
  exact Finset.mem_filter.mp hS |>.1
lemma DPbeta_mem_DP (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) : S ∈ DP n := by
  exact Finset.mem_filter.mp hS |>.1
lemma DPalpha_nonempty (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) : S.Nonempty := by
  exact Finset.card_pos.mp ( Finset.mem_filter.mp hS |>.2.1 )
lemma DPbeta_nonempty (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) : S.Nonempty := by
  exact Finset.card_pos.mp ( by unfold DPbeta at hS; aesop )
/-
In DPalpha, base ≤ slope.
-/
lemma DPalpha_base_le_slope (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) :
    partBase S ≤ partSlope S := by
      -- By definition of DPalpha, we know that S is in DP n and satisfies the condition.
      rw [DPalpha] at hS
      obtain ⟨hS_DP, hS_cond⟩ := Finset.mem_filter.mp hS;
      omega
/-
In DPbeta, base > slope (i.e., slope < base).
-/
lemma DPbeta_slope_lt_base (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    partSlope S < partBase S := by
      unfold DPbeta at hS;
      grind
/-! ## Key inequality for alpha: m ≥ 2b -/
/-
For S ∈ DPalpha(n), max(S) ≥ 2 * base(S).
-/
lemma DPalpha_max_ge_2base (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) :
    2 * partBase S ≤ partMax S := by
      unfold DPalpha at hS;
      unfold partBase partSlope partMax at *;
      split_ifs at * <;> simp_all +decide [ two_mul ];
      have := ctr_mem_of_lt S ( Finset.max' S ‹_› ) ( consecutiveTopRun S ( Finset.max' S ‹_› ) - 1 ) ?_ <;> simp_all +decide [ Nat.sub_add_cancel ];
      · have := Finset.min'_le _ _ this; omega;
      · exact ctr_pos_of_mem S _ ( Finset.max'_mem _ ‹_› )
/-! ## Key inequality for beta: m ≥ 2s + 1 -/
/-
For S ∈ DPbeta(n), max(S) ≥ 2 * slope(S) + 1.
-/
lemma DPbeta_max_ge_2slope_add_1 (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    2 * partSlope S + 1 ≤ partMax S := by
      -- Since S is nonempty, we can apply the definition of partBase.
      have h_base_le_max : partBase S ≤ partMax S - partSlope S + 1 := by
        unfold partBase;
        split_ifs <;> simp_all +decide [ partMax, partSlope ];
        rename_i h;
        have h_min_le_max_minus_slope_plus_one : ∀ j < consecutiveTopRun S (S.max' h), S.min' h ≤ S.max' h - j := by
          exact fun j hj => Finset.min'_le _ _ <| ctr_mem_of_lt _ _ _ hj;
        specialize h_min_le_max_minus_slope_plus_one ( consecutiveTopRun S ( S.max' h ) - 1 ) ; rcases k : consecutiveTopRun S ( S.max' h ) with ( _ | _ | k ) <;> simp_all +decide [ Nat.sub_sub ];
        · exact Nat.le_succ_of_le ( Finset.min'_le _ _ ( Finset.max'_mem _ h ) );
        · grind;
        · omega;
      unfold DPbeta at hS;
      grind
/-! ## partBase / partMax for nonempty sets -/
lemma partBase_mem (S : Finset ℕ) (hne : S.Nonempty) : partBase S ∈ S := by
  -- By definition of `partBase`, it is the minimum element of `S` when `S` is nonempty.
  simp [partBase, hne];
  exact Finset.min'_mem _ hne
lemma partMax_mem (S : Finset ℕ) (hne : S.Nonempty) : partMax S ∈ S := by
  -- By definition of `partMax`, it is the maximum element of the set `S`, which is nonempty.
  simp [partMax, hne];
  exact Finset.max'_mem _ _
lemma partBase_le_partMax (S : Finset ℕ) (hne : S.Nonempty) : partBase S ≤ partMax S := by
  unfold partBase partMax;
  split_ifs ; exact Finset.min'_le _ _ ( Finset.max'_mem _ hne )
lemma partBase_le (S : Finset ℕ) (hne : S.Nonempty) {x : ℕ} (hx : x ∈ S) :
    partBase S ≤ x := by
      unfold partBase;
      split_ifs ; exact Finset.min'_le _ _ hx
lemma le_partMax (S : Finset ℕ) (hne : S.Nonempty) {x : ℕ} (hx : x ∈ S) :
    x ≤ partMax S := by
      unfold partMax;
      split_ifs ; exact Finset.le_max' _ _ hx
/-! ## partSlope is positive for nonempty S -/
lemma partSlope_pos (S : Finset ℕ) (hne : S.Nonempty) (h0 : (0 : ℕ) ∉ S) :
    0 < partSlope S := by
      refine' ctr_pos_of_mem S _ ( partMax_mem S hne )
/-! ## partSlope ≤ partMax -/
lemma partSlope_le_partMax (S : Finset ℕ) (h0 : (0 : ℕ) ∉ S) :
    partSlope S ≤ partMax S := by
      convert ctr_le _ _ h0 using 1
/-! ## alphaOp key properties -/
/-
m - b + 1 ∈ S for S ∈ DPalpha (it's in the slope set)
-/
lemma DPalpha_m_sub_b_add_1_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) :
    partMax S - partBase S + 1 ∈ S := by
      convert ctr_mem_of_lt S ( partMax S ) ( partBase S - 1 ) _ using 1;
      · rw [ tsub_tsub_assoc ];
        · exact partBase_le_partMax S ( DPalpha_nonempty n S hS );
        · exact DP_pos_mem n S ( DPalpha_mem_DP n S hS ) ( partBase_mem S ( DPalpha_nonempty n S hS ) );
      · refine' lt_of_lt_of_le ( Nat.sub_lt _ _ ) _;
        · exact DP_pos_mem n S ( DPalpha_mem_DP n S hS ) ( partBase_mem S ( DPalpha_nonempty n S hS ) );
        · norm_num;
        · convert DPalpha_base_le_slope n S hS using 1
/-
b ≠ m - b + 1 for S ∈ DPalpha (follows from m ≥ 2b)
-/
lemma DPalpha_base_ne_m_sub_b_add_1 (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) :
    partBase S ≠ partMax S - partBase S + 1 := by
      have := DPalpha_max_ge_2base n S hS; omega;
/-
m + 1 ∉ S
-/
lemma partMax_succ_not_mem (S : Finset ℕ) (hne : S.Nonempty) :
    partMax S + 1 ∉ S := by
      exact fun h => not_lt_of_ge ( le_partMax _ hne h ) ( Nat.lt_succ_self _ )
/-
alphaOp preserves sum
-/
lemma alphaOp_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) :
    (alphaOp S).sum id = S.sum id := by
      unfold alphaOp;
      rw [ Finset.sum_insert ] <;> norm_num;
      · rw [ ← Finset.sum_erase_add _ _ ( show partBase S ∈ S from ?_ ), ← Finset.sum_erase_add _ _ ( show partMax S - partBase S + 1 ∈ S.erase ( partBase S ) from ?_ ) ];
        · linarith [ Nat.sub_add_cancel ( show partBase S ≤ partMax S from partBase_le_partMax S ( DPalpha_nonempty n S hS ) ) ];
        · exact Finset.mem_erase_of_ne_of_mem ( Ne.symm ( DPalpha_base_ne_m_sub_b_add_1 n S hS ) ) ( DPalpha_m_sub_b_add_1_mem n S hS );
        · exact partBase_mem S ( DPalpha_nonempty n S hS );
      · exact fun _ _ => partMax_succ_not_mem S ( DPalpha_nonempty n S hS )
/-
max of alphaOp S = max(S) + 1
-/
lemma alphaOp_partMax (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) :
    partMax (alphaOp S) = partMax S + 1 := by
      refine' le_antisymm _ _;
      · unfold partMax; simp +decide [ alphaOp ] ;
        unfold partMax; split_ifs <;> simp_all +decide [ Finset.le_max' ] ;
        exact fun a ha₁ ha₂ ha₃ => Nat.le_succ_of_le ( Finset.le_max' _ _ ha₃ );
      · -- Since $m+1$ is in the set, it is an upper bound for the set.
        have h_upper_bound : ∀ x ∈ alphaOp S, x ≤ partMax (alphaOp S) := by
          unfold partMax;
          split_ifs <;> simp_all +decide [ Finset.max' ];
          exact fun x hx => ⟨ x, hx, le_rfl ⟩;
        exact h_upper_bound _ ( Finset.mem_insert_self _ _ )
/-
slope of alphaOp S = base(S)
-/
lemma alphaOp_partSlope (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPalpha n) :
    partSlope (alphaOp S) = partBase S := by
      -- By definition of `partMax`, we know that `partMax (alphaOp S) = partMax S + 1`.
      have h_partMax : partMax (alphaOp S) = partMax S + 1 := by
        grind +suggestions;
      have h_consecutiveTopRun : ∀ j < partBase S, partMax S + 1 - j ∈ alphaOp S := by
        intro j hj;
        by_cases hj' : j = 0;
        · unfold alphaOp; aesop;
        · have h_consecutiveTopRun : partMax S + 1 - j ∈ S := by
            have h_consecutiveTopRun : partMax S + 1 - j ∈ S := by
              have h_consecutiveTopRun : partMax S - (j - 1) ∈ S := by
                apply ctr_mem_of_lt;
                exact lt_of_lt_of_le ( Nat.sub_lt ( Nat.pos_of_ne_zero hj' ) zero_lt_one ) ( le_trans ( Nat.le_of_lt hj ) ( DPalpha_base_le_slope n S hS ) )
              lia;
            exact h_consecutiveTopRun;
          have h_consecutiveTopRun : partMax S + 1 - j ≠ partBase S ∧ partMax S + 1 - j ≠ partMax S - partBase S + 1 := by
            constructor <;> intro h <;> have := DPalpha_max_ge_2base n S hS <;> omega;
          unfold alphaOp; aesop;
      have h_consecutiveTopRun_zero : partMax S + 1 - partBase S ∉ alphaOp S := by
        unfold alphaOp;
        simp +decide [ Nat.sub_add_comm ( show partBase S ≤ partMax S from partBase_le_partMax S ( DPalpha_nonempty n S hS ) ) ];
        exact ne_of_lt ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by
          intro h; simp_all +decide [ partMax ] ;
          exact absurd ( h ( DPalpha_nonempty n S hS ) ▸ Finset.max'_mem _ ( DPalpha_nonempty n S hS ) ) ( by have := DP_pos_mem n S ( DPalpha_mem_DP n S hS ) ( Finset.max'_mem _ ( DPalpha_nonempty n S hS ) ) ; aesop ) ) ) ( Nat.pos_of_ne_zero ( by
          exact Nat.ne_of_gt ( DP_pos_mem n S ( DPalpha_mem_DP n S hS ) ( partBase_mem S ( DPalpha_nonempty n S hS ) ) ) ) ) );
      have h_consecutiveTopRun_eq : ∀ m, consecutiveTopRun (alphaOp S) m = if m ∈ alphaOp S then 1 + consecutiveTopRun (alphaOp S) (m - 1) else 0 := by
        intro m; induction' m with m ih <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
        split_ifs <;> simp_all +decide [ alphaOp ];
        exact absurd ( DP_zero_not_mem n S ( DPalpha_mem_DP n S hS ) ) ( by tauto );
      have h_consecutiveTopRun_eq : ∀ j ≤ partBase S, consecutiveTopRun (alphaOp S) (partMax S + 1 - j) = partBase S - j := by
        intro j hj;
        induction' hj : partBase S - j with k hk generalizing j;
        · grind;
        · grind;
      convert h_consecutiveTopRun_eq 0 bot_le using 1;
      exact h_partMax.symm ▸ rfl
/-! ## betaOp key properties -/
/-
s ∉ S for S ∈ DPbeta (slope < base = min(S))
-/
lemma DPbeta_slope_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    partSlope S ∉ S := by
      -- Since partSlope S is less than partBase S, and partBase S is the minimum element of S, partSlope S must be smaller than all elements in S.
      have h_min : ∀ x ∈ S, partSlope S < x := by
        intros x hx; exact lt_of_lt_of_le (DPbeta_slope_lt_base n S hS) (partBase_le S (DPbeta_nonempty n S hS) hx) ;
      exact fun h => lt_irrefl _ ( h_min _ h )
/-
m - s ∉ S for S ∈ DPbeta (otherwise slope would extend)
-/
lemma DPbeta_m_sub_s_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    partMax S - partSlope S ∉ S := by
      apply ctr_not_mem_boundary;
      · exact DP_zero_not_mem n S ( DPbeta_mem_DP n S hS );
      · exact partMax_mem S ( DPbeta_nonempty n S hS )
/-
s ≠ m - s for S ∈ DPbeta (from m ≥ 2s+1)
-/
lemma DPbeta_slope_ne_m_sub_slope (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    partSlope S ≠ partMax S - partSlope S := by
      exact fun h => by have := DPbeta_max_ge_2slope_add_1 n S hS; omega;
/-
betaOp preserves sum
-/
lemma betaOp_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    (betaOp S).sum id = S.sum id := by
      have h_betaOp_sum : (insert (partSlope S) (insert (partMax S - partSlope S) S)).sum id = S.sum id + partSlope S + (partMax S - partSlope S) := by
        rw [ Finset.sum_insert, Finset.sum_insert ] <;> norm_num;
        · ring;
        · exact?;
        · exact ⟨ DPbeta_slope_ne_m_sub_slope n S hS, DPbeta_slope_not_mem n S hS ⟩;
      convert congr_arg ( fun x : ℕ => x - partMax S ) h_betaOp_sum using 1;
      · exact eq_tsub_of_add_eq <| Finset.sum_erase_add _ _ <| Finset.mem_insert_of_mem <| Finset.mem_insert_of_mem <| partMax_mem _ <| DPbeta_nonempty _ _ hS;
      · rw [ Nat.add_assoc, Nat.add_sub_of_le ];
        · rw [ Nat.add_sub_cancel ];
        · apply partSlope_le_partMax;
          exact DP_zero_not_mem n S ( DPbeta_mem_DP n S hS )
/-
max of betaOp S = max(S) - 1
-/
lemma betaOp_partMax (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    partMax (betaOp S) = partMax S - 1 := by
      refine' le_antisymm _ _;
      · have h_max_betaOp : ∀ x ∈ betaOp S, x ≤ partMax S - 1 := by
          unfold betaOp; simp +decide ;
          rintro x hx ( rfl | rfl | hx );
          · exact Nat.le_sub_one_of_lt ( lt_of_le_of_ne ( partSlope_le_partMax S ( DP_zero_not_mem n S ( DPbeta_mem_DP n S hS ) ) ) hx );
          · exact Nat.sub_le_sub_left ( partSlope_pos S ( DPbeta_nonempty n S hS ) ( DP_zero_not_mem n S ( DPbeta_mem_DP n S hS ) ) ) _;
          · exact Nat.le_sub_one_of_lt ( lt_of_le_of_ne ( le_partMax _ ( DPbeta_nonempty _ _ hS ) hx ) ‹_› );
        by_cases h : ( betaOp S ).Nonempty <;> simp_all +decide [ partMax ];
      · -- Since $m - 1 \in S \setminus \{m\}$, we have $m - 1 \in betaOp S$.
        have h_mem : partMax S - 1 ∈ betaOp S := by
          unfold betaOp; simp +decide [ *, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton ] ;
          refine' ⟨ Nat.ne_of_lt ( Nat.sub_lt _ _ ), _ ⟩;
          · exact Nat.pos_of_ne_zero fun h => by have := partMax_mem S ( DPbeta_nonempty n S hS ) ; have := DP_zero_not_mem n S ( DPbeta_mem_DP n S hS ) ; aesop;
          · norm_num;
          · by_cases h : partSlope S = 1;
            · aesop;
            · refine' Or.inr <| Or.inr <| ctr_mem_of_lt _ _ _ _;
              exact lt_of_le_of_ne ( Nat.succ_le_of_lt ( partSlope_pos S ( DPbeta_nonempty n S hS ) ( DP_zero_not_mem n S ( DPbeta_mem_DP n S hS ) ) ) ) ( Ne.symm h );
        exact le_partMax _ ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) h_mem
/-
base of betaOp S = slope(S)
-/
lemma betaOp_partBase (n : ℕ) (S : Finset ℕ) (hS : S ∈ DPbeta n) :
    partBase (betaOp S) = partSlope S := by
      refine' le_antisymm _ _ <;> simp_all +decide [ partBase, partSlope ];
      · split_ifs <;> simp_all +decide [ Finset.min', betaOp ];
        exact ⟨ partSlope S, ⟨ by linarith [ DPbeta_slope_lt_base n S hS, partBase_le S ( DPbeta_nonempty n S hS ) ( partMax_mem S ( DPbeta_nonempty n S hS ) ) ], Or.inl rfl ⟩, le_rfl ⟩;
      · have h_all_ge_slope : ∀ x ∈ S.erase (partMax S), partSlope S ≤ x := by
          intro x hx
          have h_slope_lt_base : partSlope S < partBase S := by
            exact?
          have h_base_le_x : partBase S ≤ x := by
            exact partBase_le _ ( DPbeta_nonempty _ _ hS ) ( Finset.mem_of_mem_erase hx )
          linarith [h_slope_lt_base, h_base_le_x];
        have h_all_ge_slope : partSlope S ∈ betaOp S ∧ ∀ x ∈ betaOp S, x ≠ partSlope S → partSlope S < x := by
          unfold betaOp; simp +decide [ Finset.mem_erase, Finset.mem_insert ] ;
          constructor;
          · exact ne_of_lt ( lt_of_lt_of_le ( DPbeta_slope_lt_base n S hS ) ( partBase_le_partMax S ( DPbeta_nonempty n S hS ) ) );
          · rintro x hx₁ ( rfl | rfl | hx₂ ) hx₃ <;> simp_all +decide [ Nat.sub_sub ];
            · have := DPbeta_max_ge_2slope_add_1 n S hS; omega;
            · exact lt_of_le_of_ne ( h_all_ge_slope x hx₁ hx₂ ) ( Ne.symm hx₃ );
        have h_min_ge_slope : ∀ x ∈ betaOp S, x ≥ partSlope S := by
          exact fun x hx => if hx' : x = partSlope S then hx'.symm ▸ le_rfl else le_of_lt ( h_all_ge_slope.2 x hx hx' );
        aesop
