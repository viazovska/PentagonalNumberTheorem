import Mathlib
import RequestProject.PentagonalDefs

/-!
# Franklin's Involution and the Pentagonal Number Theorem (Combinatorial Form)
-/

open scoped BigOperators
open Finset

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Staircase length -/

def consecDown (S : Finset ℕ) : ℕ → ℕ
  | 0 => if 0 ∈ S then 1 else 0
  | n + 1 => if n + 1 ∈ S then consecDown S n + 1 else 0

def stairLen (S : Finset ℕ) (hne : S.Nonempty) : ℕ :=
  consecDown S (S.max' hne)

abbrev DistPartSet (n : ℕ) := ((Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n))

/-! ## Properties of consecDown and stairLen -/

lemma consecDown_pos (S : Finset ℕ) (m : ℕ) (hm : m ∈ S) : 0 < consecDown S m := by
  induction' m with m ih <;> grind +locals

lemma stairLen_pos (S : Finset ℕ) (hne : S.Nonempty) : 0 < stairLen S hne :=
  consecDown_pos S _ (Finset.max'_mem S hne)

lemma consecDown_le_card (S : Finset ℕ) (m : ℕ) : consecDown S m ≤ S.card := by
  have h : ∀ m, consecDown S m ≤ (Finset.filter (fun x => x ∈ S) (Finset.range (m + 1))).card := by
    intro m
    induction' m with m ih <;> simp_all +decide [Finset.filter]
    · by_cases h : 0 ∈ S <;> simp +decide [h, consecDown]
      rw [Multiset.filter_singleton]; aesop
    · rw [show consecDown S (m + 1) = if m + 1 ∈ S then consecDown S m + 1 else 0 from rfl]
      split_ifs <;> simp_all +decide [Multiset.filter_cons]
  exact le_trans (h m) (Finset.card_le_card fun x hx => by aesop)

lemma stairLen_le_card (S : Finset ℕ) (hne : S.Nonempty) : stairLen S hne ≤ S.card :=
  consecDown_le_card S (S.max' hne)

lemma staircase_mem (S : Finset ℕ) (hne : S.Nonempty) (j : ℕ) (hj : j < stairLen S hne) :
    S.max' hne - j ∈ S := by
  have h_ind : ∀ m, ∀ j, j < consecDown S m → m - j ∈ S := by
    intro m j hj
    induction' m with m ih generalizing j
    · unfold consecDown at hj; aesop
    · rcases j with (_ | j) <;> simp_all +decide [Nat.sub_sub]
      · contrapose! hj; simp_all +decide [consecDown]
      · exact ih j (by rw [show consecDown S (m + 1) = if m + 1 ∈ S then consecDown S m + 1 else 0 from rfl] at hj; split_ifs at hj <;> linarith)
  exact h_ind _ _ hj

lemma below_staircase_nmem (S : Finset ℕ) (hne : S.Nonempty)
    (hℓ : stairLen S hne ≤ S.max' hne) :
    S.max' hne - stairLen S hne ∉ S := by
  set M := S.max' hne; set ℓ := stairLen S hne
  by_contra h_contra
  have h1 : 1 ≤ consecDown S (M - ℓ) := consecDown_pos S _ h_contra
  have h2 : ∀ i ≤ ℓ, consecDown S (M - ℓ + i) = consecDown S (M - ℓ) + i := by
    intro i hi; induction' i with i ih <;> simp_all +decide
    have : consecDown S (M - ℓ + (i + 1)) = consecDown S (M - ℓ + i) + 1 := by
      have : M - ℓ + (i + 1) ∈ S := by
        convert staircase_mem S hne (ℓ - (i + 1)) _ using 1 <;> omega
      exact if_pos this
    linarith [ih hi.le]
  specialize h2 ℓ le_rfl; simp_all +decide [Nat.sub_add_cancel hℓ]
  linarith [show ℓ = consecDown S M from rfl]

/-! ## Franklin's involution -/

/-- Franklin's involution. Returns a partner partition with opposite card parity,
    or itself at fixed points. -/
def franklinMap (S : Finset ℕ) : Finset ℕ :=
  if hne : S.Nonempty then
    let s := S.min' hne
    let M := S.max' hne
    let ℓ := stairLen S hne
    if s ≤ ℓ ∧ ¬(s = ℓ ∧ S.card = ℓ) then
      -- Operation A
      (S.erase s \ {M - s + 1}) ∪ {M + 1}
    else if s > ℓ ∧ 2 * ℓ < M then
      -- Operation B
      (S.erase M) ∪ ({M - ℓ} ∪ {ℓ})
    else
      S -- fixed point
  else
    S

/-! ## Operation A properties -/

/-
In Operation A: s ≠ M - s + 1 (proved by contradiction: equality implies fixed point)
-/
lemma opA_s_ne_complement {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_le : S.min' hne ≤ stairLen S hne)
    (hnfp : ¬(S.min' hne = stairLen S hne ∧ S.card = stairLen S hne)) :
    S.min' hne ≠ S.max' hne - S.min' hne + 1 := by
      intro h_eq
      have h_staircase : S = Finset.Icc (S.max' hne - S.min' hne + 1) (S.max' hne) := by
        refine' Finset.Subset.antisymm _ _ <;> intro x hx <;> simp +decide at *;
        · have h_staircase : ∀ j < stairLen S hne, S.max' hne - j ∈ S := by
            grind +suggestions;
          grind +suggestions;
        · -- Since $x$ is between $S.max' hne - S.min' hne$ and $S.max' hne$, it must be in the staircase.
          have hx_staircase : x ∈ Finset.image (fun j => S.max' hne - j) (Finset.range (stairLen S hne)) := by
            simp +zetaDelta at *;
            refine' ⟨ S.max' hne - x, _, _ ⟩ <;> omega;
          obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp hx_staircase; exact staircase_mem S hne j ( Finset.mem_range.mp hj ) ;
      generalize_proofs at *; (
      refine' hnfp ⟨ _, _ ⟩ <;> rw [ h_staircase ] at * <;> norm_num at *;
      · refine' le_antisymm _ _ <;> contrapose! h_eq <;> norm_num at *;
        · exact absurd ( h_eq _ ( Finset.min'_mem _ ‹_› ) ) ( by linarith );
        · have h_staircase : (S.max' ‹_› - S.min' ‹_›) + 1 = stairLen S ‹_› := by
            have h_staircase_def : ∀ j < stairLen S ‹_›, S.max' ‹_› - j ∈ S := by
              exact?
            grind +suggestions
          generalize_proofs at *; (
          linarith [ Nat.sub_add_cancel ( show S.min' ‹_› ≤ S.max' ‹_› from Finset.min'_le _ _ ( Finset.max'_mem _ _ ) ) ]);
      · rw [ ← h_staircase ] at *; simp +decide [ stairLen ] at *; (
        have h_staircase : ∀ m ∈ S, m ≥ S.max' ‹_› - consecDown S (S.max' ‹_›) + 1 := by
          intro m hm; have := Finset.min'_le _ _ hm; omega;
        generalize_proofs at *; (
        have h_staircase : Finset.card (Finset.Icc (S.max' ‹_› - consecDown S (S.max' ‹_›) + 1) (S.max' ‹_›)) = consecDown S (S.max' ‹_›) := by
          simp +arith +decide [ Nat.sub_sub, add_comm ];
          rw [ Nat.sub_sub_self ];
          have h_staircase : ∀ m, consecDown S m ≤ m := by
            intro m; induction' m with m ih <;> simp +decide [ *, consecDown ] ;
            · exact fun h => by simpa using hne.2 0 h;
            · split_ifs <;> linarith
          generalize_proofs at *; (
          exact h_staircase _)
        generalize_proofs at *; (
        refine' le_antisymm _ _ <;> try linarith [ consecDown_le_card S ( S.max' ‹_› ) ] ;
        exact h_staircase ▸ Finset.card_le_card ( fun x hx => Finset.mem_Icc.mpr ⟨ by solve_by_elim, Finset.le_max' _ _ hx ⟩ )))))

/-
Operation A preserves sum
-/
lemma opA_sum {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_le : S.min' hne ≤ stairLen S hne)
    (hnfp : ¬(S.min' hne = stairLen S hne ∧ S.card = stairLen S hne)) :
    ((S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1}) ∪ {S.max' hne + 1}).sum id = n := by
      have h_erase : S.min' hne ∈ S ∧ S.max' hne - S.min' hne + 1 ∈ S ∧ S.max' hne + 1 ∉ S := by
        refine' ⟨ Finset.min'_mem _ hne, _, _ ⟩;
        · convert staircase_mem S hne ( S.min' hne - 1 ) _ using 1;
          · rw [ tsub_tsub_assoc ];
            · exact Finset.min'_le _ _ ( Finset.max'_mem _ hne );
            · exact Finset.mem_Icc.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hS |>.1 ) ( Finset.min'_mem _ hne ) ) |>.1;
          · exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < S.min' hne from Finset.mem_Icc.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hS |>.1 ) ( Finset.min'_mem _ hne ) ) |>.1 ) ) ) hs_le;
        · exact fun h => not_lt_of_ge ( Finset.le_max' _ _ h ) ( Nat.lt_succ_self _ );
      have h_erase : S.sum id - S.min' hne - (S.max' hne - S.min' hne + 1) + (S.max' hne + 1) = n := by
        rw [ Nat.sub_sub, tsub_add_eq_add_tsub ];
        · exact Nat.sub_eq_of_eq_add <| by linarith! [ Nat.sub_add_cancel <| show S.min' hne ≤ S.max' hne from Finset.min'_le _ _ <| Finset.max'_mem _ hne, show S.sum id = n from Finset.mem_filter.mp hS |>.2 ] ;
        · have h_erase : S.sum id ≥ S.min' hne + (S.max' hne - S.min' hne + 1) := by
            have h_erase : S.sum id ≥ Finset.sum {S.min' hne, S.max' hne - S.min' hne + 1} id := by
              exact Finset.sum_le_sum_of_subset ( Finset.insert_subset_iff.mpr ⟨ h_erase.1, Finset.singleton_subset_iff.mpr h_erase.2.1 ⟩ )
            grind +suggestions;
          exact h_erase;
      rw [ ← h_erase, Finset.sum_union ] <;> simp +decide [ *, Finset.sum_singleton, Finset.sum_sdiff, Finset.subset_iff ];
      rw [ ← Finset.sum_sdiff ( Finset.insert_subset_iff.mpr ⟨ ‹S.min' hne ∈ S ∧ S.max' hne - S.min' hne + 1 ∈ S ∧ S.max' hne + 1 ∉ S›.1, Finset.singleton_subset_iff.mpr ‹S.min' hne ∈ S ∧ S.max' hne - S.min' hne + 1 ∈ S ∧ S.max' hne + 1 ∉ S›.2.1 ⟩ ) ];
      rw [ Finset.sum_pair ] <;> norm_num;
      · rw [ show S.erase ( S.min' hne ) \ { S.max' hne - S.min' hne + 1 } = S \ { S.min' hne, S.max' hne - S.min' hne + 1 } from ?_ ];
        · exact eq_tsub_of_add_eq <| eq_tsub_of_add_eq <| by ring;
        · grind;
      · exact?

/-
Operation A maps valid partitions to valid partitions
-/
lemma opA_valid {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_le : S.min' hne ≤ stairLen S hne)
    (hnfp : ¬(S.min' hne = stairLen S hne ∧ S.card = stairLen S hne)) :
    (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1}) ∪ {S.max' hne + 1} ∈ DistPartSet n := by
      grind +suggestions

/-
Operation A decreases card by 1
-/
lemma opA_card {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_le : S.min' hne ≤ stairLen S hne)
    (hnfp : ¬(S.min' hne = stairLen S hne ∧ S.card = stairLen S hne)) :
    ((S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1}) ∪ {S.max' hne + 1}).card + 1 = S.card := by
      have h_card_erase : ((S.max' hne - S.min' hne + 1) ∈ S.erase (S.min' hne)) := by
        apply Finset.mem_erase_of_ne_of_mem;
        · grind +suggestions;
        · convert staircase_mem S hne ( S.min' hne - 1 ) _ using 1;
          · rw [ tsub_tsub_assoc ];
            · exact Finset.min'_le _ _ ( Finset.max'_mem _ hne );
            · exact Finset.mem_Icc.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hS |>.1 ) ( Finset.min'_mem _ hne ) ) |>.1;
          · exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < S.min' hne from Finset.mem_Icc.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hS |>.1 ) ( Finset.min'_mem _ _ ) ) |>.1 ) ) ) hs_le;
      rw [ Finset.card_union_of_disjoint ] <;> simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
      · rw [ Nat.sub_add_cancel ] <;> norm_num [ Finset.card_erase_of_mem ( Finset.min'_mem _ hne ) ];
        · exact Nat.succ_pred_eq_of_pos ( Finset.card_pos.mpr hne );
        · exact Nat.le_sub_one_of_lt ( Finset.one_lt_card.2 ⟨ _, h_card_erase.2, _, Finset.min'_mem _ hne, by aesop ⟩ );
      · exact fun _ _ => absurd ( Finset.le_max' _ _ ‹_› ) ( by omega )

/-! ## Operation B properties -/

/-
Operation B preserves sum
-/
lemma opB_sum {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_gt : S.min' hne > stairLen S hne) (hM : 2 * stairLen S hne < S.max' hne) :
    ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).sum id = n := by
      rw [ Finset.sum_union, Finset.sum_union ] <;> norm_num;
      · rw [ Nat.sub_add_cancel ];
        · rw [ Finset.sum_erase_add _ _ ( Finset.max'_mem _ hne ), ← Finset.mem_filter.mp hS |>.2 ];
          rfl;
        · grind;
      · omega;
      · grind +suggestions

/-
Operation B maps valid partitions to valid partitions
-/
lemma opB_valid {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_gt : S.min' hne > stairLen S hne) (hM : 2 * stairLen S hne < S.max' hne) :
    (S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne}) ∈ DistPartSet n := by
      refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
      · simp_all +decide [ Finset.subset_iff ];
        exact ⟨ ⟨ Nat.sub_pos_of_lt ( hs_gt _ ( Finset.max'_mem _ hne ) ), fun y hy => by linarith [ hS.1 hy ] ⟩, stairLen_pos _ hne, by linarith [ hS.1 ( Finset.max'_mem _ hne ), hs_gt _ ( Finset.max'_mem _ hne ) ] ⟩;
      · convert opB_sum S hS hne hs_gt hM using 1

/-
Operation B increases card by 1
-/
lemma opB_card {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_gt : S.min' hne > stairLen S hne) (hM : 2 * stairLen S hne < S.max' hne) :
    ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).card = S.card + 1 := by
      rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num;
      · rw [ Finset.card_erase_of_mem ( Finset.max'_mem _ hne ) ] ; ring;
        linarith [ Nat.sub_add_cancel ( show 1 ≤ Finset.card S from Finset.card_pos.mpr hne ) ];
      · omega;
      · constructor;
        · exact fun _ => below_staircase_nmem S hne ( by linarith );
        · exact fun _ => fun h => not_lt_of_ge ( Finset.min'_le _ _ h ) hs_gt

/-! ## Involution property -/

/-
If Operation A applied to S produces S', then applying franklinMap to S' gives S back.
    Key: S' has max = M+1, stairLen = s, and Operation B reverses A.
-/
lemma opB_reverses_opA {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_le : S.min' hne ≤ stairLen S hne)
    (hnfp : ¬(S.min' hne = stairLen S hne ∧ S.card = stairLen S hne)) :
    franklinMap ((S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1}) ∪ {S.max' hne + 1}) = S := by
      revert hnfp hS hne hs_le;
      intro hS hne hs_le hnfp
      have h_max : (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}).max' (by
      exact ⟨ _, Finset.mem_union_right _ ( Finset.mem_singleton_self _ ) ⟩) = S.max' hne + 1 := by
        refine' le_antisymm _ _ <;> simp_all +decide [ Finset.max' ];
        · exact fun a ha₁ ha₂ ha₃ => Nat.le_succ_of_le ( Finset.le_sup' ( fun x => x ) ha₂ );
        · exact Or.inl fun i hi => ⟨ i, hi, le_rfl ⟩
      generalize_proofs at *;
      have h_stairLen : stairLen (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}) (by
      assumption) = S.min' hne := by
        have h_stairLen : ∀ j < S.min' hne, (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}).max' ‹_› - j ∈ (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}) := by
          intro j hj
          by_cases h_case : j = 0;
          · grind;
          · have h_stairLen : S.max' hne - j + 1 ∈ S := by
              have h_stairLen : S.max' hne - (j - 1) ∈ S := by
                apply staircase_mem;
                omega;
              grind +splitImp;
            simp_all +decide [ Finset.mem_union, Finset.mem_sdiff ];
            grind +suggestions;
        have h_stairLen : (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}).max' ‹_› - S.min' hne ∉ (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}) := by
          simp_all +decide [ Nat.sub_sub ];
          exact ⟨ Nat.ne_of_lt ( Nat.sub_lt ( Nat.succ_pos _ ) ( Finset.mem_Icc.mp ( hS.1 ( Finset.min'_mem _ hne ) ) |>.1 ) ), fun _ _ => by rw [ tsub_add_eq_add_tsub ( Finset.min'_le _ _ ( Finset.max'_mem _ hne ) ) ] ⟩;
        refine' le_antisymm _ _;
        · grind +suggestions;
        · grind +suggestions
      generalize_proofs at *;
      have h_min : (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}).min' (by
      assumption) > S.min' hne := by
        simp_all +decide [ Finset.min' ];
        exact ⟨ ⟨ _, Finset.min'_mem _ hne, Finset.min'_le _ _ ( Finset.max'_mem _ hne ) ⟩, fun a ha₁ ha₂ ha₃ => ⟨ _, Finset.min'_mem _ hne, lt_of_le_of_ne ( Finset.min'_le _ _ ha₂ ) ( Ne.symm ha₁ ) ⟩ ⟩
      generalize_proofs at *;
      have h_M_gt_2s : S.max' hne + 1 > 2 * S.min' hne := by
        have h_M_gt_2s : S.max' hne ≥ S.min' hne + stairLen S hne - 1 := by
          have h_card : ∀ j < stairLen S hne, S.max' hne - j ∈ S := by
            exact?;
          have h_card : S.min' hne ≤ S.max' hne - (stairLen S hne - 1) := by
            exact Finset.min'_le _ _ ( h_card _ ( Nat.sub_lt ( stairLen_pos _ hne ) zero_lt_one ) );
          grind +locals
        generalize_proofs at *;
        grind +suggestions
      generalize_proofs at *;
      have h_opB : franklinMap (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}) = (S.erase (S.min' hne) \ {S.max' hne - S.min' hne + 1} ∪ {S.max' hne + 1}).erase (S.max' hne + 1) ∪ ({S.max' hne + 1 - S.min' hne} ∪ {S.min' hne}) := by
        unfold franklinMap;
        grind;
      simp_all +decide [ Finset.ext_iff ];
      intro a; by_cases ha : a = S.min' hne <;> by_cases ha' : a = S.max' hne - S.min' hne + 1 <;> simp +decide [ ha, ha' ] ;
      · exact Finset.min'_mem _ hne;
      · exact Finset.min'_mem _ hne;
      · constructor <;> intro <;> simp_all +decide [ Nat.sub_add_comm h_min.1 ];
        convert staircase_mem S hne ( S.min' hne - 1 ) _ using 1;
        · rw [ tsub_tsub_assoc ] <;> norm_num [ h_min.1 ];
          exact fun x hx => Finset.mem_Icc.mp ( hS.1 hx ) |>.1;
        · exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Finset.min'_mem S hne |> fun x => Finset.mem_Icc.mp ( hS.1 x ) |>.1 ) ) ) hs_le;
      · by_cases ha'' : a = S.max' hne + 1 <;> simp +decide [ ha'', ha, ha' ];
        · exact iff_of_false ( Nat.ne_of_gt ( Nat.sub_lt ( Nat.succ_pos _ ) ( Finset.min'_mem _ hne |> fun x => Finset.mem_Icc.mp ( hS.1 x ) |>.1 ) ) ) ( by intro h; have := Finset.le_max' _ _ h; linarith );
        · lia

/-
The staircase length of B(S) is at least ℓ (the old staircase length)
-/
lemma opB_result_stairLen_ge {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_gt : S.min' hne > stairLen S hne) (hM : 2 * stairLen S hne < S.max' hne)
    (hne' : ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).Nonempty)
    (hmax' : ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).max' hne' = S.max' hne - 1) :
    stairLen ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})) hne' ≥ stairLen S hne := by
      have h_stair_len_ge_ell : ∀ j < stairLen S hne, (S.erase (S.max' hne) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).max' hne' - j ∈ S.erase (S.max' hne) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne}) := by
        intros j hj
        by_cases hj_cases : j < stairLen S hne - 1;
        · have := staircase_mem S hne ( j + 1 ) ( by omega ) ; simp_all +decide [ Nat.sub_sub ] ;
          exact Or.inr <| Or.inr ⟨ by omega, by simpa only [ add_comm ] using this ⟩;
        · grind +qlia;
      convert Nat.le_of_not_lt fun h => ?_;
      grind +suggestions

/-
If Operation B applied to S produces S', then applying franklinMap to S' gives S back.
-/
lemma opA_reverses_opB {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) (hne : S.Nonempty)
    (hs_gt : S.min' hne > stairLen S hne) (hM : 2 * stairLen S hne < S.max' hne) :
    franklinMap ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})) = S := by
      -- Let's first show that the new set is nonempty.
      have hne' : ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).Nonempty := by
        exact ⟨ _, Finset.mem_union_right _ ( Finset.mem_union_right _ ( Finset.mem_singleton_self _ ) ) ⟩;
      -- Let's compute the min and max of the new set.
      have hmin : (S.erase (S.max' hne) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).min' hne' = stairLen S hne := by
        refine' le_antisymm _ _ <;> simp_all +decide [ Finset.min' ];
        exact ⟨ Nat.le_sub_of_add_le ( by linarith ), fun a ha₁ ha₂ => le_of_lt ( hs_gt a ha₂ ) ⟩
      have hmax : (S.erase (S.max' hne) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).max' hne' = S.max' hne - 1 := by
        refine' le_antisymm _ _;
        · refine' Finset.sup'_le _ _ _;
          grind +suggestions;
        · refine' Finset.le_max' _ _ _ ; simp_all +decide [ Finset.mem_union, Finset.mem_erase ];
          grind +suggestions;
      -- By definition of $franklinMap$, we know that if $s \leq \ell$ and $\neg(s = \ell \land S.card = \ell)$, then $franklinMap$ applies Operation A.
      have h_opA : franklinMap ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})) = ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).erase (stairLen S hne) \ {S.max' hne - 1 - stairLen S hne + 1} ∪ {S.max' hne} := by
        unfold franklinMap;
        have h_stairLen_ge : stairLen ((S.erase (S.max' hne)) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})) hne' ≥ stairLen S hne := by
          apply opB_result_stairLen_ge S hS hne hs_gt hM hne' hmax;
        have h_card_ge : (S.erase (S.max' hne) ∪ ({S.max' hne - stairLen S hne} ∪ {stairLen S hne})).card = S.card + 1 := by
          convert opB_card S hS hne hs_gt hM using 1;
        have h_card_ge : stairLen S hne ≤ S.card := by
          exact?;
        grind;
      simp_all +decide [ Finset.ext_iff ];
      grind +suggestions

/-
Franklin map is an involution on DistPartSet
-/
lemma franklinMap_invol {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) :
    franklinMap (franklinMap S) = S := by
      unfold franklinMap;
      nontriviality;
      split_ifs <;> simp_all +decide only [and_false];
      · nontriviality;
        split_ifs <;> simp_all +decide only [and_false];
        · convert opB_reverses_opA S hS ‹_› ( by tauto ) ( by tauto ) using 1;
          grind +locals;
        · convert opA_reverses_opB S hS ‹_› ( by tauto ) ( by tauto ) using 1;
          unfold franklinMap; simp +decide [ * ] ;
      · split_ifs at * <;> simp_all +decide [ Finset.Nonempty ]

/-
Franklin map maps DistPartSet to DistPartSet
-/
lemma franklinMap_mem {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) :
    franklinMap S ∈ DistPartSet n := by
      unfold franklinMap;
      grind +suggestions

/-
At non-fixed-points, signs cancel
-/
lemma franklinMap_sign_cancel {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n)
    (hfixed : franklinMap S ≠ S) :
    (-1 : ℤ) ^ S.card + (-1 : ℤ) ^ (franklinMap S).card = 0 := by
      nontriviality;
      unfold franklinMap at *;
      split_ifs at * <;> norm_num at *;
      split_ifs at * <;> simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
      · have := opA_card S ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ( hS.1 hx ) ), hS.2 ⟩ ) ‹_› ( by tauto ) ( by tauto ) ; simp_all +decide [ pow_succ' ] ;
        grind;
      · grind +suggestions

/-! ## Fixed point characterization -/

lemma staircase_type1_sum (k : ℕ) (hk : k ≥ 1) :
    (Finset.Icc k (2 * k - 1)).sum id = k * (3 * k - 1) / 2 := by
      -- We can prove this formula by induction on $k$.
      have h_sum_induction : ∀ k ≥ 1, ∑ i ∈ Finset.range k, (k + i) = k * (3 * k - 1) / 2 := by
        intro k hk; rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ] ; zify [ Finset.sum_add_distrib ] ; norm_num [ Finset.sum_range_id ] ; ring;
        exact Nat.recOn k ( by norm_num ) fun n ih => by cases n <;> norm_num [ Finset.sum_range_succ ] at * ; linarith;
      erw [ Finset.sum_Ico_eq_sum_range ];
      grind

lemma staircase_type2_sum (k : ℕ) (hk : k ≥ 1) :
    (Finset.Icc (k + 1) (2 * k)).sum id = k * (3 * k + 1) / 2 := by
      erw [ Finset.sum_Ico_eq_sum_range ];
      norm_num [ two_mul, add_assoc, add_tsub_assoc_of_le, Finset.sum_add_distrib ];
      exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( Nat.recOn k ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith ) )

lemma staircase_type1_card (k : ℕ) (hk : k ≥ 1) :
    (Finset.Icc k (2 * k - 1)).card = k := by
  simp +zetaDelta at *; omega

lemma staircase_type2_card (k : ℕ) (hk : k ≥ 1) :
    (Finset.Icc (k + 1) (2 * k)).card = k := by
  simp +arith +decide; rw [two_mul, Nat.add_sub_cancel]

/-
Fixed points are empty or staircase partitions
-/
lemma franklinMap_fixed_iff {n : ℕ} (S : Finset ℕ) (hS : S ∈ DistPartSet n) :
    franklinMap S = S ↔
    (S = ∅ ∨ ∃ k : ℕ, k ≥ 1 ∧
      (S = Finset.Icc k (2 * k - 1) ∨ S = Finset.Icc (k + 1) (2 * k))) := by
        constructor <;> intro h;
        · by_cases hne : S.Nonempty <;> simp_all +decide [ franklinMap ];
          split_ifs at h <;> simp_all +decide [ Finset.ext_iff ];
          · contrapose! h;
            use S.min' hne;
            simp +zetaDelta at *;
            exact Or.inr ⟨ ne_of_lt ( Nat.lt_succ_of_le ( Finset.le_max' _ _ ( Finset.min'_mem _ hne ) ) ), Finset.min'_mem _ hne ⟩;
          · contrapose! h;
            use stairLen S hne;
            grind;
          · -- If $s = \ell$ and $|S| = \ell$, then $S$ is a staircase partition of type 1.
            by_cases h_case1 : S.min' hne = stairLen S hne ∧ S.card = stairLen S hne;
            · have h_staircase : S = Finset.Icc (S.max' hne - stairLen S hne + 1) (S.max' hne) := by
                have h_staircase : ∀ j < stairLen S hne, S.max' hne - j ∈ S := by
                  grind +suggestions;
                refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
                · have h_card : Finset.card (Finset.image (fun j => S.max' hne - j) (Finset.range (stairLen S hne))) = stairLen S hne := by
                    rw [ Finset.card_image_of_injOn, Finset.card_range ] ; intro a ha b hb hab ; rw [ tsub_right_inj ] at * <;> linarith [ Finset.mem_range.mp ha, Finset.mem_range.mp hb, Finset.min'_le _ _ ( Finset.max'_mem _ hne ), Finset.le_max' _ _ ( Finset.min'_mem _ hne ) ];
                  have h_card : Finset.image (fun j => S.max' hne - j) (Finset.range (stairLen S hne)) = S := by
                    exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun j hj => h_staircase j ( Finset.mem_range.mp hj ) ) ( by aesop );
                  grind +suggestions;
                · simp +arith +decide [ h_case1 ];
                  exact fun x hx => by rw [ Nat.add_sub_of_le ( show stairLen S hne ≤ S.max' hne from by linarith [ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx ] ) ] ; exact Finset.le_max' _ _ hx;
              refine Or.inr ⟨ stairLen S hne, ?_, ?_ ⟩;
              · exact h_case1.1 ▸ Finset.min'_mem _ hne |> fun x => Finset.mem_Icc.mp ( hS.1 x ) |>.1;
              · grind +suggestions;
            · -- If $s > \ell$ and $M \leq 2\ell$, then $S$ is a staircase partition of type 2.
              have h_case2 : S.min' hne > stairLen S hne ∧ S.max' hne ≤ 2 * stairLen S hne := by
                have h_case2 : S.min' hne > stairLen S hne := by
                  grobner;
                exact ⟨ h_case2, by rename_i h; exact h ( fun y hy => by linarith [ Finset.min'_le _ _ hy ] ) _ ( Finset.max'_mem _ hne ) ⟩;
              -- If $s > \ell$ and $M \leq 2\ell$, then $S$ is a staircase partition of type 2 with $k = \ell$.
              have h_case2_type2 : S = Finset.Icc (stairLen S hne + 1) (2 * stairLen S hne) := by
                refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
                · grind +suggestions;
                · have h_card_ge : S.card ≥ Finset.card (Finset.image (fun j => S.max' hne - j) (Finset.range (stairLen S hne))) := by
                    refine Finset.card_le_card ?_;
                    exact Finset.image_subset_iff.mpr fun j hj => staircase_mem S hne j ( Finset.mem_range.mp hj );
                  rw [ Finset.card_image_of_injOn ] at h_card_ge;
                  · simp_all +decide [ two_mul ];
                  · exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ Finset.mem_range.mp hx, Finset.mem_range.mp hy, Finset.le_max' _ _ ( Finset.min'_mem _ hne ) ] ;
              refine Or.inr ⟨ stairLen S hne, ?_, ?_ ⟩;
              · exact stairLen_pos S hne;
              · grind;
        · rcases h with ( rfl | ⟨ k, hk, rfl | rfl ⟩ ) <;> simp +decide [ franklinMap ];
          · -- Let's simplify the goal using the fact that multiplication by a constant out of the set does not change the set.
            have h_stairLen : stairLen (Finset.Icc k (2 * k - 1)) (by
            exact ⟨ k, Finset.mem_Icc.mpr ⟨ le_rfl, Nat.le_sub_one_of_lt ( by linarith ) ⟩ ⟩) = k := by
              -- By definition of `stairLen`, we need to show that the length of the longest consecutive sequence starting from the maximum element in `Icc k (2 * k - 1)` is `k`.
              have h_stairLen_def : ∀ m ∈ Finset.Icc k (2 * k - 1), consecDown (Finset.Icc k (2 * k - 1)) m = m - k + 1 := by
                intro m hm; induction' m with m ih <;> simp_all +decide [ consecDown ] ;
                by_cases h : k ≤ m <;> simp_all +decide [ Nat.succ_sub ];
                · grind;
                · induction' m with m ih <;> simp_all +decide [ consecDown ];
                  linarith
              generalize_proofs at *;
              convert h_stairLen_def ( 2 * k - 1 ) ( Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ) using 1;
              · exact congr_arg _ ( le_antisymm ( Finset.max'_mem _ _ |> fun x => Finset.mem_Icc.mp x |>.2 ) ( Finset.le_max' _ _ <| by aesop ) );
              · omega
            generalize_proofs at *;
            grind +suggestions;
          · -- Let's simplify the goal using the definitions of `min'` and `max'`.
            have h_min_max : (Finset.Icc (k + 1) (2 * k)).min' (by
            exact Finset.nonempty_Icc.mpr ( by linarith )) = k + 1 ∧ (Finset.Icc (k + 1) (2 * k)).max' (by
            exact Finset.nonempty_Icc.mpr ( by linarith )) = 2 * k := by
              simp +decide [ Finset.min', Finset.max' ];
              simp +decide [ Finset.inf'_eq_csInf_image, Finset.sup'_eq_csSup_image ];
              exact ⟨ csInf_Icc ( by linarith ), csSup_Icc ( by linarith ) ⟩
            generalize_proofs at *;
            unfold stairLen;
            -- By definition of `consecDown`, we have `consecDown (Icc (k + 1) (2 * k)) (2 * k) = k`.
            have h_consecDown : ∀ m ∈ Finset.Icc (k + 1) (2 * k), consecDown (Finset.Icc (k + 1) (2 * k)) m = m - k := by
              intro m hm; induction' m using Nat.strong_induction_on with m ih; rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.mul_succ ] ;
              grind +locals;
            grind

/-! ## The Pentagonal Number Theorem (Combinatorial Form) -/

/-
The signed count equals the pentagonal coefficient.
-/
theorem pentagonal_combinatorial (n : ℕ) :
    signedDistinctPartitionCount n = pentagonalCoeff n := by
      -- By definition of pentagonalCoeff, we can write it as the sum of the signs of the fixed points of the Franklin map.
      have h_pentagonalCoeff : pentagonalCoeff n = (∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S = S), (-1 : ℤ) ^ S.card) := by
        -- By definition of $pentagonalCoeff$, we know that
        have h_pentagonalCoeff_def : pentagonalCoeff n = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if k * (3 * k - 1) / 2 = n then (-1 : ℤ) ^ k.natAbs else 0 := by
          refine' Finset.sum_congr rfl fun x hx => _ ;
          split_ifs <;> simp_all +decide [ generalizedPentagonal ];
          grind;
        -- By definition of $franklinMap$, we know that the fixed points are exactly the staircase partitions.
        have h_fixed_points : (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S = S) = if n = 0 then {∅} else (Finset.image (fun k : ℕ => Finset.Icc k (2 * k - 1)) (Finset.filter (fun k => k * (3 * k - 1) / 2 = n) (Finset.Icc 1 n))) ∪ (Finset.image (fun k : ℕ => Finset.Icc (k + 1) (2 * k)) (Finset.filter (fun k => k * (3 * k + 1) / 2 = n) (Finset.Icc 1 n))) := by
          ext S;
          split_ifs <;> simp_all +decide [ franklinMap_fixed_iff ];
          constructor <;> intro hS;
          · rcases franklinMap_fixed_iff S ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS.1, hS.2.1 ⟩ ) |>.1 hS.2.2 with ( rfl | ⟨ k, hk₁, rfl | rfl ⟩ ) <;> simp_all +decide;
            · refine Or.inl ⟨ k, ⟨ ⟨ hk₁, ?_ ⟩, ?_ ⟩, rfl ⟩;
              · linarith [ Finset.mem_Icc.mp ( hS.1 ( Finset.left_mem_Icc.mpr ( Nat.le_sub_one_of_lt ( by linarith ) ) ) ) ];
              · convert hS.2.1 using 1;
                convert staircase_type1_sum k hk₁ |> Eq.symm using 1;
            · refine Or.inr ⟨ k, ⟨ ⟨ hk₁, ?_ ⟩, ?_ ⟩, rfl ⟩;
              · linarith [ Finset.mem_Icc.mp ( hS.1 ( Finset.left_mem_Icc.mpr ( by linarith ) ) ) ];
              · convert hS.2.1 using 1;
                erw [ Finset.sum_Ico_eq_sum_range ];
                rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ] ; norm_num [ two_mul, add_assoc, Finset.sum_add_distrib ] ; ring;
                exact Nat.recOn k ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith;
          · rcases hS with ( ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl ⟩ | ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl ⟩ ) <;> simp_all +decide [ Finset.subset_iff ];
            · refine' ⟨ _, _, _ ⟩;
              · exact fun x hx₁ hx₂ => ⟨ by linarith, by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ 2 * a ), Nat.div_mul_cancel ( show 2 ∣ a * ( 3 * a - 1 ) from even_iff_two_dvd.mp ( by rcases a with ( _ | _ | a ) <;> simp +arith +decide [ mul_add, parity_simps ] ) ), Nat.sub_add_cancel ( by linarith : 1 ≤ 3 * a ) ] ⟩;
              · convert staircase_type1_sum a ha₁ using 1;
                exact ha₃.symm;
              · convert franklinMap_fixed_iff _ _ |>.2 _;
                exact n;
                · refine' Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr _, _ ⟩;
                  · exact Finset.Icc_subset_Icc ( by linarith ) ( by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ 3 * a ), Nat.sub_add_cancel ( by linarith : 1 ≤ 2 * a ), Nat.div_mul_cancel ( show 2 ∣ a * ( 3 * a - 1 ) from even_iff_two_dvd.mp ( by rcases a with ( _ | _ | a ) <;> simp +arith +decide [ mul_add, parity_simps ] ) ) ] );
                  · convert staircase_type1_sum a ha₁ using 1;
                    exact ha₃.symm;
                · exact Or.inr ⟨ a, ha₁, Or.inl rfl ⟩;
            · refine' ⟨ _, _, _ ⟩;
              · exact fun x hx₁ hx₂ => ⟨ by linarith, by nlinarith [ Nat.div_mul_cancel ( show 2 ∣ a * ( 3 * a + 1 ) from even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) ) ] ⟩;
              · convert staircase_type2_sum a ha₁ using 1;
                exact ha₃.symm;
              · rw [ franklinMap_fixed_iff ];
                exact Or.inr ⟨ a, ha₁, Or.inr rfl ⟩;
                refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
                rotate_right;
                exact n;
                · exact Finset.mem_powerset.mpr ( Finset.Icc_subset_Icc ( by linarith ) ( by nlinarith [ Nat.div_mul_cancel ( show 2 ∣ a * ( 3 * a + 1 ) from even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) ) ] ) );
                · convert staircase_type2_sum a ha₁ using 1;
                  exact ha₃.symm;
        rcases n with ( _ | n ) <;> simp_all +decide [ Finset.sum_ite ];
        rw [ Finset.sum_union ];
        · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num;
          · rw [ show ( Finset.filter ( fun x : ℤ => x * ( 3 * x - 1 ) / 2 = n + 1 ) ( Finset.Icc ( -1 + -↑n ) ( ↑n + 1 ) ) ) = Finset.image ( fun x : ℕ => x : ℕ → ℤ ) ( Finset.filter ( fun x : ℕ => x * ( 3 * x - 1 ) / 2 = n + 1 ) ( Finset.Icc 1 ( n + 1 ) ) ) ∪ Finset.image ( fun x : ℕ => -x : ℕ → ℤ ) ( Finset.filter ( fun x : ℕ => x * ( 3 * x + 1 ) / 2 = n + 1 ) ( Finset.Icc 1 ( n + 1 ) ) ) from ?_ ];
            · rw [ Finset.sum_union ] <;> norm_num [ Finset.sum_image ];
              · refine' congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun x hx => _ ) ( Finset.sum_congr rfl fun x hx => _ ) <;> norm_num [ two_mul, add_assoc ];
                cases x <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
              · norm_num [ Finset.disjoint_left ];
                intros; subst_vars; omega;
            · ext x;
              rcases x with ( x | x ) <;> simp_all +decide;
              · grind;
              · grind;
          · intro x hx y hy; simp_all +decide [ Finset.ext_iff ];
            intro h; have := h ( x + 1 ) ; have := h ( y + 1 ) ; norm_num at * ; omega;
          · intro x hx y hy; simp_all +decide [ Finset.ext_iff ] ;
            intro h; have := h x; have := h y; norm_num at *; omega;
        · norm_num [ Finset.disjoint_left ];
          rintro a x hx₁ hx₂ hx₃ rfl y hy₁ hy₂ hy₃; rcases x with ( _ | _ | x ) <;> rcases y with ( _ | _ | y ) <;> norm_num [ Nat.mul_succ ] at *;
          · norm_num [ show n = 1 by linarith ] at *;
            simp +decide [ hx₂ ];
          · rw [ Nat.div_eq_iff_eq_mul_left zero_lt_two ] at *;
            · nlinarith only [ hx₃, hy₃, show x = y by nlinarith only [ hx₃, hy₃ ] ];
            · norm_num [ ← even_iff_two_dvd, parity_simps ];
            · norm_num [ ← even_iff_two_dvd, parity_simps ];
      -- By definition of signedDistinctPartitionCount, we can write it as the sum of the signs of all partitions of n.
      have h_signedDistinctPartitionCount : signedDistinctPartitionCount n = (∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n), (-1 : ℤ) ^ S.card) := by
        rfl;
      -- By definition of franklinMap, we can pair each partition with its image under franklinMap.
      have h_pair : ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n), (-1 : ℤ) ^ S.card = ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S = S), (-1 : ℤ) ^ S.card + ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S ≠ S), (-1 : ℤ) ^ S.card := by
        rw [ ← Finset.sum_union ];
        · rcongr S ; by_cases h : franklinMap S = S <;> aesop;
        · exact Finset.disjoint_filter.mpr ( by aesop );
      have h_non_fixed_points_zero : ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S ≠ S), (-1 : ℤ) ^ S.card = ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S ≠ S), (-1 : ℤ) ^ (franklinMap S).card := by
        apply Finset.sum_bij (fun S hS => franklinMap S);
        · grind +suggestions;
        · simp +zetaDelta at *;
          intro a₁ ha₁ ha₁' ha₁'' a₂ ha₂ ha₂' ha₂'' h; have := franklinMap_invol a₁ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ha₁, ha₁' ⟩ ) ; have := franklinMap_invol a₂ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ha₂, ha₂' ⟩ ) ; aesop;
        · simp +zetaDelta at *;
          exact fun b hb₁ hb₂ hb₃ => ⟨ franklinMap b, ⟨ by
            have := franklinMap_mem b ( show b ∈ DistPartSet n from by
                                          exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hb₁, hb₂ ⟩ ) ; aesop;, by
            convert franklinMap_mem b _ |> fun h => Finset.mem_filter.mp h |>.2 using 1;
            exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hb₁, hb₂ ⟩, by
            rw [ franklinMap_invol ] ; tauto;
            exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hb₁, hb₂ ⟩ ⟩, by
            apply franklinMap_invol;
            exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hb₁, hb₂ ⟩ ⟩;
        · simp +contextual [ franklinMap_invol ];
          exact fun S hS₁ hS₂ hS₃ => by rw [ franklinMap_invol S ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS₁, hS₂ ⟩ ) ] ;
      have h_non_fixed_points_zero : ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S ≠ S), (-1 : ℤ) ^ S.card + ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ franklinMap S ≠ S), (-1 : ℤ) ^ (franklinMap S).card = 0 := by
        rw [ ← Finset.sum_add_distrib ];
        refine' Finset.sum_eq_zero fun x hx => _;
        grind +suggestions;
      linarith

end