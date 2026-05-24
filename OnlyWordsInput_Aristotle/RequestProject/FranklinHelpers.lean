import Mathlib

/-!
# Helper lemmas for Franklin's involution

We prove detailed properties of the `topRun` function and the set operations
used in Franklin's involution.
-/

open Finset BigOperators

/-! ## topRun definition and basic properties -/

/-- The topRun of a finset: length of maximal consecutive run ing at the maximum. -/
def topRun (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then
    let M := S.max' h
    Nat.find (show ∃ j, M - j ∉ S ∨ j ≥ M + 1 from ⟨M + 1, Or.inr le_rfl⟩)
  else 0

theorem topRun_def {S : Finset ℕ} (h : S.Nonempty) :
    topRun S = Nat.find (show ∃ j, S.max' h - j ∉ S ∨ j ≥ S.max' h + 1
      from ⟨S.max' h + 1, Or.inr le_rfl⟩) := by
  simp [topRun, h]

/-
For `j < topRun S`, `max - j ∈ S`.
-/
theorem topRun_mem {S : Finset ℕ} (h : S.Nonempty) {j : ℕ} (hj : j < topRun S) :
    S.max' h - j ∈ S := by
  by_contra h_0; simp_all +decide [ topRun_def ] ;

/-
`topRun S > 0` for nonempty `S` (since `max ∈ S`).
-/
theorem topRun_pos {S : Finset ℕ} (h : S.Nonempty) : 0 < topRun S := by
  rcases k : topRun S with ( _ | k ) <;> simp +decide [ * ];
  exact absurd k <| Nat.ne_of_gt <| topRun_def h ▸ Nat.pos_of_ne_zero ( by have := Finset.max'_mem S h; aesop )

/-
`topRun S ≤ S.card` for any finset.
-/
theorem topRun_le_card {S : Finset ℕ} (h : S.Nonempty) : topRun S ≤ S.card := by
  -- By definition of `topRun`, we know that there are `topRun S` consecutive elements in `S` ending at `S.max' h`.
  have h_consecutive : Finset.image (fun j => S.max' h - j) (Finset.range (topRun S)) ⊆ S := by
    exact Finset.image_subset_iff.mpr fun j hj => topRun_mem h <| Finset.mem_range.mp hj;
  convert Finset.card_le_card h_consecutive using 1;
  rw [ Finset.card_image_of_injOn fun x hx y hy hxy => _, Finset.card_range ];
  simp +zetaDelta at *;
  intro x hx y hy hxy; rw [ tsub_right_inj ] at hxy <;> try linarith [ Finset.le_max' _ _ ( h_consecutive ( Finset.mem_image_of_mem _ ( Finset.mem_range.mpr hx ) ) ), Finset.le_max' _ _ ( h_consecutive ( Finset.mem_image_of_mem _ ( Finset.mem_range.mpr hy ) ) ) ] ;
  · contrapose! hx;
    exact le_trans ( show topRun S ≤ S.max' h + 1 from by
                      rw [ topRun_def ];
                      exact Nat.find_min' _ ( Or.inr le_rfl );
                      assumption ) ( by linarith );
  · contrapose! hy;
    unfold topRun; aesop;

/-
`max - topRun S ∉ S` (when topRun < max + 1).
-/
theorem topRun_not_mem {S : Finset ℕ} (h : S.Nonempty)
    (htr : topRun S ≤ S.max' h) :
    S.max' h - topRun S ∉ S := by
  grind +locals

/-
The top block `{max, max-1, ..., max-k+1}` for `k ≤ topRun S` is a subset of `S`.
-/
theorem topBlock_subset {S : Finset ℕ} (h : S.Nonempty) {k : ℕ} (hk : k ≤ topRun S) :
    (Finset.range k).image (fun i => S.max' h - i) ⊆ S := by
  exact Finset.image_subset_iff.mpr fun i hi => topRun_mem h <| by linarith [ Finset.mem_range.mp hi ] ;

/-
The top block has cardinality `k` when `k ≤ max + 1`.
-/
theorem topBlock_card {M : ℕ} {k : ℕ} (hk : k ≤ M + 1) :
    ((Finset.range k).image (fun i => M - i)).card = k := by
  rw [ Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
  exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ Set.mem_Iio.mp hx, Set.mem_Iio.mp hy ] ;

/- The topBlock_subset_Icc lemma was removed (incorrect for ℕ subtraction edge cases) -/

/-! ## Properties of operation A -/

/-
When operation A conditions hold (σ ≤ s, σ < s or σ < card),
the minimum σ is NOT in the top block of size σ.
-/
theorem sigma_not_in_topBlock {S : Finset ℕ} (h : S.Nonempty)
    (hcond : S.min' h ≤ topRun S ∧ (S.min' h < topRun S ∨ S.min' h < S.card)) :
    S.min' h ∉ (Finset.range (S.min' h)).image (fun i => S.max' h - i) := by
  -- By definition of $topRun$, we know that $M - topRun S \notin S$ (since $topRun S \leq M$).
  by_cases h_gt : S.max' h ≥ 2 * S.min' h;
  · grind;
  · -- Since $S.min' h < S.max' h$, we have $S.max' h = S.min' h + k$ for some $k < S.min' h$.
    obtain ⟨k, hk⟩ : ∃ k, S.max' h = S.min' h + k ∧ k < S.min' h := by
      exact ⟨ S.max' h - S.min' h, by rw [ Nat.add_sub_cancel' ( Finset.min'_le _ _ ( Finset.max'_mem _ h ) ) ], by rw [ tsub_lt_iff_left ( Finset.min'_le _ _ ( Finset.max'_mem _ h ) ) ] ; linarith ⟩;
    -- Since $S.max' h = S.min' h + k$, we have $topRun S \leq k + 1$.
    have h_topRun_le : topRun S ≤ k + 1 := by
      have h_topRun_le : S.max' h - (k + 1) ∉ S := by
        exact fun h => by have := Finset.min'_le _ _ h; omega;
      unfold topRun at *; aesop;
    -- Since $S$ has more than $k + 1$ elements, there must be at least one element in $S$ that is not in the top block.
    have h_card_gt : S.card > k + 1 := by
      grind +splitImp;
    -- Since $S$ has more than $k + 1$ elements, there must be at least one element in $S$ that is not in the top block. Let's denote this element by $x$.
    obtain ⟨x, hx⟩ : ∃ x ∈ S, x < S.min' h + k - k := by
      contrapose! h_card_gt;
      exact le_trans ( Finset.card_le_card ( show S ⊆ Finset.Icc ( S.min' h ) ( S.max' h ) from fun x hx => Finset.mem_Icc.mpr ⟨ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx ⟩ ) ) ( by simp +arith +decide [ hk ] );
    exact absurd hx.2 ( by rw [ Nat.add_sub_cancel ] ; exact not_lt_of_ge ( Finset.min'_le _ _ hx.1 ) )

/-
The shifted top block is disjoint from `S \ topBlock \ {σ}` (in operation A).
-/
theorem shifted_disjoint_A {S : Finset ℕ} (h : S.Nonempty)
    (hcond : S.min' h ≤ topRun S ∧ (S.min' h < topRun S ∨ S.min' h < S.card)) :
    Disjoint
      ((S \ (Finset.range (S.min' h)).image (fun i => S.max' h - i)) \ {S.min' h})
      (((Finset.range (S.min' h)).image (fun i => S.max' h - i)).image (· + 1)) := by
  rw [ Finset.disjoint_left ] ; norm_num;
  intro a ha₁ ha₂ ha₃ x hx hx₂;
  contrapose! ha₂;
  refine' ⟨ x - 1, _, _ ⟩ <;> rcases x with ( _ | x ) <;> simp_all +decide [ Nat.sub_sub ];
  · exact fun y hy => Nat.lt_of_succ_lt ( hx y hy );
  · linarith [ Finset.le_max' _ _ ha₁ ];
  · grind

/-
Card of operation A result is `card - 1`.
-/
theorem card_operationA {S : Finset ℕ} (h : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcond : S.min' h ≤ topRun S ∧ (S.min' h < topRun S ∨ S.min' h < S.card)) :
    (((S \ (Finset.range (S.min' h)).image (fun i => S.max' h - i)) \ {S.min' h}) ∪
      ((Finset.range (S.min' h)).image (fun i => S.max' h - i)).image (· + 1)).card =
    S.card - 1 := by
  rw [ Finset.card_union_of_disjoint ];
  · rw [ Finset.card_sdiff, Finset.card_image_of_injective _ Nat.succ_injective, Finset.card_sdiff ];
    grind +suggestions;
  · convert shifted_disjoint_A h hcond using 1

/-
Sum of operation A result equals sum of S.
-/
theorem sum_operationA {S : Finset ℕ} (h : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcond : S.min' h ≤ topRun S ∧ (S.min' h < topRun S ∨ S.min' h < S.card)) :
    (((S \ (Finset.range (S.min' h)).image (fun i => S.max' h - i)) \ {S.min' h}) ∪
      ((Finset.range (S.min' h)).image (fun i => S.max' h - i)).image (· + 1)).sum id =
    S.sum id := by
  rw [ Finset.sum_union ];
  · -- The sum of the shifted top block is equal to the sum of the original top block plus the cardinality of the top block.
    have h_shifted_sum : ∑ x ∈ (Finset.range (S.min' h)).image (fun i => S.max' h - i), (x + 1) = ∑ x ∈ (Finset.range (S.min' h)).image (fun i => S.max' h - i), x + (Finset.range (S.min' h)).card := by
      rw [ Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_image_of_injOn ];
      exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ Finset.mem_range.mp hx, Finset.mem_range.mp hy, Finset.min'_le _ _ ( Finset.max'_mem _ h ), Finset.le_max' _ _ ( Finset.min'_mem _ h ) ] ;
    simp_all +decide [ Finset.sum_sdiff, Finset.subset_iff ];
    rw [ ← Finset.sum_sdiff ( show ( Finset.image ( fun i => S.max' h - i ) ( Finset.range ( S.min' h ) ) ) ⊆ S from ?_ ) ];
    · rw [ Finset.sum_eq_sum_diff_singleton_add ( show S.min' h ∈ S \ image ( fun i => S.max' h - i ) ( range ( S.min' h ) ) from ?_ ) ] ; ring!;
      grind +suggestions;
    · exact topBlock_subset h ( by linarith );
  · convert shifted_disjoint_A h hcond using 1

/-! ## Properties of operation B -/

/-
Card of operation B result is `card + 1`.
-/
theorem card_operationB {S : Finset ℕ} (h : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcondB : S.min' h > topRun S ∧ S.max' h ≠ 2 * topRun S) :
    (((S \ (Finset.range (topRun S)).image (fun i => S.max' h - i)) ∪
      ((Finset.range (topRun S)).image (fun i => S.max' h - i)).image (· - 1)) ∪
      {topRun S}).card =
    S.card + 1 := by
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ];
  · rw [ Finset.card_sdiff ];
    rw [ show image ( fun i => S.max' h - i ) ( range ( topRun S ) ) ∩ S = image ( fun i => S.max' h - i ) ( range ( topRun S ) ) from ?_, show image ( fun x => x - 1 ) ( image ( fun i => S.max' h - i ) ( range ( topRun S ) ) ) = image ( fun i => S.max' h - i - 1 ) ( range ( topRun S ) ) from ?_ ];
    · rw [ Finset.card_image_of_injOn, Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
      · rw [ Nat.sub_add_cancel ( topRun_le_card h ) ];
      · intros i hi j hj hij;
        norm_num +zetaDelta at *;
        rw [ tsub_tsub, tsub_tsub, tsub_right_inj ] at hij <;> linarith [ hcondB.1 _ ( Finset.max'_mem S h ), topRun_le_card h ];
      · exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ hx.out, hy.out, Finset.le_max' _ _ ( Finset.min'_mem S h ), topRun_le_card h ] ;
    · simp +decide [ Finset.ext_iff ];
    · exact Finset.inter_eq_left.mpr ( topBlock_subset h ( by linarith ) );
  · simp +contextual [ Finset.disjoint_right ];
    grind +locals;
  · simp +zetaDelta at *;
    grind +suggestions

/-
General characterization of topRun: if the first k elements from the top are in S
and the (k+1)-th is not, then topRun S = k.
-/
theorem topRun_eq_of {S : Finset ℕ} (hne : S.Nonempty) (k : ℕ)
    (hk_le : k ≤ S.max' hne)
    (h_mem : ∀ j, j < k → S.max' hne - j ∈ S)
    (h_not : S.max' hne - k ∉ S) :
    topRun S = k := by
      convert Nat.find_eq_iff ?_ |>.2 ?_;
      convert topRun_def hne;
      grind

/-
Sum of operation B result equals sum of S.
-/
theorem sum_operationB {S : Finset ℕ} (h : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcondB : S.min' h > topRun S ∧ S.max' h ≠ 2 * topRun S) :
    (((S \ (Finset.range (topRun S)).image (fun i => S.max' h - i)) ∪
      ((Finset.range (topRun S)).image (fun i => S.max' h - i)).image (· - 1)) ∪
      {topRun S}).sum id =
    S.sum id := by
  rw [ Finset.sum_union, Finset.sum_union ];
  · rw [ Finset.sum_image ];
    · rw [ ← Finset.sum_sdiff ( show ( Finset.image ( fun i => S.max' h - i ) ( Finset.range ( topRun S ) ) ) ⊆ S from ?_ ) ];
      · simp +arith +decide [ Finset.sum_image, Finset.sum_range_succ' ];
        rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num;
        · zify [ Finset.sum_add_distrib ];
          rw [ Finset.sum_congr rfl fun x hx => by rw [ Nat.sub_sub, Nat.cast_sub <| show x + 1 ≤ S.max' h from by linarith [ Finset.mem_range.mp hx, show topRun S ≤ S.max' h from by
                                                                                                                                                        have := Finset.min'_le _ _ ( Finset.max'_mem _ h ) ; linarith; ] ] ] ; norm_num [ Finset.sum_add_distrib ];
          rw [ Finset.sum_congr rfl fun x hx => Nat.cast_sub <| show x ≤ S.max' h from by linarith [ Finset.mem_range.mp hx, show topRun S ≤ S.max' h from by
                                                                                                                              have := Finset.min'_le _ _ ( Finset.max'_mem _ h ) ; linarith; ] ] ; norm_num [ Finset.sum_add_distrib ] ; ring;
        · exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ hx.out, hy.out, Finset.le_max' _ _ ( Finset.min'_mem S h ), topRun_le_card h ] ;
        · exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ hx.out, hy.out, Finset.le_max' _ _ ( Finset.min'_mem S h ), topRun_le_card h ] ;
      · exact topBlock_subset h ( le_refl _ );
    · intro x hx y hy; rcases x with ( _ | x ) <;> rcases y with ( _ | y ) <;> simp_all +decide ;
      · obtain ⟨ x, hx₁, hx₂ ⟩ := hx; rw [ Nat.sub_eq_iff_eq_add ] at hx₂ <;> linarith [ hcondB.1 _ ( Finset.max'_mem S h ), topRun_le_card h ] ;
      · exact absurd hy ( by rintro ⟨ k, hk₁, hk₂ ⟩ ; exact absurd hk₂ ( Nat.sub_ne_zero_of_lt ( lt_of_lt_of_le hk₁ ( le_trans ( Nat.le_of_lt ( hcondB.1 _ ( Finset.max'_mem _ h ) ) ) ( Nat.le_refl _ ) ) ) ) );
  · simp +contextual [ Finset.disjoint_right ];
    grind +locals;
  · simp +decide [ Finset.disjoint_singleton_right ];
    grind +suggestions
