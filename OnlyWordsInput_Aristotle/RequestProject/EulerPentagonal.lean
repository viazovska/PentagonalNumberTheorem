import Mathlib
import RequestProject.FranklinHelpers

/-!
# Euler's Pentagonal Number Theorem

We prove Euler's pentagonal number theorem:
$$\prod_{n=1}^{\infty} (1 - x^n) = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k-1)/2}$$

## Proof structure

The proof has three main parts:
1. **Product expansion**: Show that the coefficient of `x^n` in the truncated Euler product
   `∏_{i=1}^{N} (1 - x^i)` (for `N > n`) equals the alternating sum over strict
   partitions of `n`.
2. **Franklin's involution**: Define an involution on strict partitions that cancels
   non-fixed-point contributions.
3. **Fixed-point analysis**: Show the fixed points of the involution are exactly the
   generalized pentagonal partitions, and their contributions sum to `pentagonalCoeff n`.
-/

open Finset BigOperators

noncomputable section

/-! ## Definitions -/

/-- The coefficient of `x^n` in the pentagonal series
`∑_{k ∈ ℤ} (-1)^k x^{k(3k-1)/2}`. -/
def pentagonalCoeff (n : ℕ) : ℤ :=
  (Finset.Icc (-(n : ℤ)) n).sum fun k =>
    if 2 * (n : ℤ) = k * (3 * k - 1) then (-1) ^ k.natAbs else 0

/-- The Euler product truncated at `N`:
`∏_{i=1}^{N} (1 - x^i)` as a formal power series over `ℤ`. -/
def eulerProd (N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))

/-- The set of strict partitions of `n`: finsets of positive naturals summing to `n`,
with all parts at most `n`. -/
def StrictPartitions (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range (n + 1)).powerset).filter
    (fun S => (∀ x ∈ S, 0 < x) ∧ S.sum id = n)

/-! ## Part I: Coefficient equals alternating sum over strict partitions -/

/-- Product of negated power series monomials. -/
theorem prod_neg_X_pow (T : Finset ℕ) :
    (∏ i ∈ T, (-(PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) =
      (-1) ^ T.card * (PowerSeries.X : PowerSeries ℤ) ^ (T.sum fun i => i + 1) := by
  convert Finset.prod_congr rfl fun i hi => neg_eq_neg_one_mul ( PowerSeries.X ^ ( i + 1 ) ) using 1 ; rw [ Finset.prod_mul_distrib ] ; norm_num [ Finset.prod_pow_eq_pow_sum ]

/-- Coefficient of `x^n` in the expanded Euler product. -/
theorem coeff_eulerProd_eq_sum_range (N n : ℕ) :
    (PowerSeries.coeff (R := ℤ) n) (eulerProd N) =
      ((Finset.range N).powerset.filter (fun T => (T.sum fun i => i + 1) = n)).sum
        (fun T => (-1 : ℤ) ^ T.card) := by
  have h_expand : eulerProd N = ∑ T ∈ (Finset.range N).powerset, (-1 : PowerSeries ℤ) ^ T.card * (PowerSeries.X : PowerSeries ℤ) ^ (T.sum fun i => i + 1) := by
    unfold eulerProd;
    simp +decide [ sub_eq_neg_add, Finset.prod_add, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum ];
    exact Finset.sum_congr rfl fun T hT => by rw [ Finset.prod_congr rfl fun _ _ => neg_eq_neg_one_mul _, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_eq_sum_ones ] ; rw [ Finset.prod_pow_eq_pow_sum ] ;
  simp +decide [ h_expand, PowerSeries.coeff_X_pow ];
  rw [ Finset.sum_filter ] ; refine' Finset.sum_congr rfl fun T hT => _ ; by_cases h : ∑ i ∈ T, ( i + 1 ) = n <;> simp_all +decide [ PowerSeries.coeff_X_pow ] ;
  · by_cases h : Even T.card <;> simp_all +decide [ PowerSeries.coeff_mul, PowerSeries.coeff_X_pow ];
  · by_cases h' : Even T.card <;> simp_all +decide [ PowerSeries.coeff_mul, PowerSeries.coeff_X_pow ];
    · tauto;
    · grind +splitImp

/-- For `N > n`, the coefficient equals the alternating sum over strict partitions. -/
theorem coeff_eulerProd_eq_sum (n N : ℕ) (hN : n < N) :
    (PowerSeries.coeff (R := ℤ) n) (eulerProd N) =
      (StrictPartitions n).sum (fun S => (-1 : ℤ) ^ S.card) := by
  suffices h_bij : ∀ N, N > n → (Finset.powerset (Finset.range N)).filter (fun T => T.sum (fun i => i + 1) = n) = Finset.image (fun T => T.image (fun i => i - 1)) (StrictPartitions n) by
    rw [ coeff_eulerProd_eq_sum_range, h_bij N hN, Finset.sum_image ];
    · refine' Finset.sum_congr rfl fun x hx => _;
      rw [ Finset.card_image_of_injOn ];
      exact fun a ha b hb hab => by linarith [ Nat.sub_add_cancel ( show 1 ≤ a from by have := Finset.mem_filter.mp hx; exact this.2.1 a ha ), Nat.sub_add_cancel ( show 1 ≤ b from by have := Finset.mem_filter.mp hx; exact this.2.1 b hb ) ] ;
    · intro T hT T' hT' h_eq; ext x; simp_all +decide [ Finset.ext_iff ] ;
      constructor <;> intro hx <;> specialize h_eq ( x - 1 ) <;> rcases x with ( _ | x ) <;> simp_all +decide [ StrictPartitions ];
      · linarith [ hT.2.1 0 hx ];
      · exact h_eq.mp ⟨ _, hx, rfl ⟩ |> fun ⟨ y, hy, hy' ⟩ => by convert hy using 1; linarith [ Nat.sub_add_cancel ( hT'.2.1 y hy ) ] ;
      · linarith [ hT'.2.1 0 hx ];
      · grind +extAll;
  intro N hN; ext; simp +decide [ StrictPartitions ] ; simp_all +decide [ StrictPartitions ] ;
  constructor <;> intro h;
  · refine' ⟨ Finset.image ( fun i => i + 1 ) ‹_›, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact fun x hx => lt_of_lt_of_le ( Nat.lt_succ_self x ) ( h.2 ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le ( x + 1 ) ) hx );
    · ext; aesop;
  · rcases h with ⟨ a, ⟨ ha₁, ha₂, ha₃ ⟩, rfl ⟩ ; refine' ⟨ _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ] ;
    · exact fun x hx => lt_of_le_of_lt ( Nat.sub_le _ _ ) ( lt_of_le_of_lt ( ha₁ hx ) hN );
    · rw [ Finset.sum_image ];
      · rwa [ Finset.sum_congr rfl fun x hx => Nat.sub_add_cancel ( ha₂ x hx ) ];
      · exact fun x hx y hy hxy => by linarith [ Nat.sub_add_cancel ( ha₂ x hx ), Nat.sub_add_cancel ( ha₂ y hy ) ] ;

/-! ## Part II: Franklin's involution -/

/-- Franklin's involution on finite sets of positive integers.
Given `S`, let `σ = min(S)`, `s = topRun(S)`, `M = max(S)`.
- If `σ ≤ s` and (`σ < s` or `σ < |S|`): **Operation A** — remove smallest,
  shift top `σ` elements up by 1.
- If `σ > s` and `M ≠ 2s`: **Operation B** — shift top `s` elements down by 1,
  add new element `s`.
- Otherwise: **Fixed point** — return `S` unchanged. -/
def franklinInv (S : Finset ℕ) : Finset ℕ :=
  if h : S.Nonempty then
    let σ := S.min' h
    let s := topRun S
    let M := S.max' h
    if σ ≤ s ∧ (σ < s ∨ σ < S.card) then
      let topBlock := (Finset.range σ).image (fun i => M - i)
      let shifted := topBlock.image (· + 1)
      ((S \ topBlock) \ {σ}) ∪ shifted
    else if σ > s ∧ M ≠ 2 * s then
      let topBlock := (Finset.range s).image (fun i => M - i)
      let shifted := topBlock.image (· - 1)
      ((S \ topBlock) ∪ shifted) ∪ {s}
    else
      S
  else
    S

/-- For non-fixed points, Franklin's involution changes the cardinality by ±1,
hence flips the sign contribution. -/
theorem franklinInv_sign {S : Finset ℕ} (hpos : ∀ x ∈ S, 0 < x)
    (hne : franklinInv S ≠ S) :
    (-1 : ℤ) ^ (franklinInv S).card + (-1 : ℤ) ^ S.card = 0 := by
  by_cases hσ : S.Nonempty <;> simp_all +decide [ franklinInv ];
  split_ifs at * <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
  · rw [ card_operationA hσ hpos ‹_› ];
    rcases n : S.card with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
    grind +splitIndPred;
  · have h_card : Finset.card (insert (topRun S) (S \ (Finset.range (topRun S)).image (fun i => S.max' hσ - i) ∪ ((Finset.range (topRun S)).image (fun i => S.max' hσ - i)).image (· - 1))) = Finset.card S + 1 := by
      convert card_operationB hσ hpos _ using 1;
      · grind;
      · exact ⟨ by linarith [ Finset.min'_mem S hσ, ‹ ( ∀ y ∈ S, topRun S < y ) ∧ ¬S.max' hσ = 2 * topRun S ›.1 _ ( Finset.min'_mem S hσ ) ], by tauto ⟩;
    rw [ h_card, pow_succ' ] ; ring

set_option maxHeartbeats 800000 in
/-- Franklin's involution maps strict partitions to strict partitions. -/
theorem franklinInv_mem {n : ℕ} {S : Finset ℕ} (hS : S ∈ StrictPartitions n) :
    franklinInv S ∈ StrictPartitions n := by
  have hsum : franklinInv S ∈ StrictPartitions n := by
    have hsum : franklinInv S = S ∨ (franklinInv S).sum id = S.sum id ∧ (∀ x ∈ franklinInv S, 0 < x) := by
      by_cases h : S.Nonempty <;> simp_all +decide [ StrictPartitions ];
      by_cases hcond : S.min' h ≤ topRun S ∧ (S.min' h < topRun S ∨ S.min' h < S.card);
      · convert sum_operationA h hS.2.1 hcond using 1;
        unfold franklinInv; aesop;
      · by_cases hcondB : S.min' h > topRun S ∧ S.max' h ≠ 2 * topRun S;
        · have hsum : (franklinInv S).sum id = S.sum id := by
            convert sum_operationB h hS.2.1 hcondB using 1;
            grind +locals;
          refine Or.inr ⟨ hsum.trans hS.2.2, ?_ ⟩;
          unfold franklinInv; simp_all +decide [ Finset.subset_iff ] ;
          split_ifs <;> simp_all +decide [ Finset.subset_iff ];
          · grind;
          · refine' ⟨ _, _ ⟩;
            · exact topRun_pos h;
            · rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ k, hk₁, rfl ⟩ ) <;> [ exact hS.2.1 _ ha₁; exact Nat.sub_pos_of_lt ( Nat.lt_sub_of_add_lt ( by linarith [ hcondB.1 _ ( Finset.max'_mem _ h ), Nat.sub_add_cancel ( show k ≤ S.max' h from le_trans ( Nat.le_of_lt hk₁ ) ( by linarith [ hcondB.1 _ ( Finset.max'_mem _ h ) ] ) ) ] ) ) ];
        · grind +locals
    unfold StrictPartitions at *; simp_all +decide [ Finset.subset_iff ] ;
    cases hsum <;> simp_all +decide [ Finset.sum_eq_zero_iff ];
    exact fun x hx => le_trans ( Finset.single_le_sum ( fun a _ => Nat.zero_le a ) hx ) ( by linarith );
  assumption

/-! ### Helper lemmas for the involution proof -/

/-- franklinInv preserves nonemptiness for sets of positive naturals. -/
theorem franklinInv_nonempty {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x) :
    (franklinInv S).Nonempty := by
  unfold franklinInv; simp only [dif_pos hne]
  split_ifs with h1 h2
  · -- Op A: shifted block contains M+1
    have hmin_pos : 0 < S.min' hne := hpos _ (Finset.min'_mem _ _)
    exact ⟨S.max' hne + 1, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨S.max' hne, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hmin_pos, by omega⟩, rfl⟩))⟩
  · -- Op B: contains {topRun S}
    exact ⟨topRun S, Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
  · -- Fixed point
    exact hne

/-- When op A conditions hold, franklinInv S equals the op A expression. -/
theorem franklinInv_eq_opA {S : Finset ℕ} (hne : S.Nonempty)
    (h : S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card)) :
    franklinInv S = ((S \ (Finset.range (S.min' hne)).image (fun i => S.max' hne - i)) \
      {S.min' hne}) ∪
      ((Finset.range (S.min' hne)).image (fun i => S.max' hne - i)).image (· + 1) := by
  simp only [franklinInv, dif_pos hne]
  split_ifs with h1
  · rfl
  · exact absurd h h1

/-- When op B conditions hold, franklinInv S equals the op B expression. -/
theorem franklinInv_eq_opB {S : Finset ℕ} (hne : S.Nonempty)
    (h : S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S) :
    franklinInv S = ((S \ (Finset.range (topRun S)).image (fun i => S.max' hne - i)) ∪
      ((Finset.range (topRun S)).image (fun i => S.max' hne - i)).image (· - 1)) ∪ {topRun S} := by
  simp only [franklinInv, dif_pos hne]
  split_ifs with h1
  · exfalso; omega
  · simp_all


set_option maxHeartbeats 800000 in
/-- After op A, max of the result = M + 1. -/
theorem opA_max {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcond : S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card))
    (hne' : (franklinInv S).Nonempty) :
    (franklinInv S).max' hne' = S.max' hne + 1 := by
      refine' le_antisymm _ _ <;> simp_all +decide [ franklinInv ];
      · rintro y ( ⟨ ⟨ hy₁, hy₂ ⟩, hy₃ ⟩ | ⟨ a, ha₁, rfl ⟩ ) <;> [ exact Nat.le_succ_of_le ( Finset.le_max' _ _ hy₁ ) ; exact Nat.succ_le_succ ( Nat.sub_le _ _ ) ];
      · simp_all +decide [ Finset.max' ];
        intro y hy; use ( Finset.sup' S hne fun x => x ) - 0 + 1; simp_all +decide [ Finset.le_sup' ] ;
        exact ⟨ Or.inr ⟨ 0, fun x hx => Nat.zero_lt_of_lt ( hpos x hx ), Nat.sub_zero _ ⟩, ⟨ Finset.max' S hne, Finset.max'_mem _ _, Finset.le_max' _ _ hy ⟩ ⟩

set_option maxHeartbeats 800000 in
/-- After op A, all elements are > σ. -/
theorem opA_all_gt {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcond : S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card)) :
    ∀ x ∈ franklinInv S, S.min' hne < x := by
      intro x hx;
      by_cases hx' : x ∈ (S \ (Finset.range (S.min' hne)).image (fun i => S.max' hne - i)) \ {S.min' hne};
      · simp +zetaDelta at *;
        exact lt_of_le_of_ne ( Finset.min'_le _ _ hx'.1.1 ) ( Ne.symm hx'.2 );
      · -- Since $x$ is in the shifted top block, we have $x = y + 1$ for some $y \in T$.
        obtain ⟨y, hyT, rfl⟩ : ∃ y ∈ (Finset.range (S.min' hne)).image (fun i => S.max' hne - i), x = y + 1 := by
          grind +locals;
        -- Since $y$ is in the top block, we have $y \geq S.max' hne - (S.min' hne - 1)$.
        have hy_ge : y ≥ S.max' hne - (S.min' hne - 1) := by
          grind;
        have h_max_ge_min : S.max' hne ≥ 2 * S.min' hne := by
          contrapose! hcond;
          intro h;
          have h_topRun_le_min : topRun S ≤ S.max' hne - S.min' hne + 1 := by
            have h_topRun_le_min : S.max' hne - (S.max' hne - S.min' hne + 1) ∉ S := by
              grind +suggestions;
            unfold topRun;
            split_ifs ; simp_all +decide [ Nat.find_eq_iff ];
            exact ⟨ S.max' hne - S.min' hne + 1, le_rfl, Or.inl h_topRun_le_min ⟩;
          have h_card_le_min : S.card ≤ S.max' hne - S.min' hne + 1 := by
            have h_card_le_min : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
              exact fun x hx => Finset.mem_Icc.mpr ⟨ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx ⟩;
            exact le_trans ( Finset.card_le_card h_card_le_min ) ( by simp +arith +decide [ Nat.sub_add_comm ( show S.min' hne ≤ S.max' hne from Finset.min'_le _ _ ( Finset.max'_mem _ hne ) ) ] );
          omega;
        grind

set_option maxHeartbeats 800000 in
/-- After op A, topRun of the result = σ. -/
theorem opA_topRun {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcond : S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card)) :
    topRun (franklinInv S) = S.min' hne := by
      -- Let's unfold the definition of `franklinInv` to analyze the resulting set.
      have hfranklinInv_def : franklinInv S = ((S \ (Finset.range (S.min' hne)).image (fun i => S.max' hne - i)) \ {S.min' hne}) ∪ ((Finset.range (S.min' hne)).image (fun i => S.max' hne - i)).image (· + 1) := by
        unfold franklinInv; aesop;
      -- Let's denote the new set as `S'`.
      set S' := franklinInv S with hS';
      -- By definition of `S'`, we know that `S'` is nonempty and its maximum element is `S.max' hne + 1`.
      have hS'_nonempty : S'.Nonempty := by
        simp_all +decide [ Finset.ext_iff ];
        exact ⟨ _, hS' _ |>.2 <| Or.inr ⟨ 0, fun y hy => Nat.pos_of_ne_zero <| by linarith [ hpos y hy ], rfl ⟩ ⟩
      have hS'_max : S'.max' hS'_nonempty = S.max' hne + 1 := by
        apply opA_max hne hpos hcond hS'_nonempty;
      apply topRun_eq_of hS'_nonempty (S.min' hne);
      · exact hS'_max.symm ▸ Nat.le_succ_of_le ( Finset.le_max' _ _ ( Finset.min'_mem _ _ ) );
      · intro j hj
        have h_mem : S.max' hne + 1 - j ∈ ((Finset.range (S.min' hne)).image (fun i => S.max' hne - i)).image (· + 1) := by
          simp +zetaDelta at *;
          exact ⟨ j, hj, by rw [ tsub_add_eq_add_tsub ( by linarith [ hj _ ( Finset.max'_mem S hne ) ] ) ] ⟩;
        grind;
      · simp_all +decide [ Finset.ext_iff ];
        constructor;
        · intro h₁ h₂; specialize h₂ ( S.min' hne - 1 ) ; rcases k : S.min' hne with ( _ | _ | k ) <;> simp_all +decide ;
          · linarith [ hpos _ ( Finset.min'_mem S hne ) ];
          · exact absurd ( k ▸ Finset.min'_le _ _ h₂.choose_spec.1 ) ( by linarith [ h₂.choose_spec.2 ] );
        · intro x hx; rw [ eq_tsub_iff_add_eq_of_le ] <;> try linarith [ Finset.min'_le _ _ ( Finset.max'_mem _ hne ) ] ;
          contrapose! hx;
          exact ⟨ S.min' hne, Finset.min'_mem _ hne, by omega ⟩

set_option maxHeartbeats 800000 in
/-- After op B, min of the result = s. -/
theorem opB_min {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcondB : S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S)
    (hne' : (franklinInv S).Nonempty) :
    (franklinInv S).min' hne' = topRun S := by
      refine' le_antisymm _ _ <;> simp_all +decide [ franklinInv ];
      · split_ifs <;> simp_all +decide [ Finset.min' ];
        grind;
      · split_ifs <;> simp_all +decide [ Finset.subset_iff ];
        · exact absurd ( hcondB.1 _ ( Finset.min'_mem _ hne ) ) ( by linarith );
        · rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ k, hk₁, rfl ⟩ );
          · linarith [ hcondB.1 a ha₁ ];
          · have := hcondB.1 ( S.max' hne - k ) ?_;
            · exact Nat.le_sub_one_of_lt this;
            · exact?

set_option maxHeartbeats 800000 in
/-- After op B, max of the result = M - 1. -/
theorem opB_max {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcondB : S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S)
    (hne' : (franklinInv S).Nonempty) :
    (franklinInv S).max' hne' = S.max' hne - 1 := by
      have h_max : ∀ x ∈ franklinInv S, x ≤ S.max' hne - 1 := by
        intro x hx;
        by_cases h : S.min' hne ≤ topRun S ∧ ( S.min' hne < topRun S ∨ S.min' hne < S.card ) <;> simp_all +decide [ franklinInv ];
        · linarith [ hcondB.1 _ ( Finset.min'_mem _ hne ) ];
        · rcases hx with ( rfl | ⟨ hx₁, hx₂ ⟩ | ⟨ a, ha₁, rfl ⟩ );
          · exact Nat.le_sub_one_of_lt ( hcondB.1 _ ( Finset.max'_mem _ hne ) );
          · refine' Nat.le_sub_one_of_lt ( lt_of_le_of_ne ( Finset.le_max' _ _ hx₁ ) _ );
            intro H; specialize hx₂ 0; simp_all +decide ;
            exact absurd hx₂ ( ne_of_gt ( topRun_pos hne ) );
          · exact Nat.sub_le_sub_right ( Nat.sub_le _ _ ) _;
      refine' le_antisymm ( h_max _ <| Finset.max'_mem _ _ ) ( Finset.le_max' _ _ _ );
      unfold franklinInv; simp +decide [ hne, hpos, hcondB ] ;
      split_ifs <;> simp_all +decide [ Finset.subset_iff ];
      · linarith [ hcondB.1 _ ( Finset.min'_mem S hne ), Finset.min'_le _ _ ( Finset.max'_mem S hne ) ];
      · rcases k : topRun S with ( _ | k ) <;> simp_all +decide [ Nat.sub_sub ];
        · exact absurd k ( ne_of_gt ( topRun_pos hne ) );
        · exact Or.inr <| Or.inr <| ⟨ 0, by norm_num, by norm_num ⟩

set_option maxHeartbeats 800000 in
/-- After op B, topRun of the result ≥ s. -/
theorem opB_topRun_ge {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcondB : S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S) :
    topRun (franklinInv S) ≥ topRun S := by
      -- Let $M = \max(S)$ and $s = \topRun(S)$.
      set M := S.max' hne
      set s := topRun S
      have hM : M = S.max' hne := rfl
      have hs : s = topRun S := rfl
      have hs_lt_M : s < M := by
        exact lt_of_lt_of_le hcondB.1 ( Finset.min'_le _ _ ( Finset.max'_mem _ _ ) )
      have hs_lt_M_plus_1 : s < M + 1 := by
        linarith;
      -- Since $s < M$, we have $M - 1 \in franklinInv S$ and $M - 2 \in franklinInv S$, ..., $M - s \in franklinInv S$.
      have h_elements : ∀ j < s, (M - 1 - j) ∈ franklinInv S := by
        intros j hj_lt_s
        have h_j_in_T : M - j ∈ (Finset.range s).image (fun i => M - i) := by
          exact Finset.mem_image.mpr ⟨ j, Finset.mem_range.mpr hj_lt_s, rfl ⟩
        have h_j_in_T' : M - 1 - j ∈ (Finset.range s).image (fun i => M - i - 1) := by
          exact Finset.mem_image.mpr ⟨ j, Finset.mem_range.mpr hj_lt_s, by omega ⟩
        have h_j_in_franks : M - 1 - j ∈ franklinInv S := by
          grind +locals
        exact h_j_in_franks;
      -- Since $M - 1 \in franklinInv S$, we have $\max(franklinInv S) = M - 1$.
      have h_max : (franklinInv S).max' (by
      exact ⟨ _, h_elements 0 ( topRun_pos hne ) ⟩) = M - 1 := by
        apply opB_max;
        · assumption;
        · tauto
      generalize_proofs at *;
      unfold topRun at *;
      grind

set_option maxHeartbeats 1600000 in
/-- When operation A applies, franklinInv is an involution.
After op A (remove σ, shift top σ elements up), the result S' has:
- max(S') = M + 1
- topRun(S') = σ (a gap appears at M - σ + 1)
- min(S') > σ (σ was removed)
- M + 1 ≠ 2σ
So op B applies to S', and the op B computation recovers S. -/
theorem franklinInv_invol_caseA {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcond : S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card)) :
    franklinInv (franklinInv S) = S := by
      convert franklinInv_eq_opB ( franklinInv_nonempty hne hpos ) _ using 1;
      · ext x;
        by_cases hx : x ∈ S <;> simp_all +decide [ Finset.subset_iff ];
        · by_cases hx' : x ∈ (Finset.range (S.min' hne)).image (fun i => S.max' hne - i);
          · obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp hx';
            refine' Or.inr <| Or.inr ⟨ i, _, _ ⟩;
            · rw [ opA_topRun hne hpos hcond ] ; linarith [ Finset.mem_range.mp hi ];
            · rw [ opA_max ];
              grobner;
              exacts [ hne, hpos, hcond ];
          · by_cases hx'' : x = S.min' hne;
            · rw [ opA_topRun hne hpos hcond ] ; aesop;
            · refine' Or.inr <| Or.inl ⟨ _, _ ⟩;
              · grind +suggestions;
              · intro i hi;
                rw [ opA_max ];
                any_goals assumption;
                contrapose! hx';
                rw [ opA_topRun ] at hi;
                rotate_left;
                grind;
                · assumption;
                · exact hcond;
                · rw [ Nat.sub_eq_iff_eq_add ] at hx';
                  · exact Finset.mem_image.mpr ⟨ S.max' hne - x, Finset.mem_range.mpr ( by omega ), by rw [ Nat.sub_sub_self ( by linarith [ Finset.le_max' _ _ hx ] ) ] ⟩;
                  · exact le_trans hi.le ( Nat.le_succ_of_le ( Finset.min'_le _ _ ( Finset.max'_mem _ _ ) ) );
        · rw [ opA_topRun hne hpos hcond ];
          refine' ⟨ _, _, _ ⟩;
          · exact fun h => hx <| h.symm ▸ Finset.min'_mem _ hne;
          · intro hx';
            use (franklinInv S).max' (franklinInv_nonempty hne hpos) - x;
            rw [ opA_max hne hpos hcond ];
            grind +locals;
          · intro i hi;
            rw [ opA_max hne hpos hcond ];
            contrapose! hx;
            convert topRun_mem hne ( show i < topRun S from lt_of_lt_of_le hi hcond.1 ) using 1;
            omega;
      · constructor
        all_goals generalize_proofs at *;
        · rw [ opA_topRun hne hpos hcond ];
          exact opA_all_gt hne hpos hcond _ ( Finset.min'_mem _ _ );
        · have h_max_ge_2sigma : S.max' hne ≥ 2 * S.min' hne := by
            have h_max_ge_2sigma : S.min' hne ∉ (Finset.range (S.min' hne)).image (fun i => S.max' hne - i) := by
              exact sigma_not_in_topBlock hne hcond
            generalize_proofs at *;
            nontriviality;
            contrapose! h_max_ge_2sigma;
            exact Finset.mem_image.mpr ⟨ S.max' hne - S.min' hne, Finset.mem_range.mpr ( by omega ), by rw [ Nat.sub_sub_self ( by linarith [ Finset.min'_le _ _ ( Finset.max'_mem _ hne ) ] ) ] ⟩
          generalize_proofs at *;
          rw [ opA_max hne hpos hcond ‹_›, opA_topRun hne hpos hcond ] ; omega

set_option maxHeartbeats 1600000 in
/-- When operation B applies, franklinInv is an involution.
After op B (shift top s elements down, add s), the result S' has:
- min(S') = s
- max(S') = M - 1
- topRun(S') ≥ s, and s < card(S')
So op A applies to S', and the op A computation recovers S. -/
theorem franklinInv_invol_caseB {S : Finset ℕ} (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (hcondB : S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S) :
    franklinInv (franklinInv S) = S := by
      -- Let's unfold the definition of `franklinInv` for `S`.
      have hS' : franklinInv S = ((S \ (Finset.range (topRun S)).image (fun i => S.max' hne - i)) ∪ ((Finset.range (topRun S)).image (fun i => S.max' hne - i)).image (· - 1)) ∪ {topRun S} := by
        exact?;
      -- Let's simplify the expression for `franklinInv (franklinInv S)`.
      have hS'_simplified : franklinInv (franklinInv S) = ((franklinInv S \ (Finset.range (topRun S)).image (fun i => (S.max' hne - 1) - i)) \ {topRun S}) ∪ ((Finset.range (topRun S)).image (fun i => (S.max' hne - 1) - i)).image (· + 1) := by
        rw [franklinInv_eq_opA];
        any_goals exact franklinInv_nonempty hne hpos;
        · rw [ opB_min, opB_max ] <;> aesop;
        · refine' ⟨ _, Or.inr _ ⟩;
          · refine' le_trans _ ( opB_topRun_ge hne hpos hcondB );
            exact opB_min hne hpos hcondB ( franklinInv_nonempty hne hpos ) |> le_of_eq;
          · have h_card : (franklinInv S).card = S.card + 1 := by
              convert card_operationB hne hpos hcondB using 1;
              rw [hS'];
            have h_min_lt_card : (franklinInv S).min' (franklinInv_nonempty hne hpos) ≤ topRun S := by
              exact Finset.min'_le _ _ ( hS'.symm ▸ Finset.mem_union_right _ ( Finset.mem_singleton_self _ ) );
            linarith [ show topRun S ≤ S.card from topRun_le_card hne ];
      -- Let's simplify the expression for `franklinInv (franklinInv S)` further.
      have hS'_simplified' : ((franklinInv S \ (Finset.range (topRun S)).image (fun i => (S.max' hne - 1) - i)) \ {topRun S}) = S \ (Finset.range (topRun S)).image (fun i => S.max' hne - i) := by
        ext x; simp [hS'];
        constructor <;> intro h;
        · grind;
        · grind +suggestions;
      have hS'_simplified'' : ((Finset.range (topRun S)).image (fun i => (S.max' hne - 1) - i)).image (· + 1) = (Finset.range (topRun S)).image (fun i => S.max' hne - i) := by
        ext; simp [Finset.mem_image];
        constructor <;> rintro ⟨ a, ha, rfl ⟩ <;> use a;
        · rw [ tsub_right_comm, tsub_add_cancel_of_le ];
          · exact ⟨ ha, rfl ⟩;
          · exact Nat.sub_pos_of_lt ( by linarith [ Finset.le_max' _ _ ( Finset.min'_mem _ hne ), topRun_le_card hne ] );
        · rw [ tsub_right_comm, tsub_add_cancel_of_le ];
          · exact ⟨ ha, rfl ⟩;
          · exact Nat.sub_pos_of_lt ( by linarith [ Finset.le_max' _ _ ( Finset.min'_mem _ hne ), topRun_le_card hne ] );
      rw [ hS'_simplified, hS'_simplified', hS'_simplified'' ];
      rw [ Finset.union_comm, Finset.union_sdiff_of_subset ];
      exact topBlock_subset hne ( by linarith )

/-- Franklin's involution is an involution.
The proof proceeds by case analysis: after operation A, operation B is applied
to the result (and vice versa), and the composition gives back the original set. -/
theorem franklinInv_invol {S : Finset ℕ} (hpos : ∀ x ∈ S, 0 < x) :
    franklinInv (franklinInv S) = S := by
  by_cases hne : S.Nonempty
  · by_cases hA : S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card)
    · exact franklinInv_invol_caseA hne hpos hA
    · by_cases hB : S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S
      · exact franklinInv_invol_caseB hne hpos hB
      · -- Fixed point case: franklinInv S = S
        have hfix : franklinInv S = S := by
          simp only [franklinInv, dif_pos hne]
          split_ifs with h1 h2 <;> first | exact absurd h1 hA | rfl
        simp only [hfix]
  · simp only [franklinInv, show ¬S.Nonempty from hne, dite_false]

/-! ## Part III: Alternating sum equals pentagonal coefficient -/

/-- The sum over non-fixed points of the involution is zero. -/
theorem non_fixed_sum_zero (n : ℕ) :
    ((StrictPartitions n).filter (fun S => franklinInv S ≠ S)).sum
      (fun S => (-1 : ℤ) ^ S.card) = 0 := by
  apply Finset.sum_involution (fun S hS => franklinInv S);
  · simp +zetaDelta at *;
    exact fun S hS hne => by rw [ add_comm ] ; exact franklinInv_sign ( fun x hx => ( Finset.mem_filter.mp hS ) |>.2.1 x hx ) hne;
  · grind +locals;
  · simp +zetaDelta at *;
    intro S hS hne;
    exact ⟨ franklinInv_mem hS, by rw [ franklinInv_invol ( fun x hx => Finset.mem_filter.mp hS |>.2.1 x hx ) ] ; tauto ⟩;
  · intro S hS
    have h_pos : ∀ x ∈ S, 0 < x := by
      unfold StrictPartitions at hS; aesop;
    exact franklinInv_invol h_pos

set_option maxHeartbeats 1600000 in
/-- Fixed points of franklinInv in StrictPartitions are exactly intervals. -/
theorem fixed_point_is_interval {n : ℕ} {S : Finset ℕ}
    (hS : S ∈ StrictPartitions n) (hne : S.Nonempty) (hfixed : franklinInv S = S) :
    S = Finset.Icc (S.min' hne) (S.max' hne) := by
      have hcases : ¬(S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card)) ∧ ¬(S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S) := by
        constructor <;> intro h <;> simp_all +decide [ franklinInv ];
        · have := opA_all_gt hne ( fun x hx => Finset.mem_filter.mp hS |>.2.1 x hx ) h; simp_all +decide [ Finset.ext_iff ] ;
          unfold franklinInv at this; simp_all +decide [ Finset.ext_iff ] ;
          exact absurd ( this _ ( Finset.min'_mem _ hne ) ) ( by norm_num );
        · grind +suggestions;
      by_cases hcase2 : S.min' hne > topRun S ∧ S.max' hne = 2 * topRun S;
      · have h_subset : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
          exact fun x hx => Finset.mem_Icc.mpr ⟨ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx ⟩;
        refine' Finset.eq_of_subset_of_card_le h_subset _;
        simp +arith +decide [ hcase2 ];
        linarith [ show S.card ≥ topRun S from le_trans ( topRun_le_card hne ) ( by simp ) ];
      · have hcase1 : S.min' hne = topRun S ∧ S.min' hne = S.card := by
          grind +suggestions;
        have htopRun : ∀ j, j < topRun S → S.max' hne - j ∈ S := by
          grind +suggestions;
        have htopRun_subset : Finset.image (fun j => S.max' hne - j) (Finset.range (topRun S)) ⊆ S := by
          exact Finset.image_subset_iff.mpr fun j hj => htopRun j <| Finset.mem_range.mp hj;
        have htopRun_eq : Finset.image (fun j => S.max' hne - j) (Finset.range (topRun S)) = S := by
          refine' Finset.eq_of_subset_of_card_le htopRun_subset _;
          rw [ Finset.card_image_of_injOn ];
          · grind;
          · exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ Finset.mem_range.mp hx, Finset.mem_range.mp hy, Finset.le_max' _ _ ( Finset.min'_mem _ hne ) ] ;
        refine' Finset.eq_of_subset_of_card_le _ _;
        · exact fun x hx => Finset.mem_Icc.mpr ⟨ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx ⟩;
        · simp +zetaDelta at *;
          grind +qlia

set_option maxHeartbeats 1600000 in
/-- Fixed point intervals have min and max satisfying: either min = max - min + 1
    (i.e., max = 2*min - 1, type 1) or min > max - min + 1 and max = 2*(max - min + 1)
    (type 2). Equivalently, the card k satisfies either min = k or min = k + 1. -/
theorem fixed_point_params {n : ℕ} {S : Finset ℕ}
    (hS : S ∈ StrictPartitions n) (hne : S.Nonempty) (hfixed : franklinInv S = S) :
    let k := S.card
    (S = Finset.Icc k (2 * k - 1) ∧ n = k * (3 * k - 1) / 2) ∨
    (S = Finset.Icc (k + 1) (2 * k) ∧ n = k * (3 * k + 1) / 2) := by
      -- Let's unfold the definition of `franklinInv` and analyze the conditions for it to be a fixed point.
      have h_open_A : ¬ (S.min' hne ≤ topRun S ∧ (S.min' hne < topRun S ∨ S.min' hne < S.card)) := by
        have h_card : (S.min' hne < S.max' hne + 1) ∧ (S.min' hne < (Finset.range (S.min' hne)).card ∨ S.min' hne + (S.min' hne - S.max' hne) < 0) → False := by
          grind;
        grind +suggestions
      have h_open_B : ¬ (S.min' hne > topRun S ∧ S.max' hne ≠ 2 * topRun S) := by
        grind +suggestions;
      -- By definition of `franklinInv`, we know that `S = Icc (S.min' hne) (S.max' hne)`.
      have h_interval : S = Finset.Icc (S.min' hne) (S.max' hne) := by
        apply fixed_point_is_interval hS hne hfixed;
      -- By definition of `topRun`, we know that `topRun S = S.max' hne - S.min' hne + 1`.
      have h_topRun : topRun S = S.max' hne - S.min' hne + 1 := by
        rw [ topRun_eq_of ];
        grind +suggestions;
        · grind +suggestions;
        · grind;
        · grind +locals;
      -- By definition of `StrictPartitions`, we know that `n = ∑ x ∈ S, x`.
      have h_sum : n = ∑ x ∈ S, x := by
        exact Eq.symm ( Finset.mem_filter.mp hS |>.2.2 );
      -- By definition of `StrictPartitions`, we know that `S.card = S.max' hne - S.min' hne + 1`.
      have h_card : S.card = S.max' hne - S.min' hne + 1 := by
        conv_lhs => rw [ h_interval ] ; simp +decide [ Nat.card_Icc ] ;
        rw [ Nat.sub_add_comm ( Finset.min'_le _ _ ( Finset.max'_mem _ _ ) ) ];
      -- By definition of `StrictPartitions`, we know that `∑ x ∈ Finset.Icc (S.min' hne) (S.max' hne), x = (S.max' hne - S.min' hne + 1) * (S.min' hne + S.max' hne) / 2`.
      have h_sum_formula : ∑ x ∈ Finset.Icc (S.min' hne) (S.max' hne), x = (S.max' hne - S.min' hne + 1) * (S.min' hne + S.max' hne) / 2 := by
        erw [ Finset.sum_Ico_eq_sum_range ];
        rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
        rw [ Finset.sum_add_distrib ];
        norm_num [ Nat.sub_add_comm ( show S.min' hne ≤ S.max' hne from Finset.min'_le _ _ ( Finset.max'_mem _ hne ) ) ];
        nlinarith! only [ Nat.sub_add_cancel ( show S.min' hne ≤ S.max' hne from Finset.min'_le _ _ ( Finset.max'_mem _ hne ) ), Finset.sum_range_id_mul_two ( S.max' hne - S.min' hne + 1 ) ];
      grind

/-- The sum over fixed points of the involution equals `pentagonalCoeff n`.
The fixed points are exactly the "pentagonal partitions":
- `∅` (when `n = 0`)
- `{k, k+1, ..., 2k-1}` (when `n = k(3k-1)/2`, type 1)
- `{k+1, k+2, ..., 2k}` (when `n = k(3k+1)/2`, type 2) -/
theorem fixed_sum_eq (n : ℕ) :
    ((StrictPartitions n).filter (fun S => franklinInv S = S)).sum
      (fun S => (-1 : ℤ) ^ S.card) = pentagonalCoeff n := by
  sorry

/-- The alternating sum over strict partitions equals `pentagonalCoeff n`. -/
theorem alternating_sum_eq (n : ℕ) :
    (StrictPartitions n).sum (fun S => (-1 : ℤ) ^ S.card) = pentagonalCoeff n := by
  have := Finset.sum_filter_add_sum_filter_not (StrictPartitions n) (fun S => franklinInv S = S)
    (fun S => (-1 : ℤ) ^ S.card)
  rw [fixed_sum_eq] at this
  have h2 : ((StrictPartitions n).filter (fun x => ¬franklinInv x = x)).sum
      (fun S => (-1 : ℤ) ^ S.card) = 0 := non_fixed_sum_zero n
  linarith

/-! ## Main theorem -/

/-- **Euler's Pentagonal Number Theorem**: For all `N > n`, the coefficient of `x^n`
in the Euler product `∏_{i=1}^{N} (1 - x^i)` equals `pentagonalCoeff n`. -/
theorem euler_pentagonal (n : ℕ) (N : ℕ) (hN : n < N) :
    (PowerSeries.coeff (R := ℤ) n) (eulerProd N) = pentagonalCoeff n := by
  rw [coeff_eulerProd_eq_sum n N hN]
  exact alternating_sum_eq n

end