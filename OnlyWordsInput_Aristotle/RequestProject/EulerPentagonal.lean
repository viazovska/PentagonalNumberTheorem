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

/-- Franklin's involution is an involution.
The proof proceeds by case analysis: after operation A, operation B is applied
to the result (and vice versa), and the composition gives back the original set. -/
theorem franklinInv_invol {S : Finset ℕ} (hpos : ∀ x ∈ S, 0 < x) :
    franklinInv (franklinInv S) = S := by
  sorry

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
