import Mathlib
import RequestProject.Franklin

/-!
# Euler's Pentagonal Number Theorem (Power Series Form)

We prove that for all d ≤ N,
  coeff_d(∏_{n=1}^{N} (1 - X^n)) = pentagonalCoeff d

This combines:
1. The product expansion identity (Euler product coefficients = signed distinct partition count)
2. The stabilization of coefficients as N grows
3. Franklin's involution (pentagonal_combinatorial from Franklin.lean)
-/

open scoped BigOperators
open Finset

noncomputable section

set_option maxHeartbeats 800000

/-! ## Product expansion -/

/-
The coefficient of X^d in ∏_{n ∈ S} (1 - X^n) equals the signed
    count over subsets T ⊆ S with sum T = d.
-/
lemma prod_one_sub_coeff (S : Finset ℕ) (hS : ∀ x ∈ S, 0 < x) (d : ℕ) :
    PowerSeries.coeff (R := ℤ) d (∏ n ∈ S, (1 - (PowerSeries.X : PowerSeries ℤ) ^ n)) =
    ∑ T ∈ S.powerset.filter (fun T => T.sum id = d),
      (-1 : ℤ) ^ T.card := by
        -- By definition of polynomial multiplication, we can expand the product into a sum.
        have h_expand : (∏ n ∈ S, (1 - PowerSeries.X ^ n)) = (∑ T ∈ S.powerset, (-1 : PowerSeries ℤ) ^ T.card * PowerSeries.X ^ (T.sum id)) := by
          simp +decide [ sub_eq_neg_add, Finset.prod_add ];
          refine' Finset.sum_congr rfl fun T hT => _;
          rw [ Finset.prod_congr rfl fun x hx => neg_eq_neg_one_mul _, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_eq_sum_ones, Finset.prod_pow_eq_pow_sum ];
        simp +decide [ h_expand, PowerSeries.coeff_X_pow ];
        rw [ Finset.sum_filter ];
        refine' Finset.sum_congr rfl fun T hT => _;
        by_cases h : Even T.card <;> simp_all +decide [ PowerSeries.coeff_X_pow ];
        · grind;
        · grind +revert

/-- The coefficient of X^n in ∏_{k=1}^{n}(1-X^k) equals signedDistinctPartitionCount n. -/
lemma eulerCoeff_eq_signedCount (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (∏ k ∈ Finset.Icc 1 n,
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) =
    signedDistinctPartitionCount n := by
  unfold signedDistinctPartitionCount
  exact prod_one_sub_coeff _ (fun x hx => by simp [Finset.mem_Icc] at hx; omega) n

/-
Adding more factors beyond d doesn't change coefficient at degree d.
-/
lemma euler_coeff_stable (d N : ℕ) (hN : d ≤ N) :
    PowerSeries.coeff (R := ℤ) d (∏ k ∈ Finset.Icc 1 N,
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) =
    PowerSeries.coeff (R := ℤ) d (∏ k ∈ Finset.Icc 1 d,
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) := by
        induction' hN with N hN ih;
        · rfl;
        · erw [ Finset.prod_Ico_succ_top ( by linarith [ Nat.succ_le_succ hN ] ), mul_comm ];
          simp_all +decide [ sub_mul, PowerSeries.coeff_mul ];
          simp_all +decide [ PowerSeries.coeff_X_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ];
          erw [ if_neg ( by linarith ) ] ; aesop

/-! ## Main theorem -/

/-- **Euler's Pentagonal Number Theorem**:
    For all d ≤ N, the coefficient of X^d in ∏_{n=1}^{N}(1-X^n)
    equals the pentagonal coefficient. -/
theorem euler_pentagonal_number_theorem (d N : ℕ) (hN : d ≤ N) :
    PowerSeries.coeff (R := ℤ) d (∏ n ∈ Finset.Icc 1 N,
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ n)) =
    pentagonalCoeff d := by
  rw [euler_coeff_stable d N hN, eulerCoeff_eq_signedCount]
  exact pentagonal_combinatorial d

end