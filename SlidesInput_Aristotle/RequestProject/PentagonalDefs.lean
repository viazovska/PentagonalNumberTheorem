import Mathlib

/-!
# Definitions for Euler's Pentagonal Number Theorem
-/

open scoped BigOperators
open Finset

noncomputable section

/-- The generalized pentagonal number k(3k-1)/2 for k ∈ ℤ. -/
def generalizedPentagonal (k : ℤ) : ℕ := ((k * (3 * k - 1)) / 2).toNat

/-- The pentagonal coefficient at degree d. -/
def pentagonalCoeff (d : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc (-(d : ℤ)) (d : ℤ),
    if generalizedPentagonal k = d then (-1 : ℤ) ^ k.natAbs else 0

/-- The signed count of partitions of n into distinct positive parts. -/
def signedDistinctPartitionCount (n : ℕ) : ℤ :=
  ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.sum id = n),
    (-1 : ℤ) ^ S.card

/-- k(3k-1) is always even. -/
lemma pentagonal_even (k : ℤ) : 2 ∣ k * (3 * k - 1) := by
  exact even_iff_two_dvd.mp ( by simp +decide [ mul_sub, parity_simps ] )

/-- k(3k-1)/2 ≥ 0 for all k. -/
lemma pentagonal_nonneg (k : ℤ) : 0 ≤ k * (3 * k - 1) / 2 := by
  exact Int.le_ediv_of_mul_le ( by norm_num ) ( by rcases lt_trichotomy k 0 with hk | rfl | hk <;> nlinarith )

end
