/-
PROPOSED MATHLIB ADDITION — PR 1 of 3
Target file: Mathlib/Algebra/BigOperators/Intervals.lean
Insertion point: inside `section GaussSum`, immediately after `sum_range_id`.

Rationale: Mathlib has Gauss' summation formula over `Finset.range` but not over
`Finset.Icc`. The `Icc` form is what one actually needs when summing a block of
consecutive naturals, and it is currently re-proved ad hoc in downstream projects.

This staging file exists only to type-check the proposed declarations against the
current Mathlib. In the PR the bodies below go into `Mathlib/Algebra/BigOperators/
Intervals.lean` verbatim (that file already has `module` / `public import` /
`public section` headers and `namespace Finset`, so only the declarations move).
-/
import Mathlib.Algebra.BigOperators.Intervals

namespace Finset

section GaussSum

/-- Gauss' summation formula over an interval. Both sides vanish when `n < m`. -/
theorem sum_Icc_id_mul_two (m n : ℕ) : (∑ i ∈ Icc m n, i) * 2 = (n + 1 - m) * (m + n) := by
  rcases le_or_gt m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hc : m + k + 1 - m = k + 1 := by omega
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, hc, sum_add_distrib, sum_const,
      card_range, smul_eq_mul, add_mul, sum_range_id_mul_two, Nat.add_sub_cancel, mul_assoc,
      ← Nat.mul_add]
    congr 1
    omega
  · rw [Icc_eq_empty (by omega), sum_empty, Nat.sub_eq_zero_of_le (by omega), Nat.zero_mul,
      Nat.zero_mul]

/-- Gauss' summation formula over an interval. -/
theorem sum_Icc_id (m n : ℕ) : ∑ i ∈ Icc m n, i = (n + 1 - m) * (m + n) / 2 := by
  rw [← sum_Icc_id_mul_two, Nat.mul_div_cancel _ Nat.zero_lt_two]

end GaussSum

end Finset

-- ## Sanity checks (NOT part of the PR)
section Checks
open Finset

example : ∑ i ∈ Icc 1 4, i = 10 := by decide
example : (∑ i ∈ Icc 3 7, i) * 2 = (7 + 1 - 3) * (3 + 7) := sum_Icc_id_mul_two 3 7
example : ∑ i ∈ Icc 5 2, i = 0 := by decide
-- degenerate: empty interval, both sides zero
example : (∑ i ∈ Icc 5 2, i) * 2 = (2 + 1 - 5) * (5 + 2) := sum_Icc_id_mul_two 5 2
-- agrees with the existing `range` lemma at `m = 0`, shifted
example (n : ℕ) : (∑ i ∈ Icc 0 n, i) * 2 = (n + 1) * n := by
  rw [sum_Icc_id_mul_two]; simp
-- `Finset.sum _ id` phrasing used by downstream projects
example (m n : ℕ) : (Icc m n).sum id * 2 = (n + 1 - m) * (m + n) := sum_Icc_id_mul_two m n

end Checks
