import Mathlib

/-!
# Franklin's involution via sorted lists

An alternative formalization of partitions into distinct parts using
**strictly decreasing lists** of positive natural numbers, rather than
`Finset ℕ`. The advantage of the list representation is that the
"base" (smallest part) is the last element and the "slope" (maximal
consecutive run from the top) is a prefix of the list, so most
operations become structural recursion / `List.takeWhile` / `List.span`
instead of `Finset.filter` plus interval lemmas.
-/

namespace ListPartitions

/-- A partition into distinct parts, represented as a strictly
    decreasing list of positive naturals. -/
structure DistinctPartition where
  parts : List ℕ
  sorted : parts.Sorted (· > ·)
  pos : ∀ x ∈ parts, 0 < x

namespace DistinctPartition

/-- The integer being partitioned. -/
def sum (p : DistinctPartition) : ℕ := p.parts.sum

/-- Number of parts. -/
def card (p : DistinctPartition) : ℕ := p.parts.length

/-- A partition is non-empty if it has at least one part. -/
def Nonempty (p : DistinctPartition) : Prop := p.parts ≠ []

/-- The largest part — head of the decreasing list. -/
def maxPart (p : DistinctPartition) (h : p.Nonempty) : ℕ :=
  p.parts.head h

/-- The smallest part — last element of the decreasing list. -/
def base (p : DistinctPartition) (h : p.Nonempty) : ℕ :=
  p.parts.getLast h

/-- The slope: the maximal prefix `[m, m-1, m-2, ...]` of consecutive
    decreasing integers starting from the head. Implemented with
    `List.takeWhile` indexed by position: position `i` is in the slope
    iff `parts[i] = parts[0] - i`. -/
def slope (p : DistinctPartition) : List ℕ :=
  match p.parts with
  | []     => []
  | x :: _ => p.parts.takeWhile (fun y => decide (x ≥ y) ∧
                                          decide (y + (p.parts.idxOf y) ≥ x ∧
                                                  x ≥ y + (p.parts.idxOf y)))

/-- A cleaner definition of the slope using a recursive helper that
    walks the list and stops as soon as the gap is not 1. -/
def slopeAux : ℕ → List ℕ → List ℕ
  | _, []      => []
  | k, x :: xs => if x = k then x :: slopeAux (k - 1) xs else []

/-- The slope of a partition: maximal strictly-decreasing-by-1 prefix. -/
def slope' (p : DistinctPartition) : List ℕ :=
  match p.parts with
  | []     => []
  | x :: _ => slopeAux x p.parts

/-- Length of the slope. -/
def slopeCard (p : DistinctPartition) : ℕ := (slope' p).length

end DistinctPartition

/-! ## Alpha and beta criteria -/

open DistinctPartition

/-- Alpha applies when the base is strictly less than the slope length,
    or equal to the slope length but disjoint from the slope.
    In list terms: the slope is a prefix `[m, m-1, ..., m-σ+1]` where
    `σ = slopeCard`. The base `b` is in the slope iff `b ≥ m - σ + 1`,
    i.e. iff `b + σ ≥ m + 1`. -/
def alphaCrit (p : DistinctPartition) (h : p.Nonempty) : Prop :=
  let b := p.base h
  let σ := slopeCard p
  let m := p.maxPart h
  (b ≤ σ ∧ b + σ < m + 1) ∨ b < σ

/-- Beta applies when base > slope length, with no collision.  -/
def betaCrit (p : DistinctPartition) (h : p.Nonempty) : Prop :=
  let b := p.base h
  let σ := slopeCard p
  let m := p.maxPart h
  (b > σ ∧ b + σ < m + 1) ∨ σ + 2 ≤ b

/-! ## Alpha and beta involutions on sorted lists -/

/-- Helper: increment the first `b` elements of a list. On a sorted
    decreasing list whose head-prefix is the slope, this corresponds to
    "lifting the top `b` rows of the slope". -/
def incFirst : ℕ → List ℕ → List ℕ
  | 0,     xs       => xs
  | _ + 1, []       => []
  | k + 1, x :: xs  => (x + 1) :: incFirst k xs

/-- Alpha on lists: drop the last element (the base `b`), then add 1 to
    the top `b` elements of what remains.

    Example. `[7, 6, 5, 4, 2]` has base `b = 2`, slope `[7,6,5,4]`,
    so alpha gives `[8, 7, 5, 4]`. -/
def alphaList (p : DistinctPartition) (h : p.Nonempty) : List ℕ :=
  let b := p.base h
  incFirst b (p.parts.dropLast)

/-- Beta on lists: subtract 1 from every slope element, then append
    a new bottom row of size `slopeCard`.

    Example. `[8, 7, 5, 4]` has slope `[8,7]`, slopeCard `2`,
    so beta gives `[7, 6, 5, 4, 2]`. -/
def betaList (p : DistinctPartition) (h : p.Nonempty) : List ℕ :=
  let σ := slopeCard p
  let head := (slope' p).map (· - 1)
  let tail := p.parts.drop σ
  head ++ tail ++ [σ]

/-! ## Sum-preservation (statements; proofs to be filled in) -/

/-- The sum of a list with its first `k` entries each incremented by 1
    differs from the original sum by `min k (length xs)`. -/
lemma incFirst_sum (k : ℕ) (xs : List ℕ) :
    (incFirst k xs).sum = xs.sum + min k xs.length := by
  induction k generalizing xs with
  | zero => simp [incFirst]
  | succ k ih =>
    cases xs with
    | nil => simp [incFirst]
    | cons x xs =>
      simp [incFirst, ih, List.sum_cons]
      omega

/-- Length is preserved by `incFirst`. -/
lemma incFirst_length (k : ℕ) (xs : List ℕ) :
    (incFirst k xs).length = xs.length := by
  induction k generalizing xs with
  | zero => simp [incFirst]
  | succ k ih =>
    cases xs with
    | nil => simp [incFirst]
    | cons _ xs => simp [incFirst, ih]

/-- Alpha preserves the partitioned integer. -/
theorem alphaList_preserves_sum (p : DistinctPartition) (h : p.Nonempty)
    (hcrit : alphaCrit p h) :
    (alphaList p h).sum = p.sum := by
  -- The dropped last element is `base = b`. Adding 1 to the top `b`
  -- elements adds exactly `b` (since the list has length ≥ b under
  -- `alphaCrit`). So the net change is `-b + b = 0`.
  sorry

/-- The slope is a strictly decreasing run by 1 from the top. -/
lemma slope'_consecutive (p : DistinctPartition) (h : p.Nonempty) :
    ∀ i, i < (slope' p).length →
      (slope' p).get ⟨i, by exact ‹_›⟩ = p.maxPart h - i := by
  sorry

/-- Beta preserves the partitioned integer. -/
theorem betaList_preserves_sum (p : DistinctPartition) (h : p.Nonempty)
    (hcrit : betaCrit p h) :
    (betaList p h).sum = p.sum := by
  -- Lowering each of the `σ` slope elements by 1 subtracts `σ`;
  -- appending a new row of size `σ` adds `σ`.
  sorry

/-! ## Distinctness and positivity preservation -/

theorem alphaList_sorted (p : DistinctPartition) (h : p.Nonempty)
    (hcrit : alphaCrit p h) :
    (alphaList p h).Sorted (· > ·) := by
  sorry

theorem alphaList_pos (p : DistinctPartition) (h : p.Nonempty)
    (hcrit : alphaCrit p h) :
    ∀ x ∈ alphaList p h, 0 < x := by
  sorry

theorem betaList_sorted (p : DistinctPartition) (h : p.Nonempty)
    (hcrit : betaCrit p h) :
    (betaList p h).Sorted (· > ·) := by
  sorry

theorem betaList_pos (p : DistinctPartition) (h : p.Nonempty)
    (hcrit : betaCrit p h) :
    ∀ x ∈ betaList p h, 0 < x := by
  sorry

/-- Package alpha as a map on `DistinctPartition`. -/
def alpha (p : DistinctPartition) (h : p.Nonempty) (hcrit : alphaCrit p h) :
    DistinctPartition where
  parts := alphaList p h
  sorted := alphaList_sorted p h hcrit
  pos := alphaList_pos p h hcrit

/-- Package beta as a map on `DistinctPartition`. -/
def beta (p : DistinctPartition) (h : p.Nonempty) (hcrit : betaCrit p h) :
    DistinctPartition where
  parts := betaList p h
  sorted := betaList_sorted p h hcrit
  pos := betaList_pos p h hcrit

/-! ## Franklin's map -/

/-- Franklin's involution. Note that exactly one of the criteria can
    hold on a non-fixed-point partition. -/
noncomputable def franklin (p : DistinctPartition) (h : p.Nonempty) :
    DistinctPartition :=
  if hα : alphaCrit p h then alpha p h hα
  else if hβ : betaCrit p h then beta p h hβ
  else p

/-! ## Top-level theorems (to be proved) -/

theorem alpha_inverse_beta (p : DistinctPartition) (h : p.Nonempty)
    (hα : alphaCrit p h) :
    let p' := alpha p h hα
    ∃ h' : p'.Nonempty, ∃ hβ : betaCrit p' h', beta p' h' hβ = p := by
  sorry

theorem beta_inverse_alpha (p : DistinctPartition) (h : p.Nonempty)
    (hβ : betaCrit p h) :
    let p' := beta p h hβ
    ∃ h' : p'.Nonempty, ∃ hα : alphaCrit p' h', alpha p' h' hα = p := by
  sorry

theorem franklin_changes_parity (p : DistinctPartition) (h : p.Nonempty)
    (hcrit : alphaCrit p h ∨ betaCrit p h) :
    ∃ h' : (franklin p h).Nonempty,
      (franklin p h).card % 2 ≠ p.card % 2 := by
  sorry

end ListPartitions
