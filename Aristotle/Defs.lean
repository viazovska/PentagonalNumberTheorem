import Mathlib
open Finset
set_option maxHeartbeats 800000
/-! # Pentagonal Number Theorem — Definitions
This file contains the core definitions for the formalization of the
Pentagonal Number Theorem, following the source document
"Pentagonal Number Theorem" by JC, PM, MV (May 11, 2026).
-/
/-- Helper: count the length of the consecutive run ending at position `m` in `S`,
going downward. E.g., if `S = {4,5,6}` and `m = 6`, returns 3. -/
def consecutiveTopRun (S : Finset ℕ) : ℕ → ℕ
  | 0 => if (0 : ℕ) ∈ S then 1 else 0
  | m + 1 => if m + 1 ∈ S then 1 + consecutiveTopRun S m else 0
/-- **Definition 4 (Source, 𝒫(n))**: The set of partitions of `n` into distinct positive parts.
Each partition is a subset `S ⊆ {1, …, n}` with `∑_{s ∈ S} s = n`. -/
def DP (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter (fun S => S.sum id = n)
/-- **Definition 4 (Source, 𝒫_even(n))**: Partitions of `n` into distinct parts
with an even number of parts. -/
def DPeven (n : ℕ) : Finset (Finset ℕ) :=
  (DP n).filter (fun S => S.card % 2 = 0)
/-- **Definition 4 (Source, 𝒫_odd(n))**: Partitions of `n` into distinct parts
with an odd number of parts. -/
def DPodd (n : ℕ) : Finset (Finset ℕ) :=
  (DP n).filter (fun S => S.card % 2 = 1)
/-- **Definition 4 (Source, p_e(n))**: Number of even partitions of `n` into distinct parts. -/
def pe (n : ℕ) : ℕ := (DPeven n).card
/-- **Definition 4 (Source, p_o(n))**: Number of odd partitions of `n` into distinct parts. -/
def po (n : ℕ) : ℕ := (DPodd n).card
/-- **Definition 9 (Source, base)**: The smallest element of a partition.
Returns 0 for the empty set. -/
def partBase (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.min' h else 0
/-- **Definition 9 (Source, max)**: The largest element of a partition.
Returns 0 for the empty set. -/
def partMax (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.max' h else 0
/-- **Definition 9 (Source, slope)**: The length of the maximal consecutive run
from `max(S)` downward in `S`. Returns 0 for the empty set. -/
def partSlope (S : Finset ℕ) : ℕ :=
  consecutiveTopRun S (partMax S)
/-- **Definition 9 (Source, slope set D)**: The set `{max(S)−slope(S)+1, …, max(S)}`.
Returns `∅` for the empty set. -/
def partSlopeSet (S : Finset ℕ) : Finset ℕ :=
  Icc (partMax S - partSlope S + 1) (partMax S)
/-- **Definition 10 (Source, 𝒫_α(n))**: Partitions `S ∈ 𝒫(n)` that are nonempty and satisfy
`(b ≤ s ∧ b ∉ D) ∨ b ≤ s − 1`, where `b = base(S)`, `s = slope(S)`, `D = slopeSet(S)`.
In ℕ arithmetic, `b ≤ s − 1` becomes `b + 1 ≤ s`, and `b ∉ D` becomes
`b < max(S) − slope(S) + 1`. -/
def DPalpha (n : ℕ) : Finset (Finset ℕ) :=
  (DP n).filter (fun S =>
    0 < S.card ∧
    ((partBase S ≤ partSlope S ∧ ¬(partMax S - partSlope S + 1 ≤ partBase S)) ∨
     partBase S + 1 ≤ partSlope S))
/-- **Definition 10 (Source, 𝒫_β(n))**: Partitions `S ∈ 𝒫(n)` that are nonempty and satisfy
`(b > s ∧ b ∉ D) ∨ b ≥ s + 2`, where `b = base(S)`, `s = slope(S)`, `D = slopeSet(S)`.
Here `b ∉ D` becomes `b < max(S) − slope(S) + 1`. -/
def DPbeta (n : ℕ) : Finset (Finset ℕ) :=
  (DP n).filter (fun S =>
    0 < S.card ∧
    ((partSlope S < partBase S ∧ ¬(partMax S - partSlope S + 1 ≤ partBase S)) ∨
     partSlope S + 2 ≤ partBase S))
/-- **Definition 10 (Source, 𝒫_special(n))**: Partitions `S ∈ 𝒫(n)` that are either empty,
or satisfy `b ∈ D ∧ (b = s ∨ b = s + 1)`. -/
def DPspecial (n : ℕ) : Finset (Finset ℕ) :=
  (DP n).filter (fun S =>
    S.card = 0 ∨
    (0 < S.card ∧
     partMax S - partSlope S + 1 ≤ partBase S ∧
     (partBase S = partSlope S ∨ partBase S = partSlope S + 1)))
/-- **Definition 13 (Source, S_{−k})**: For `k ≥ 1`, the set `{k, k+1, …, 2k−1}`,
which has `k` elements summing to `(3k²−k)/2`. -/
def SmkSet (k : ℕ) : Finset ℕ := Icc k (2 * k - 1)
/-- **Definition 13 (Source, S_k)**: For `k ≥ 1`, the set `{k+1, k+2, …, 2k}`,
which has `k` elements summing to `(3k²+k)/2`. -/
def SpkSet (k : ℕ) : Finset ℕ := Icc (k + 1) (2 * k)
/-- **Definition 15 (Source, α)**: For `S ∈ 𝒫_α(n)` with base `b` and max `m`,
`α(S) = (S \ {b, m−b+1}) ∪ {m+1}`.
Defined as a total function on `Finset ℕ`; only meaningful on `DPalpha`. -/
def alphaOp (S : Finset ℕ) : Finset ℕ :=
  let b := partBase S
  let m := partMax S
  insert (m + 1) ((S.erase b).erase (m - b + 1))
/-- **Definition 15 (Source, β)**: For `S ∈ 𝒫_β(n)` with slope `s` and max `m`,
`β(S) = (S ∪ {s, m−s}) \ {m}`.
Defined as a total function on `Finset ℕ`; only meaningful on `DPbeta`. -/
def betaOp (S : Finset ℕ) : Finset ℕ :=
  let s := partSlope S
  let m := partMax S
  (insert s (insert (m - s) S)).erase m
