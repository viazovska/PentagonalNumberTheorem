import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Max

/- Define the set of partitions of n to distinct parts -/
def all_distinct_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun s => Finset.sum s id = n ∧ ∀ x ∈ s, x > 0)
   (Finset.powerset (Finset.range (n + 1)))

/- Test 1
def c1 : Finset (Finset ℕ) := all_distinct_partitions 3
#eval c1.card

Define the set of partitions of n to even number of distinct parts -/
def even_distinct_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun s => ( Finset.sum s id = n ) ∧ (∀ x ∈ s, x > 0 ) ∧ ( s.card % 2 = 0) )
   (Finset.powerset (Finset.range (n + 1)))

/-- Test 2
def c2 : Finset (Finset ℕ) := even_distinct_partitions 6
#eval c2.card

Define the set of partitions of n to odd number of distinct parts -/
def odd_distinct_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun s => ( Finset.sum s id = n ) ∧ ( ∀ x ∈ s, x > 0 ) ∧ ( s.card % 2 = 1 ))
  (Finset.powerset (Finset.range (n + 1)))


/- Test 3
def c3 : Finset (Finset ℕ) := odd_distinct_partitions 6
#eval c3.card -/
def p_e (n : ℕ) : ℕ := (even_distinct_partitions n).card

def p_o (n : ℕ) : ℕ := (odd_distinct_partitions n).card

/- Test 4
#eval p_e 5

#eval p_e 2
#eval p_o 2
 -/

/- \begin{theorem}Let $n$ be a natural number.
If there exists $k\in\mathbb{Z}$ such that $n=(3k^2-k)/2$ then
$p_e(n)-p_0(n)=(-1)^k$,
otherwise $p_e(n)-p_0(n)=0$\end{theorem} -/


/-- Euler’s pentagonal number theorem. -/
theorem euler_pentagonal_number_theorem (n : ℕ) :
  (∃ k : ℤ, (n = (k * (3 * k - 1)) / 2) ∧
  ((p_e n : ℤ) - (p_o n : ℤ) = (-1 : ℤ) ^ (Int.natAbs k) )) ∨
  ((¬ ∃ k : ℤ, n = (k * (3 * k - 1)) / 2 ) ∧
    ((p_e n : ℤ) - (p_o n : ℤ) = 0 )) :=
 sorry

/- Definition of the base of a partition into different parts

Let $n$ be a natural number. Let $S$ be a partition of $n$ into
different parts. The base of S is defined as its minimal element.-/

def base (S : Finset ℕ) (H : S.Nonempty) : ℕ := S.min' H

/- Definition of the slope of a partition into different parts

Let $n$ be a natural number. Let $S$ be a partition of $n$ into
different parts. Let $m$ be the maximal element of S.
The slope of S is the length of the longest interval
$[m-l,… ,m]$ contained in $S$. -/

/- WIP — temporarily commented out so doc-gen4 can build docs for the
declarations above. Re-enable once the proof compiles.

def slope (S : Finset ℕ) (H : S.Nonempty) : WithTop ℕ :=
  let m := S.max' H
  let L := (Icc' 0 m).filter (fun l => Icc' l m ⊆ S)
  have h1: m ∈ Icc' 0 m := by exact mem_Icc'_self m
  have h2: Icc' m m ⊆ S := by unfold m; sorry
  have hLm: m ∈ L := by unfold L; apply h1; rw[m,l] sorry
  have HL: L.Nonempty := by simp[hLm]
  m-(L.min' HL)+1
-/
