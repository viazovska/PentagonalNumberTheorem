/*
 * Franklin's involution for Euler's Pentagonal Number Theorem
 * ===========================================================
 *
 * A Stainless (Viktor Kuncak / EPFL LARA) formalization, ported from the Lean 4
 * development in this repository:
 *
 *   - Aristotle/Defs.lean      (partBase, partMax, partSlope, partSlopeSet,
 *                               DPalpha, DPbeta, DPspecial, alphaOp, betaOp)
 *   - Aristotle/Lemmas.lean    (Lemmas 16–19: Franklin's involution)
 *   - blueprint/src/content_v2.tex (Definitions 9, 10, 15)
 *
 * Run with:   stainless FranklinInvolution.scala
 * (or via sbt-stainless). The functions ending in `.holds` are the proof
 * obligations Stainless will attempt to discharge with its SMT back-end.
 *
 * ---------------------------------------------------------------------------
 * Representation of a partition
 * ---------------------------------------------------------------------------
 * The Lean development uses `Finset ℕ`. Stainless's built-in `Set` is an
 * uninterpreted SMT set: you cannot fold a sum over it, nor compute min/max.
 * We therefore represent a partition of an integer into DISTINCT POSITIVE parts
 * as a strictly increasing `List[BigInt]`:
 *
 *     isPartition(p)  ==  strictly sorted ascending  &&  every element > 0
 *
 * Strict sortedness gives distinctness for free, makes `min = head`,
 * `max = last`, and lets us define a recursive, verifiable `sum`. `BigInt` is
 * used throughout (rather than `Int`) so the SMT solver reasons over unbounded
 * integers, exactly as Lean's `ℕ`/`ℤ`.
 */

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object FranklinInvolution {

  /* =========================================================================
   * 1. The partition data structure: strictly-sorted lists of positive ints
   * ========================================================================= */

  /** `p` is sorted strictly ascending (hence its elements are distinct). */
  def isSortedStrict(p: List[BigInt]): Boolean = p match {
    case Nil()        => true
    case Cons(x, xs)  => xs match {
      case Nil()       => true
      case Cons(y, _)  => x < y && isSortedStrict(xs)
    }
  }

  /** Every element of `p` is a positive part. */
  def allPositive(p: List[BigInt]): Boolean = p match {
    case Nil()       => true
    case Cons(x, xs) => x > 0 && allPositive(xs)
  }

  /** A valid partition into distinct positive parts. Mirrors membership in
    * `DP n` (Aristotle/Defs.lean), minus the fixed total `n` which we track
    * separately via `sum`. */
  def isPartition(p: List[BigInt]): Boolean =
    isSortedStrict(p) && allPositive(p)

  /** The integer that `p` partitions: ∑_{x ∈ p} x.  (Lean: `S.sum id`.) */
  def sum(p: List[BigInt]): BigInt = p match {
    case Nil()       => BigInt(0)
    case Cons(x, xs) => x + sum(xs)
  }

  /* =========================================================================
   * 2. Sorted insert / erase  (the Finset.insert / Finset.erase of Lean)
   * ========================================================================= */

  /** Insert `x` keeping the list strictly sorted; a no-op if `x` is present.
    * Corresponds to `insert x S` on a `Finset`. */
  def insertSorted(p: List[BigInt], x: BigInt): List[BigInt] = {
    p match {
      case Nil()       => Cons(x, Nil())
      case Cons(h, t)  =>
        if (x < h)      Cons(x, p)
        else if (x == h) p
        else            Cons(h, insertSorted(t, x))
    }
  }.ensuring(res =>
    // insertSorted preserves the partition invariant when x is positive.
    (isPartition(p) && x > 0) ==> isPartition(res))

  /** Remove `x` from the list. Corresponds to `S.erase x` on a `Finset`. */
  def erase(p: List[BigInt], x: BigInt): List[BigInt] = {
    p match {
      case Nil()       => Nil[BigInt]()
      case Cons(h, t)  => if (h == x) t else Cons(h, erase(t, x))
    }
  }.ensuring(res =>
    isPartition(p) ==> isPartition(res))

  /* =========================================================================
   * 3. base, max, slope, slope set   (Definition 9 / Aristotle/Defs.lean)
   * ========================================================================= */

  /** `base(S) = min(S)`. For a sorted list this is the head. (Lean: `partBase`.) */
  def base(p: List[BigInt]): BigInt = {
    require(!p.isEmpty)
    p.head
  }

  /** `max(S)` = the last (largest) element. (Lean: `partMax`.)
    * The postcondition records that the max of a positive-element list is
    * itself positive — needed so `slope`/`runDownFrom` see a non-negative
    * starting point. */
  def maxOf(p: List[BigInt]): BigInt = {
    require(!p.isEmpty)
    p match {
      case Cons(x, Nil()) => x
      case Cons(_, t)     => maxOf(t)
    }
  }.ensuring(res => allPositive(p) ==> (res > 0))

  /** Length of the consecutive run `x, x-1, x-2, …` contained in `p`,
    * counting downward from `x`. (Lean: `consecutiveTopRun`.) */
  def runDownFrom(p: List[BigInt], x: BigInt): BigInt = {
    require(x >= 0)
    decreases(x)
    if (p.contains(x)) {
      if (x >= 1) 1 + runDownFrom(p, x - 1) else BigInt(1)
    } else BigInt(0)
  }.ensuring(_ >= 0)

  /** `slope(S)` = length of the maximal top-consecutive run from max(S) down.
    * (Lean: `partSlope`.) */
  def slope(p: List[BigInt]): BigInt = {
    require(isPartition(p) && !p.isEmpty)
    runDownFrom(p, maxOf(p))
  }

  /** Membership in the slope set `D = {max−slope+1, …, max}`, i.e. `x ∈ D`.
    * (Lean: `x ∈ partSlopeSet S`, encoded arithmetically as in Defs.lean.) */
  def inSlopeSet(p: List[BigInt], x: BigInt): Boolean = {
    require(isPartition(p) && !p.isEmpty)
    val m = maxOf(p)
    val s = slope(p)
    m - s + 1 <= x && x <= m
  }

  /* =========================================================================
   * 4. Criteria checkers for the three classes 𝒫_α, 𝒫_β, 𝒫_special
   *    (Definition 10 / DPalpha, DPbeta, DPspecial in Aristotle/Defs.lean)
   * ========================================================================= */

  /** `S ∈ 𝒫_α`:  (b ≤ s ∧ b ∉ D) ∨ b ≤ s − 1   (b = base, s = slope, D = slope set). */
  def isAlpha(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    if (p.isEmpty) false
    else {
      val b = base(p)
      val s = slope(p)
      (b <= s && !inSlopeSet(p, b)) || (b + 1 <= s)
    }
  }

  /** `S ∈ 𝒫_β`:  (b > s ∧ b ∉ D) ∨ b ≥ s + 2. */
  def isBeta(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    if (p.isEmpty) false
    else {
      val b = base(p)
      val s = slope(p)
      (s < b && !inSlopeSet(p, b)) || (s + 2 <= b)
    }
  }

  /** `S ∈ 𝒫_special`:  S = ∅, or (b ∈ D ∧ (b = s ∨ b = s + 1)). */
  def isSpecial(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    if (p.isEmpty) true
    else {
      val b = base(p)
      val s = slope(p)
      inSlopeSet(p, b) && (b == s || b == s + 1)
    }
  }

  /* =========================================================================
   * 5. The operations α and β   (Definition 15 / alphaOp, betaOp in Defs.lean)
   * ========================================================================= */

  /** `α(S) = (S \ {b, m−b+1}) ∪ {m+1}`,  with b = base(S), m = max(S).
    * The `ensuring` clause IS the specification: on a 𝒫_α-input, α produces a
    * valid partition that lies in 𝒫_β and partitions the same integer
    * (Lemma 16 `alphaOp_mem_DPbeta` + sum preservation). (Lean: `alphaOp`.) */
  def alphaOp(p: List[BigInt]): List[BigInt] = {
    require(isPartition(p) && isAlpha(p))
    val b = base(p)
    val m = maxOf(p)
    insertSorted(erase(erase(p, b), m - b + 1), m + 1)
  }.ensuring(res => isPartition(res) && isBeta(res) && sum(res) == sum(p))

  /** `β(S) = (S ∪ {s, m−s}) \ {m}`,  with s = slope(S), m = max(S).
    * Dually, on a 𝒫_β-input, β produces a valid partition in 𝒫_α with the same
    * sum (Lemma 17 `betaOp_mem_DPalpha` + sum preservation). (Lean: `betaOp`.) */
  def betaOp(p: List[BigInt]): List[BigInt] = {
    require(isPartition(p) && isBeta(p))
    val s = slope(p)
    val m = maxOf(p)
    erase(insertSorted(insertSorted(p, m - s), s), m)
  }.ensuring(res => isPartition(res) && isAlpha(res) && sum(res) == sum(p))

  /* =========================================================================
   * 6. Franklin's involution: dispatch on the class of S
   * ========================================================================= */

  /** Franklin's map F: apply α on 𝒫_α, β on 𝒫_β, and idle on 𝒫_special.
    * The three classes partition 𝒫(n) (Lemma `DP_eq_union`), so exactly one
    * branch fires. F is an involution that pairs an even partition with an odd
    * one, fixing only the (single) special partition — the combinatorial heart
    * of the Pentagonal Number Theorem. */
  def franklinInvolution(p: List[BigInt]): List[BigInt] = {
    require(isPartition(p))
    if (isAlpha(p))      alphaOp(p)
    else if (isBeta(p))  betaOp(p)
    else                 p              // special / idle case
  }

  /* =========================================================================
   * 7. Verification targets (proof obligations for Stainless)
   * ========================================================================= */

  /** The three classes are mutually exclusive — no partition is both α and β.
    * (Lean: `DPalpha_inter_DPbeta`.) */
  def alphaBetaDisjoint(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    !(isAlpha(p) && isBeta(p))
  }.holds

  /** α and β cover the non-special, nonempty partitions: every nonempty
    * partition lies in exactly one of α, β, special.
    * (Lean: `DP_eq_union` together with disjointness.) */
  def classTrichotomy(p: List[BigInt]): Boolean = {
    require(isPartition(p) && !p.isEmpty)
    (isAlpha(p) && !isBeta(p) && !isSpecial(p)) ||
    (!isAlpha(p) && isBeta(p) && !isSpecial(p)) ||
    (!isAlpha(p) && !isBeta(p) && isSpecial(p))
  }.holds

  /** F preserves the integer being partitioned (α and β are sum-preserving
    * rewrites: −b−(m−b+1)+(m+1) = 0 and +s+(m−s)−m = 0). */
  def franklinPreservesSum(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    sum(franklinInvolution(p)) == sum(p)
  }.holds

  /** F maps partitions to partitions. */
  def franklinClosed(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    isPartition(franklinInvolution(p))
  }.holds

  // NOTE: "α lands in 𝒫_β" (Lemma 16) and "β lands in 𝒫_α" (Lemma 17) are now
  // expressed directly as the `ensuring` postconditions of `alphaOp` / `betaOp`
  // above. They are the two remaining hard, induction-requiring obligations;
  // everything below is proved *modularly* by assuming those contracts.

  /** THE involution property: F ∘ F = id  (Lemmas 18–19 / β∘α = id, α∘β = id,
    * plus the idle case). This is the central theorem. */
  def franklinIsInvolution(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    franklinInvolution(franklinInvolution(p)) == p
  }.holds
}
