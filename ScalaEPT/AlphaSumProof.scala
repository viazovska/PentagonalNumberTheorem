/*
 * Experiment: discharging α's postcondition by hand with @induct lemmas.
 * ======================================================================
 * Focused, self-contained file (re-declares the minimal defs) that attempts to
 * PROVE  sum(alphaOp(p)) == sum(p)  for p ∈ 𝒫_α — the "easy half" of alphaOp's
 * postcondition. The point is to measure how much inductive scaffolding the
 * SMT back-end actually needs.  Run:  stainless ScalaEPT/AlphaSumProof.scala
 *
 * `maxOf` is defined here as a FOLD-maximum (not "last element"): for a sorted
 * partition the value is identical, but the fold version lets `leMax` be a clean
 * @induct lemma that needs no sortedness reasoning.
 */

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object AlphaSumProof {

  /* ---- partition core (mirrors FranklinInvolution.scala) ---- */

  def isSortedStrict(p: List[BigInt]): Boolean = p match {
    case Nil()       => true
    case Cons(x, xs) => xs match {
      case Nil()      => true
      case Cons(y, _) => x < y && isSortedStrict(xs)
    }
  }
  def allPositive(p: List[BigInt]): Boolean = p match {
    case Nil()       => true
    case Cons(x, xs) => x > 0 && allPositive(xs)
  }
  def isPartition(p: List[BigInt]): Boolean = isSortedStrict(p) && allPositive(p)

  def sum(p: List[BigInt]): BigInt = p match {
    case Nil()       => BigInt(0)
    case Cons(x, xs) => x + sum(xs)
  }

  def insertSorted(p: List[BigInt], x: BigInt): List[BigInt] = p match {
    case Nil()      => Cons(x, Nil())
    case Cons(h, t) =>
      if (x < h) Cons(x, p) else if (x == h) p else Cons(h, insertSorted(t, x))
  }
  def erase(p: List[BigInt], x: BigInt): List[BigInt] = p match {
    case Nil()      => Nil[BigInt]()
    case Cons(h, t) => if (h == x) t else Cons(h, erase(t, x))
  }

  def base(p: List[BigInt]): BigInt = { require(!p.isEmpty); p.head }

  /** fold-maximum (≥ every element by construction) */
  def maxOf(p: List[BigInt]): BigInt = {
    require(!p.isEmpty)
    p match {
      case Cons(x, Nil()) => x
      case Cons(x, t)     => val mt = maxOf(t); if (x > mt) x else mt
    }
  }

  def runDownFrom(p: List[BigInt], x: BigInt): BigInt = {
    require(x >= 0)
    decreases(x)
    if (p.contains(x)) { if (x >= 1) 1 + runDownFrom(p, x - 1) else BigInt(1) }
    else BigInt(0)
  }.ensuring(_ >= 0)

  def slope(p: List[BigInt]): BigInt = {
    require(isPartition(p) && !p.isEmpty)
    runDownFrom(p, maxOf(p))
  }
  def inSlopeSet(p: List[BigInt], x: BigInt): Boolean = {
    require(isPartition(p) && !p.isEmpty)
    maxOf(p) - slope(p) + 1 <= x && x <= maxOf(p)
  }
  def isAlpha(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    if (p.isEmpty) false
    else {
      val b = base(p); val s = slope(p)
      (b <= s && !inSlopeSet(p, b)) || (b + 1 <= s)
    }
  }

  def alphaOp(p: List[BigInt]): List[BigInt] = {
    require(isPartition(p) && isAlpha(p))
    val b = base(p); val m = maxOf(p)
    insertSorted(erase(erase(p, b), m - b + 1), m + 1)
  }

  /* ======================================================================
   * Inductive helper lemmas
   * ====================================================================== */

  /** sum after erasing a present element drops by exactly that element.
    * Manual recursion: in the head-match case there is no recursive call, so we
    * never invoke the IH where its `contains` precondition would fail. */
  def sumErase(l: List[BigInt], x: BigInt): Boolean = {
    require(l.contains(x))
    decreases(l)
    l match {
      case Cons(h, t) =>
        if (h == x) sum(erase(l, x)) == sum(l) - x
        else { sumErase(t, x); sum(erase(l, x)) == sum(l) - x }
    }
  }.holds

  /** sum after inserting an absent element rises by exactly that element. */
  @induct
  def sumInsert(l: List[BigInt], x: BigInt): Boolean = {
    require(!l.contains(x))
    sum(insertSorted(l, x)) == sum(l) + x
  }.holds

  /** every element is ≤ the (fold-)max. Manual recursion for the same reason. */
  def leMax(l: List[BigInt], y: BigInt): Boolean = {
    require(!l.isEmpty && l.contains(y))
    decreases(l)
    l match {
      case Cons(x, Nil()) => y <= maxOf(l)
      case Cons(x, t)     =>
        if (y == x) y <= maxOf(l) else { leMax(t, y); y <= maxOf(l) }
    }
  }.holds

  /** nothing above the max is present. */
  def aboveMaxNotIn(l: List[BigInt], z: BigInt): Boolean = {
    require(!l.isEmpty && z > maxOf(l))
    !l.contains(z) because { if (l.contains(z)) leMax(l, z) else true }
  }.holds

  /** erasing one element keeps any *other* present element. Manual recursion. */
  def eraseKeepsOther(l: List[BigInt], x: BigInt, y: BigInt): Boolean = {
    require(l.contains(y) && x != y)
    decreases(l)
    l match {
      case Cons(h, t) =>
        if (h == y) erase(l, x).contains(y)
        else { eraseKeepsOther(t, x, y); erase(l, x).contains(y) }
    }
  }.holds

  /** erasing never introduces a previously-absent element. */
  @induct
  def eraseNotContains(l: List[BigInt], x: BigInt, z: BigInt): Boolean = {
    require(!l.contains(z))
    !erase(l, x).contains(z)
  }.holds

  /** the head of a nonempty list is an element of it. */
  def headContains(l: List[BigInt]): Boolean = {
    require(!l.isEmpty)
    l.contains(l.head)
  }.holds

  /** every position in the top-run is actually present:
    * if `d < runDownFrom(p, x)` then `x - d ∈ p`.  Hand-written induction on x. */
  def runMem(p: List[BigInt], x: BigInt, d: BigInt): Boolean = {
    require(x >= 0 && d >= 0 && d < runDownFrom(p, x))
    decreases(x)
    if (d == 0) p.contains(x - d)
    else { runMem(p, x - 1, d - 1); p.contains(x - d) }
  }.holds

  /* ======================================================================
   * THE TARGET: sum preservation of α
   * ====================================================================== */

  /** m ≥ 2b for a 𝒫_α-partition (blueprint Lemma 16, Step 0). This is the
    * genuinely hard structural fact; left as a stated obligation here so we can
    * see whether the *sum* equation closes once it is assumed. */
  def mGe2b(p: List[BigInt]): Boolean = {
    require(isPartition(p) && isAlpha(p))
    maxOf(p) >= 2 * base(p)
  }.holds

  def alphaSumPreserved(p: List[BigInt]): Boolean = {
    require(isPartition(p) && isAlpha(p))
    val b = base(p)
    val m = maxOf(p)
    // assemble the facts, then state the goal
    headContains(p) &&                        // b ∈ p
    runMem(p, m, b - 1) &&                     // m-b+1 ∈ p  (uses b-1 < slope)
    mGe2b(p) &&                                // ⇒ m-b+1 = m-b+1 > b, distinct from b
    eraseKeepsOther(p, b, m - b + 1) &&        // m-b+1 ∈ erase(p, b)
    aboveMaxNotIn(p, m + 1) &&                 // m+1 ∉ p
    eraseNotContains(p, b, m + 1) &&           // m+1 ∉ erase(p, b)
    eraseNotContains(erase(p, b), m - b + 1, m + 1) && // m+1 ∉ erase(erase(p,b), m-b+1)
    sumErase(p, b) &&                          // sum(erase(p,b)) = sum(p) - b
    sumErase(erase(p, b), m - b + 1) &&        // ... - (m-b+1)
    sumInsert(erase(erase(p, b), m - b + 1), m + 1) && // ... + (m+1)
    sum(alphaOp(p)) == sum(p)
  }.holds
}
