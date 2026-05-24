/* minimal_hybrid_stainless.scala  —  Stainless half of the minimal hybrid PNT proof.
 *
 * Stainless proves, about the executable Franklin map on partitions:
 *   - disjointness + trichotomy of the α/β/special classes   (auto; tedious in Lean)
 *   - franklin ∘ franklin = id                                 (modularly)
 * It ASSUMES the four hard structural lemmas (marked @extern) that it cannot
 * discharge; these are proved in `minimal_hybrid_lean.lean`. The bridge is the
 * human check that each @extern signature matches the cited Lean theorem.
 *
 * Verify:  stainless minimal_hybrid_stainless.scala
 */
import stainless.lang._
import stainless.collection._
import stainless.annotation._

object MinimalHybrid {

  // ---- partitions: strictly-sorted positive lists -------------------------
  def sorted(p: List[BigInt]): Boolean = p match {
    case Cons(x, t @ Cons(y, _)) => x < y && sorted(t)
    case _                       => true
  }
  def positive(p: List[BigInt]): Boolean = p match {
    case Cons(x, t) => x > 0 && positive(t)
    case Nil()      => true
  }
  def isPartition(p: List[BigInt]): Boolean = sorted(p) && positive(p)

  def base(p: List[BigInt]): BigInt = { require(!p.isEmpty); p.head }
  def maxOf(p: List[BigInt]): BigInt = {
    require(!p.isEmpty)
    p match { case Cons(x, Nil()) => x
              case Cons(x, t)     => val m = maxOf(t); if (x > m) x else m }
  }
  def runDown(p: List[BigInt], x: BigInt): BigInt = {
    require(x >= 0); decreases(x)
    if (p.contains(x)) { if (x >= 1) 1 + runDown(p, x - 1) else BigInt(1) } else BigInt(0)
  }.ensuring(_ >= 0)
  def slope(p: List[BigInt]): BigInt = { require(isPartition(p) && !p.isEmpty); runDown(p, maxOf(p)) }
  def inD(p: List[BigInt], x: BigInt): Boolean = {
    require(isPartition(p) && !p.isEmpty); maxOf(p) - slope(p) + 1 <= x && x <= maxOf(p)
  }

  // ---- the three classes --------------------------------------------------
  def isAlpha(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    !p.isEmpty && { val b = base(p); val s = slope(p); (b <= s && !inD(p, b)) || b + 1 <= s }
  }
  def isBeta(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    !p.isEmpty && { val b = base(p); val s = slope(p); (s < b && !inD(p, b)) || s + 2 <= b }
  }
  def isSpecial(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    p.isEmpty || { val b = base(p); val s = slope(p); inD(p, b) && (b == s || b == s + 1) }
  }

  // ---- the operations and Franklin's map ----------------------------------
  def insertS(p: List[BigInt], x: BigInt): List[BigInt] = p match {
    case Nil()      => Cons(x, Nil())
    case Cons(h, t) => if (x < h) Cons(x, p) else if (x == h) p else Cons(h, insertS(t, x))
  }
  def eraseE(p: List[BigInt], x: BigInt): List[BigInt] = p match {
    case Nil()      => Nil[BigInt]()
    case Cons(h, t) => if (h == x) t else Cons(h, eraseE(t, x))
  }
  def alphaOp(p: List[BigInt]): List[BigInt] = {
    require(isPartition(p) && isAlpha(p)); val b = base(p); val m = maxOf(p)
    insertS(eraseE(eraseE(p, b), m - b + 1), m + 1)
  }
  def betaOp(p: List[BigInt]): List[BigInt] = {
    require(isPartition(p) && isBeta(p)); val s = slope(p); val m = maxOf(p)
    eraseE(insertS(insertS(p, m - s), s), m)
  }
  def franklin(p: List[BigInt]): List[BigInt] = {
    require(isPartition(p))
    if (isAlpha(p)) alphaOp(p) else if (isBeta(p)) betaOp(p) else p
  }

  // ---- ASSUMED here, PROVED in Lean (bridge) ------------------------------
  // ↔ Aristotle/Lemmas.lean : alphaOp_mem_DPbeta
  @extern def alpha_in_beta(p: List[BigInt]): Boolean = {
    require(isPartition(p) && isAlpha(p)); true
  }.ensuring(_ => isPartition(alphaOp(p)) && isBeta(alphaOp(p)))
  // ↔ Aristotle/Lemmas.lean : betaOp_mem_DPalpha
  @extern def beta_in_alpha(p: List[BigInt]): Boolean = {
    require(isPartition(p) && isBeta(p)); true
  }.ensuring(_ => isPartition(betaOp(p)) && isAlpha(betaOp(p)))
  // ↔ Aristotle/Lemmas.lean : betaOp_alphaOp   (membership precond. makes the
  //    nested call well-formed; supplied by alpha_in_beta at the use site)
  @extern def beta_alpha_id(p: List[BigInt]): Boolean = {
    require(isPartition(p) && isAlpha(p) && isPartition(alphaOp(p)) && isBeta(alphaOp(p))); true
  }.ensuring(_ => betaOp(alphaOp(p)) == p)
  // ↔ Aristotle/Lemmas.lean : alphaOp_betaOp
  @extern def alpha_beta_id(p: List[BigInt]): Boolean = {
    require(isPartition(p) && isBeta(p) && isPartition(betaOp(p)) && isAlpha(betaOp(p))); true
  }.ensuring(_ => alphaOp(betaOp(p)) == p)

  // ---- PROVED by Stainless ------------------------------------------------
  /** classes are pairwise disjoint (Lemma 11). */
  def disjoint(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    !(isAlpha(p) && isBeta(p)) && !(isAlpha(p) && isSpecial(p)) && !(isBeta(p) && isSpecial(p))
  }.holds

  /** every nonempty partition is in exactly one class (Lemma 12). */
  def trichotomy(p: List[BigInt]): Boolean = {
    require(isPartition(p) && !p.isEmpty)
    (isAlpha(p) && !isBeta(p) && !isSpecial(p)) ||
    (!isAlpha(p) && isBeta(p) && !isSpecial(p)) ||
    (!isAlpha(p) && !isBeta(p) && isSpecial(p))
  }.holds

  /** Franklin's map is an involution (Lemmas 18–19), from the four assumptions. */
  def franklin_involution(p: List[BigInt]): Boolean = {
    require(isPartition(p))
    if (isAlpha(p)) {
      alpha_in_beta(p); beta_alpha_id(p); disjoint(alphaOp(p)); franklin(franklin(p)) == p
    } else if (isBeta(p)) {
      beta_in_alpha(p); alpha_beta_id(p); disjoint(betaOp(p)); franklin(franklin(p)) == p
    } else franklin(franklin(p)) == p
  }.holds
}
