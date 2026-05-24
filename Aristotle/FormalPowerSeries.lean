import Mathlib
import Aristotle.Defs
import Aristotle.Helpers
import Aristotle.Lemmas
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology
set_option maxHeartbeats 4000000



/-! # Pentagonal Number Theorem — Formal Power Series Statements
This file contains the formal power series identities from the source document
"Pentagonal Number Theorem" by JC, PM, MV (May 11, 2026).
These results connect the combinatorial content (proved in `Lemmas.lean`)
to the algebraic identities involving generating functions.
-/
/-! ## Section 1: Generating function for p(n)

The partition function `p(n)` counts the partitions of `n` with repetition
allowed. Mathlib provides the structure `Nat.Partition n` together with a
`Fintype` instance, so we identify `p(n) := Fintype.card (Nat.Partition n)`.

Mathlib's `Nat.Partition.genFun` constructs, for any character `f`, the
power series whose `n`-th coefficient is `∑_{p ∈ n.Partition} ∏_{i ∈ p} f i #i`.
For `f = (fun _ _ => 1)` (the trivial character), each partition contributes
`1`, so the `n`-th coefficient is exactly the count `p(n)`. The product
representation comes from `Nat.Partition.genFun_eq_tprod`.
-/

/-- The unrestricted partition count `p(n)`: the number of ways to write
`n` as a sum of positive integers (with repetition allowed, order ignored). -/
noncomputable def p_count (n : ℕ) : ℕ := Fintype.card n.Partition

/-- The generating function for `p_count`: a formal power series in `ℤ⟦X⟧`
whose coefficients are the partition counts. -/
noncomputable def pGenFun : ℤ⟦X⟧ := Nat.Partition.genFun fun _ _ => (1 : ℤ)

/--
**Lemma 3 (combinatorial side).** The `n`-th coefficient of the partition
generating function is `p(n)`.
-/
theorem coeff_pGenFun_eq_p_count (n : ℕ) :
    (coeff n) pGenFun = (p_count n : ℤ) := by
  simp [pGenFun, Nat.Partition.coeff_genFun, p_count, Finsupp.prod_fun_one]

/--
**Lemma 3 (product side).** The generating function equals the formal product
`∏_{k≥1} (1 + X^k + X^{2k} + ...)` (the geometric series expansion of each
`(1 - X^k)^{-1}`). The product is taken in the X-adic topology on `ℤ⟦X⟧`,
where it converges (each `[X^n]` only sees finitely many factors).
-/
theorem pGenFun_eq_prod :
    pGenFun
      = ∏' i, ((1 : ℤ⟦X⟧) + ∑' j, (1 : ℤ) • X^((i+1)*(j+1))) :=
  Nat.Partition.genFun_eq_tprod (fun _ _ => (1 : ℤ))
/-! ## Section 1: Product expansion (Lemma 5)

The coefficient of `X^n` in the infinite product `∏_{k≥1}(1 - X^k)` equals
`p_e(n) - p_o(n)`. We work with the truncated product `∏_{k=1}^{n}(1 - X^k)`:
for the coefficient `[X^n]`, factors with `k > n` contribute the identity
modulo `X^{n+1}`, so the truncation does not lose information.

The argument has two clean halves:

* **5a** (`coeff_prod_eq_signed_partition_sum`) — Expanding the product
  identifies `[X^n] ∏_{k=1}^{n}(1 - X^k)` with the signed count
  `∑_{S ∈ DP n} (-1)^|S|`. *(Combinatorial expansion; proved below.)*

* **5b** (`signed_partition_sum_eq_pe_sub_po`) — That signed count equals
  `p_e(n) - p_o(n)` by splitting partitions by the parity of their length.

The main statement (`coeff_prod_eq_pe_sub_po`) is then immediate.
-/

/--
**Lemma 5a (combinatorial expansion).** The coefficient of `X^n` in the
truncated product `∏_{k=1}^{n}(1 - X^k)` equals `∑_{S ∈ DP n} (-1)^|S|`.

**Proof sketch.** Rewrite each factor as `1 + (-X^k)` and use the classical
expansion of a product of `1 + a_k` over subsets:
`∏_{k ∈ {1,…,n}} (1 + (-X^k)) = ∑_{T ⊆ {1,…,n}} ∏_{k ∈ T} (-X^k)`
`                            = ∑_{T ⊆ {1,…,n}} (-1)^|T| · X^{T.sum id}`.
Extracting the coefficient of `X^n` keeps only those `T` with `T.sum id = n`;
these are exactly the elements of `DP n`. The Mathlib tools needed are
`Finset.prod_one_add` (product of `1 + a_k` as a sum over subsets), linearity
of `PowerSeries.coeff` over a finite sum, and `PowerSeries.coeff_X_pow`
(coefficient of `X^m` is `1` iff the index matches, else `0`).
-/
theorem coeff_prod_eq_signed_partition_sum (n : ℕ) :
    (coeff n) (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧)) =
      ∑ S ∈ DP n, (-1 : ℤ)^S.card := by
  -- Expand the product: ∏ (1 - X^k) = ∑_{T ⊆ Icc 1 n} ∏_{k ∈ T} (-X^k).
  have hexpand : (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧))
      = ∑ T ∈ (Finset.Icc 1 n).powerset, ∏ k ∈ T, (-(X^k) : ℤ⟦X⟧) := by
    rw [show (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧))
          = (∏ k ∈ Finset.Icc 1 n, (1 + (-(X^k)) : ℤ⟦X⟧))
        from Finset.prod_congr rfl (fun k _ => by ring)]
    exact Finset.prod_one_add _
  rw [hexpand, map_sum]
  -- For each subset T, simplify the inner product:
  --   ∏_{k ∈ T} (-X^k) = (-1)^|T| · X^(T.sum id),
  -- so coeff n of it is (-1)^|T| when T.sum id = n, else 0.
  have hterm : ∀ T ∈ (Finset.Icc 1 n).powerset,
      (coeff n) (∏ k ∈ T, (-(X^k) : ℤ⟦X⟧))
        = if T.sum id = n then (-1 : ℤ)^T.card else 0 := by
    intro T _
    rw [Finset.prod_neg,
        show (∏ x ∈ T, (X : ℤ⟦X⟧)^x) = X^(T.sum id) from
          Finset.prod_pow_eq_pow_sum T id X,
        show ((-1 : ℤ⟦X⟧))^T.card = (C ((-1 : ℤ)^T.card) : ℤ⟦X⟧) by
          rw [map_pow]; simp,
        coeff_C_mul_X_pow]
    congr 1
    exact propext eq_comm
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- The filter `T.sum id = n` over `(Icc 1 n).powerset` is exactly `DP n` (by definition).
  rfl

/--
**Lemma 5b (parity split).** The signed partition sum equals `p_e(n) - p_o(n)`.

The sum splits over the partition `DP n = DPeven n ⊔ DPodd n`. On `DPeven`,
`(-1)^|S| = 1`; on `DPodd`, `(-1)^|S| = -1`. The pieces give `|DPeven|` and
`-|DPodd|`, i.e. `p_e(n)` and `-p_o(n)`.
-/
theorem signed_partition_sum_eq_pe_sub_po (n : ℕ) :
    ∑ S ∈ DP n, (-1 : ℤ)^S.card = (pe n : ℤ) - po n := by
  have h_sign : ∀ S ∈ DP n,
      (-1 : ℤ)^S.card = if S.card % 2 = 0 then (1 : ℤ) else -1 := by
    intro S _
    rcases Nat.mod_two_eq_zero_or_one S.card with h | h
    · rw [if_pos h]; exact (Nat.even_iff.mpr h).neg_one_pow
    · rw [if_neg (by omega : ¬ S.card % 2 = 0)]
      exact (Nat.odd_iff.mpr h).neg_one_pow
  rw [Finset.sum_congr rfl h_sign, Finset.sum_ite]
  have hev : (DP n).filter (fun S => S.card % 2 = 0) = DPeven n := rfl
  have hod : (DP n).filter (fun S => ¬ S.card % 2 = 0) = DPodd n := by
    apply Finset.filter_congr; intro S _; omega
  rw [hev, hod, Finset.sum_const, Finset.sum_const]
  simp only [pe, po]
  ring

/--
**Lemma 5 (Source).** For each `n`, the coefficient of `X^n` in the
truncated product `∏_{k=1}^{n}(1 - X^k)` in `ℤ⟦X⟧` equals `p_e(n) - p_o(n)`.

(The truncation matches the infinite product `∏_{k≥1}(1 - X^k)` on this
coefficient because factors with `k > n` are `≡ 1 mod X^{n+1}`.)
-/
theorem coeff_prod_eq_pe_sub_po (n : ℕ) :
    (coeff n) (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧)) = (pe n : ℤ) - po n := by
  rw [coeff_prod_eq_signed_partition_sum, signed_partition_sum_eq_pe_sub_po]
/-! ## Section 2: Pentagonal Number Theorem (Theorem 7)

Euler's Pentagonal Number Theorem in formal-power-series form:
$$
  \prod_{i=1}^{\infty}(1 - X^i)
  \;=\; \sum_{k \in \mathbb{Z}} (-1)^k\, X^{(3k ^ 2 - k)/2}
  \;=\; 1 + \sum_{k \geq 1} (-1)^k\bigl(X^{(3k ^ 2-k)/2} + X^{(3k ^ 2+k)/2}\bigr).
$$
For the coefficient of `X^n`, only factors `(1 - X^k)` with `k ≤ n` matter
(those with `k > n` are `≡ 1 mod X^{n+1}`), so we work with the truncated
product `∏_{k=1}^{n}(1 - X^k)`.

The coefficient-by-coefficient identity is the conjunction of four cases
matching Aristotle's `pe_minus_po_*` lemmas. Each case is a one-line
composition: Lemma 5 (`coeff_prod_eq_pe_sub_po`) turns the coefficient into
`p_e(n) - p_o(n)`, which the matching `pe_minus_po_*` lemma evaluates.
-/

/--
**PNT (Euler), zero case.** `[X^0] ∏_{k=1}^{0}(1 - X^k) = 1`.
(The product is empty, so this is just `coeff 0 1 = 1`; we state it via
`coeff_prod_eq_pe_sub_po` for uniformity with the other cases.)
-/
theorem coeff_prod_pentagonal_zero :
    (coeff 0) (∏ k ∈ Finset.Icc 1 0, (1 - X^k : ℤ⟦X⟧)) = 1 := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_zero

/--
**PNT (Euler), non-pentagonal case.** For `n ≥ 1` with `2n` not of the
form `3k² - k` nor `3k² + k` for any `k ≥ 1`,
`[X^n] ∏_{k=1}^{n}(1 - X^k) = 0`.
-/
theorem coeff_prod_pentagonal_nonpent (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 - k)
    (h2 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 + k) :
    (coeff n) (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧)) = 0 := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_nonpent n hn h1 h2

/--
**PNT (Euler), pentagonal `(3k²-k)/2` case.** If `2n = 3k² - k` for some
`k ≥ 1` (equivalently, `n = (3k²-k)/2`), then
`[X^n] ∏_{k'=1}^{n}(1 - X^{k'}) = (-1)^k`.
-/
theorem coeff_prod_pentagonal_minus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 - k) :
    (coeff n) (∏ k' ∈ Finset.Icc 1 n, (1 - X^k' : ℤ⟦X⟧)) = (-1)^k := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_pent_minus n k hk hn

/--
**PNT (Euler), pentagonal `(3k²+k)/2` case.** If `2n = 3k² + k` for some
`k ≥ 1` (equivalently, `n = (3k²+k)/2`), then
`[X^n] ∏_{k'=1}^{n}(1 - X^{k'}) = (-1)^k`.
-/
theorem coeff_prod_pentagonal_plus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 + k) :
    (coeff n) (∏ k' ∈ Finset.Icc 1 n, (1 - X^k' : ℤ⟦X⟧)) = (-1)^k := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_pent_plus n k hk hn

/--
**PNT (Euler), Maryna's unified form.** For every `n`, either `n` is a
generalized pentagonal number `k(3k-1)/2` for some `k ∈ ℤ` — in which case
`p_e(n) - p_o(n) = (-1)^|k|` — or it is not, in which case the difference
vanishes.

This repackages the four cases (`pe_minus_po_zero`, `pe_minus_po_pent_minus`,
`pe_minus_po_pent_plus`, `pe_minus_po_nonpent`) under a single integer index:
`k = 0` gives `n = 0`, `k ≥ 1` gives the `(3k²-k)/2` family, and `k ≤ -1`
(with `m = |k|`) gives the `(3m²+m)/2` family.
-/
theorem euler_pentagonal_number_theorem_packaged (n : ℕ) :
  (∃ k : ℤ, (n = (k * (3 * k - 1)) / 2) ∧
  ((pe n : ℤ) - (po n : ℤ) = (-1 : ℤ) ^ (Int.natAbs k) )) ∨
  ((¬ ∃ k : ℤ, n = (k * (3 * k - 1)) / 2 ) ∧
    ((pe n : ℤ) - (po n : ℤ) = 0 )) := by
  -- `n = k(3k-1)/2` ↔ `2n = k(3k-1)`, since `k(3k-1)` is always even.
  have key : ∀ k : ℤ, ((n : ℤ) = k * (3 * k - 1) / 2) ↔ (2 * (n : ℤ) = k * (3 * k - 1)) := by
    intro k
    have hdvd : (2 : ℤ) ∣ k * (3 * k - 1) := by
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact ⟨m * (3 * (m + m) - 1), by ring⟩
      · exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
    constructor
    · intro h; rw [h, mul_comm]; exact Int.ediv_mul_cancel hdvd
    · intro h; rw [← h, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  by_cases hP : ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2
  · -- Pentagonal case: produce the witnessing `k` and evaluate the sign.
    left
    obtain ⟨k, hk⟩ := hP
    refine ⟨k, hk, ?_⟩
    rw [key] at hk  -- hk : 2 * ↑n = k * (3 * k - 1)
    rcases lt_trichotomy k 0 with hneg | hzero | hpos
    · -- k < 0 : set j = |k|, then 2n = 3j² + j (the "plus" family).
      set j := k.natAbs with hj
      have hkj : k = -(j : ℤ) := by rw [hj, Int.ofNat_natAbs_of_nonpos hneg.le]; ring
      have hj1 : 1 ≤ j := Int.natAbs_pos.mpr (ne_of_lt hneg)
      have hnat : 2 * n = 3 * j ^ 2 + j := by
        have : (2 * (n : ℤ)) = 3 * (j : ℤ) ^ 2 + (j : ℤ) := by rw [hk, hkj]; ring
        exact_mod_cast this
      exact pe_minus_po_pent_plus n j hj1 hnat
    · -- k = 0 : then n = 0.
      subst hzero
      have hn0 : n = 0 := by simpa using hk
      subst hn0
      simpa using pe_minus_po_zero
    · -- k > 0 : set j = k, then 2n = 3j² - j (the "minus" family).
      set j := k.natAbs with hj
      have hkj : k = (j : ℤ) := (Int.natAbs_of_nonneg hpos.le).symm
      have hj1 : 1 ≤ j := Int.natAbs_pos.mpr (ne_of_gt hpos)
      have hnat : 2 * n = 3 * j ^ 2 - j := by
        have hz : 2 * n + j = 3 * j ^ 2 := by
          have : (2 * (n : ℤ)) + (j : ℤ) = 3 * (j : ℤ) ^ 2 := by rw [hk, hkj]; ring
          exact_mod_cast this
        omega
      exact pe_minus_po_pent_minus n j hj1 hnat
  · -- Non-pentagonal case: discharge `nonpent`'s hypotheses by contraposition.
    right
    refine ⟨hP, ?_⟩
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd ⟨0, by simp [h]⟩ hP
      · exact h
    apply pe_minus_po_nonpent n hn1
    · intro k hk hcontra
      apply hP
      refine ⟨(k : ℤ), ?_⟩
      rw [key]
      have hle : k ≤ 3 * k ^ 2 := by nlinarith [hk]
      have : (2 * (n : ℤ)) = 3 * (k : ℤ) ^ 2 - (k : ℤ) := by
        have := hcontra; zify [hle] at this; linarith
      rw [this]; ring
    · intro k hk hcontra
      apply hP
      refine ⟨-(k : ℤ), ?_⟩
      rw [key]
      have : (2 * (n : ℤ)) = 3 * (k : ℤ) ^ 2 + (k : ℤ) := by
        have := hcontra; zify at this; linarith
      rw [this]; ring
