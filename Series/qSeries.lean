import Mathlib

/-!
# $q$-Pochhammer symbol and Gaussian binomial coefficient

Blueprint reference: Section `sec:qbin-proof` of `blueprint/src/content_Jac.tex`.
This file (in the `Series` lean library) realizes steps 1–4 of the roadmap
listed under `\subsection{Formalization plan in Lean}` (Section 11.4):

* `qPochhammer`  — Definition `def:qPochhammer`,
  the finite $q$-Pochhammer symbol $(a;q)_n = \prod_{k=0}^{n-1}(1 - a q^k)$.
* `qPochhammer_succ` — Lemma `lem:qPochhammer-succ`,
  the recursion $(a;q)_{n+1} = (a;q)_n \cdot (1 - a q^n)$.
* `qBinom` — Definition `def:qBinom`,
  the Gaussian binomial coefficient defined by the $q$-Pascal recurrence
  $\binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}\binom{n}{k}_q$.
* `qBinom_mul_qPochhammer_mul_qPochhammer` — Lemma `lem:qBinom-closed-form`,
  the closed-form identity $\binom{n}{k}_q \cdot (q;q)_k \cdot (q;q)_{n-k} = (q;q)_n$
  for $k \leq n$.
-/

open Finset Filter
open scoped Topology

namespace qSeries

variable {R : Type*}

/-- **Finite $q$-Pochhammer symbol.**
$(a;q)_n = \prod_{k=0}^{n-1} (1 - a q^k)$. -/
def qPochhammer [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ k ∈ range n, (1 - a * q ^ k)

@[simp]
theorem qPochhammer_zero [CommRing R] (a q : R) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]

/-- **Recurrence for $q$-Pochhammer.** $(a;q)_{n+1} = (a;q)_n \cdot (1 - a q^n)$. -/
theorem qPochhammer_succ [CommRing R] (a q : R) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by
  simp [qPochhammer, prod_range_succ]

/-- **Gaussian binomial coefficient** $\binom{n}{k}_q$.

Defined by the $q$-Pascal recurrence so that the result is always a polynomial
in $q$ (no division). The boundary cases use the conventions
$\binom{0}{0}_q = 1$, $\binom{0}{k+1}_q = 0$, $\binom{n+1}{0}_q = 1$. -/
def qBinom [CommRing R] : ℕ → ℕ → R → R
  | 0,     0,     _ => 1
  | 0,     _ + 1, _ => 0
  | _ + 1, 0,     _ => 1
  | n + 1, k + 1, q => qBinom n (k + 1) q + q ^ (n - k) * qBinom n k q

@[simp] theorem qBinom_zero_zero [CommRing R] (q : R) : qBinom 0 0 q = 1 := rfl

@[simp] theorem qBinom_zero_succ [CommRing R] (k : ℕ) (q : R) :
    qBinom 0 (k + 1) q = 0 := rfl

@[simp] theorem qBinom_succ_zero [CommRing R] (n : ℕ) (q : R) :
    qBinom (n + 1) 0 q = 1 := rfl

@[simp] theorem qBinom_zero_right [CommRing R] (n : ℕ) (q : R) :
    qBinom n 0 q = 1 := by cases n <;> rfl

theorem qBinom_succ_succ [CommRing R] (n k : ℕ) (q : R) :
    qBinom (n + 1) (k + 1) q
      = qBinom n (k + 1) q + q ^ (n - k) * qBinom n k q := rfl

/-- $\binom{n}{k}_q = 0$ whenever $k > n$. -/
theorem qBinom_eq_zero_of_lt [CommRing R] (q : R) :
    ∀ {n k : ℕ}, n < k → qBinom n k q = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl _)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [qBinom_succ_succ,
        qBinom_eq_zero_of_lt q (show n < k + 1 by omega),
        qBinom_eq_zero_of_lt q (show n < k by omega)]
    ring

/-- $\binom{n}{n}_q = 1$. -/
theorem qBinom_self [CommRing R] (q : R) : ∀ n : ℕ, qBinom n n q = 1
  | 0 => rfl
  | n + 1 => by
    rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n),
        qBinom_self q n, Nat.sub_self, pow_zero]
    ring

/-- **Closed-form identity** (step 4 of the blueprint roadmap).

For $k \leq n$:
$$\binom{n}{k}_q \cdot (q;q)_k \cdot (q;q)_{n-k} = (q;q)_n.$$ -/
theorem qBinom_mul_qPochhammer_mul_qPochhammer [CommRing R] (q : R) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom n k q * qPochhammer q q k * qPochhammer q q (n - k)
        = qPochhammer q q n := by
  intro n
  induction n with
  | zero =>
      intro k hk
      interval_cases k
      simp
  | succ n ih =>
      intro k hk
      rcases k with _ | k
      · -- $k = 0$: both Pochhammer factors not involving $n$ are $1$.
        simp
      · -- $k$ is `k + 1` (renamed).
        rcases lt_or_eq_of_le hk with hlt | heq
        · -- Inductive step: $k + 1 < n + 1$, so $k + 1 \le n$ and $k \le n$.
          have hk1 : k + 1 ≤ n := Nat.lt_succ_iff.mp hlt
          have hk2 : k ≤ n := by omega
          have ih1 := ih hk1
          have ih2 := ih hk2
          have hpow1 : q * q ^ (n - (k + 1)) = q ^ (n - k) := by
            rw [show (n - k : ℕ) = (n - (k + 1)) + 1 from by omega, pow_succ']
          have hpow2 : q ^ (n - k) * (q * q ^ k) = q * q ^ n := by
            rw [show q ^ (n - k) * (q * q ^ k) = q * (q ^ (n - k) * q ^ k)
                  from by ring, ← pow_add, Nat.sub_add_cancel hk2]
          have hnk_split :
              qPochhammer q q (n - k)
                = qPochhammer q q (n - (k + 1)) * (1 - q * q ^ (n - (k + 1))) := by
            rw [show (n - k : ℕ) = (n - (k + 1)) + 1 from by omega,
                qPochhammer_succ]
          have ih1' :
              qBinom n (k + 1) q * (qPochhammer q q k * (1 - q * q ^ k))
                  * qPochhammer q q (n - (k + 1))
                = qPochhammer q q n := by
            rw [← qPochhammer_succ]; exact ih1
          have ih2_split :
              qBinom n k q * qPochhammer q q k
                  * (qPochhammer q q (n - (k + 1)) * (1 - q * q ^ (n - (k + 1))))
                = qPochhammer q q n := by
            rw [← hnk_split]; exact ih2
          have h_rhs_pow :
              q * q ^ n = q * q ^ (n - (k + 1)) * (q * q ^ k) := by
            rw [← hpow2, ← hpow1]
          rw [qBinom_succ_succ,
              show (n + 1) - (k + 1) = n - k from by omega,
              hnk_split, qPochhammer_succ q q k, qPochhammer_succ q q n,
              ← hpow1, h_rhs_pow]
          linear_combination
            (1 - q * q ^ (n - (k + 1))) * ih1'
              + q * q ^ (n - (k + 1)) * (1 - q * q ^ k) * ih2_split
        · -- Boundary: $k + 1 = n + 1$, i.e. $k = n$.
          have hkn : k = n := by omega
          rw [hkn, qBinom_succ_succ,
              qBinom_eq_zero_of_lt q (Nat.lt_succ_self _),
              qBinom_self, Nat.sub_self, pow_zero,
              show (n + 1) - (n + 1) = 0 from by omega,
              qPochhammer_zero]
          ring

/-- Helper: $(k+1).\mathrm{choose}\, 2 = k.\mathrm{choose}\, 2 + k$. -/
private lemma choose_two_succ (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- **Finite $q$-binomial theorem** (step 5 of the blueprint roadmap).

$$\prod_{k=0}^{n-1}\,(1 + z\, q^k) \;=\; \sum_{k=0}^{n} q^{\binom{k}{2}}\,\binom{n}{k}_q\, z^k.$$ -/
theorem qBinom_finite_thm [CommRing R] (q z : R) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + z * q ^ k)
      = ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * z ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      -- Step A: Peel off the $k = 0$ term on the RHS via `Finset.sum_range_succ'`.
      rw [Finset.sum_range_succ'
            (fun k => q ^ k.choose 2 * qBinom (n + 1) k q * z ^ k) (n + 1)]
      simp only [Nat.choose_zero_succ, pow_zero, qBinom_succ_zero, mul_one]
      -- Step B: Apply the $q$-Pascal recurrence and split into two sums.
      have stepB :
          (∑ k ∈ Finset.range (n + 1),
              q ^ (k + 1).choose 2 * qBinom (n + 1) (k + 1) q * z ^ (k + 1))
            = (∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * qBinom n (k + 1) q * z ^ (k + 1))
              + ∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * q ^ (n - k) * qBinom n k q
                    * z ^ (k + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [qBinom_succ_succ]
        ring
      rw [stepB]
      -- Step C: The second sum equals $z\, q^n \cdot \mathrm{RHS}_n$.
      have stepC :
          (∑ k ∈ Finset.range (n + 1),
              q ^ (k + 1).choose 2 * q ^ (n - k) * qBinom n k q * z ^ (k + 1))
            = z * q ^ n *
                ∑ k ∈ Finset.range (n + 1),
                    q ^ k.choose 2 * qBinom n k q * z ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [choose_two_succ k, pow_add q (k.choose 2) k,
            mul_assoc (q ^ k.choose 2) (q ^ k) (q ^ (n - k)),
            ← pow_add q k (n - k),
            show k + (n - k) = n from by omega,
            pow_succ z k]
        ring
      rw [stepC]
      -- Step D: The remaining first sum equals $\mathrm{RHS}_n - 1$ (after
      -- using $\binom{n}{n+1}_q = 0$ to drop the top term of an extended sum).
      have stepD :
          (∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * z ^ k)
            = (∑ k ∈ Finset.range (n + 1),
                  q ^ (k + 1).choose 2 * qBinom n (k + 1) q * z ^ (k + 1)) + 1 := by
        have h := Finset.sum_range_succ'
          (fun k => q ^ k.choose 2 * qBinom n k q * z ^ k) (n + 1)
        simp only [Nat.choose_zero_succ, pow_zero, qBinom_zero_right, mul_one] at h
        rw [Finset.sum_range_succ
              (f := fun k => q ^ k.choose 2 * qBinom n k q * z ^ k) (n := n + 1),
            qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)] at h
        simp only [mul_zero, zero_mul, add_zero] at h
        exact h
      linear_combination stepD

/-! ## Infinite $q$-Pochhammer symbol and the Cauchy identity

Under $\|q\| < 1$, the infinite product $(a; q)_\infty = \prod_{k \geq 0}(1 - a q^k)$
converges (in $\mathbb{C}$). We define it via `tprod`; only under the convergence
hypothesis is the value mathematically meaningful. -/

/-- **Infinite $q$-Pochhammer symbol** $(a; q)_\infty = \prod_{k = 0}^{\infty}(1 - a q^k)$.

Defined unconditionally as a `tprod`; convergence
(under $\|q\| < 1$) is provided by `multipliable_one_sub_smul_qpow` below. -/
noncomputable def qPochhammerInf (a q : ℂ) : ℂ := ∏' k : ℕ, (1 - a * q ^ k)

/-- For $\|q\| < 1$ the product $\prod_{k \geq 0}(1 - a q^k)$ is multipliable
in $\mathbb{C}$. The proof reduces multipliability to summability of
$\sum_k \|a q^k\| = \|a\| \sum_k \|q\|^k$, which is geometric. -/
theorem multipliable_one_sub_smul_qpow {a q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun k : ℕ => 1 - a * q ^ k) := by
  have h_geom : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have h_summ : Summable (fun n : ℕ => ‖-(a * q ^ n)‖) := by
    have eq : (fun n : ℕ => ‖-(a * q ^ n)‖) = (fun n => ‖a‖ * ‖q‖ ^ n) := by
      ext n; rw [norm_neg, norm_mul, norm_pow]
    rw [eq]
    exact h_geom.mul_left ‖a‖
  have key : Multipliable (fun k : ℕ => 1 + -(a * q ^ k)) :=
    multipliable_one_add_of_summable h_summ
  simpa [sub_eq_add_neg] using key

/-! ## The Cauchy identity (step 8)

We prove `qBinom_infinite_thm` by Heine's classical functional-equation
argument. Set
$$F(z) := \sum_{n \ge 0} \frac{(a;q)_n}{(q;q)_n}\, z^n, \qquad
  G(z) := \frac{(a z;q)_\infty}{(z;q)_\infty}.$$
Both satisfy the functional equation $(1 - z)\,H(z) = (1 - a z)\,H(qz)$
with $H(0) = 1$. The argument has three pieces:

(i)   *Algebraic*: a coefficient recurrence
      $c_{n+1}(1 - q^{n+1}) = c_n (1 - a q^n)$ where $c_n = (a;q)_n/(q;q)_n$.
(ii)  *Functional equation*: both $F$ and $G$ satisfy
      $(1-z) H(z) = (1-az) H(qz)$.
(iii) *Iteration*: from the functional equation,
      $F(z) (z;q)_n = F(q^n z) (a z;q)_n$ for every $n$.
      Sending $n \to \infty$: $F(q^n z) \to F(0) = 1$ and $(z;q)_n \to (z;q)_\infty$
      (and similarly for $(a z;q)_n$), giving $F(z) (z;q)_\infty = (a z;q)_\infty$.
-/

section CauchyIdentity

/-! ### Non-vanishing of denominators -/

/-- **Non-vanishing of $(q;q)_n$ for $\|q\| < 1$.** -/
theorem qPochhammer_q_q_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammer q q n ≠ 0 := by
  rw [qPochhammer, Finset.prod_ne_zero_iff]
  intro k _ h
  rw [show (1 : ℂ) - q * q ^ k = 1 - q ^ (k + 1) from by ring] at h
  have h1 : q ^ (k + 1) = 1 := by linear_combination -h
  have hn1 : ‖q ^ (k + 1)‖ = 1 := by rw [h1]; simp
  rw [norm_pow] at hn1
  have hqp : ‖q‖ ^ (k + 1) < 1 :=
    pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero k)
  linarith

/-- **Non-vanishing of $(z;q)_n$ when $\|z\| < 1$ and $\|q\| \le 1$.** -/
theorem qPochhammer_z_q_ne_zero {z q : ℂ} (hz : ‖z‖ < 1) (hq : ‖q‖ ≤ 1)
    (n : ℕ) : qPochhammer z q n ≠ 0 := by
  rw [qPochhammer, Finset.prod_ne_zero_iff]
  intro k _ h
  have h1 : z * q ^ k = 1 := by linear_combination -h
  have hnorm : ‖z * q ^ k‖ = 1 := by rw [h1]; simp
  rw [norm_mul, norm_pow] at hnorm
  have hqkle : ‖q‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hq
  nlinarith [norm_nonneg z, norm_nonneg q, pow_nonneg (norm_nonneg q) k]

/-- Helper: $(a; q)_\infty \neq 0$ whenever $\|q\| < 1$ and every factor is nonzero. -/
private lemma qPochhammerInf_ne_zero_of_factors {a q : ℂ} (hq : ‖q‖ < 1)
    (hfac : ∀ k : ℕ, (1 : ℂ) - a * q ^ k ≠ 0) :
    qPochhammerInf a q ≠ 0 := by
  have h_geom : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have h_summ : Summable (fun n : ℕ => ‖-(a * q ^ n)‖) := by
    have eq : (fun n : ℕ => ‖-(a * q ^ n)‖) = (fun n => ‖a‖ * ‖q‖ ^ n) := by
      ext n; rw [norm_neg, norm_mul, norm_pow]
    rw [eq]
    exact h_geom.mul_left ‖a‖
  have h_ne : ∀ i, (1 : ℂ) + -(a * q ^ i) ≠ 0 := by
    intro i
    rw [show (1 : ℂ) + -(a * q ^ i) = 1 - a * q ^ i from by ring]
    exact hfac i
  have h_main : (∏' k : ℕ, ((1 : ℂ) + -(a * q ^ k))) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable h_ne h_summ
  unfold qPochhammerInf
  have h_eq : (fun k : ℕ => (1 : ℂ) - a * q ^ k)
                = (fun k => (1 : ℂ) + -(a * q ^ k)) := by
    ext k; ring
  rw [h_eq]
  exact h_main

/-- **Non-vanishing of $(z;q)_\infty$ for $\|z\| < 1, \|q\| < 1$.** -/
theorem qPochhammerInf_z_q_ne_zero {z q : ℂ} (hz : ‖z‖ < 1) (hq : ‖q‖ < 1) :
    qPochhammerInf z q ≠ 0 := by
  apply qPochhammerInf_ne_zero_of_factors hq
  intro k h
  have h1 : z * q ^ k = 1 := by linear_combination -h
  have hnorm : ‖z * q ^ k‖ = 1 := by rw [h1]; simp
  rw [norm_mul, norm_pow] at hnorm
  have hqkle : ‖q‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
  nlinarith [norm_nonneg z, norm_nonneg q, pow_nonneg (norm_nonneg q) k]

/-! ### Convergence of partial products -/

/-- **Partial products converge to $(a;q)_\infty$.** -/
theorem tendsto_qPochhammer {a q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n => qPochhammer a q n) atTop (𝓝 (qPochhammerInf a q)) := by
  have hmul : Multipliable (fun k : ℕ => 1 - a * q ^ k) :=
    multipliable_one_sub_smul_qpow hq
  simpa [qPochhammer, qPochhammerInf] using hmul.hasProd.tendsto_prod_nat

/-! ### The coefficient sequence -/

/-- The coefficient sequence $c_n = (a;q)_n / (q;q)_n$. -/
noncomputable def cauchyCoeff (a q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer a q n / qPochhammer q q n

@[simp] theorem cauchyCoeff_zero (a q : ℂ) : cauchyCoeff a q 0 = 1 := by
  simp [cauchyCoeff]

/-- **Coefficient recurrence.** $c_{n+1}(1 - q^{n+1}) = c_n(1 - a q^n)$. -/
theorem cauchyCoeff_succ_mul {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) (n : ℕ) :
    cauchyCoeff a q (n + 1) * (1 - q ^ (n + 1))
      = cauchyCoeff a q n * (1 - a * q ^ n) := by
  unfold cauchyCoeff
  have hqn : qPochhammer q q n ≠ 0 := qPochhammer_q_q_ne_zero hq n
  have hqn1 : qPochhammer q q (n + 1) ≠ 0 := qPochhammer_q_q_ne_zero hq (n + 1)
  rw [qPochhammer_succ a q n, qPochhammer_succ q q n,
      show (1 : ℂ) - q * q ^ n = 1 - q ^ (n + 1) from by ring]
  have hq_ne : (1 : ℂ) - q ^ (n + 1) ≠ 0 := by
    intro habs
    apply hqn1
    rw [qPochhammer_succ q q n,
        show (1 : ℂ) - q * q ^ n = 1 - q ^ (n + 1) from by ring,
        habs, mul_zero]
  field_simp

/-- **Boundedness of the coefficients.** There exists $C$ with $\|c_n\| \le C$
for all $n$. -/
theorem cauchyCoeff_bounded {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    ∃ C, ∀ n, ‖cauchyCoeff a q n‖ ≤ C := by
  have hnum : Tendsto (fun n => ‖qPochhammer a q n‖) atTop
      (𝓝 ‖qPochhammerInf a q‖) := (tendsto_qPochhammer hq).norm
  have hden : Tendsto (fun n => ‖qPochhammer q q n‖) atTop
      (𝓝 ‖qPochhammerInf q q‖) := (tendsto_qPochhammer hq).norm
  obtain ⟨M, hM⟩ : ∃ M, ∀ n, ‖qPochhammer a q n‖ ≤ M := by
    rcases hnum.bddAbove_range with ⟨M, hM⟩
    exact ⟨M, fun n => hM ⟨n, rfl⟩⟩
  have hden_ne : qPochhammerInf q q ≠ 0 := by
    apply qPochhammerInf_ne_zero_of_factors hq
    intro k h
    rw [show (1 : ℂ) - q * q ^ k = 1 - q ^ (k + 1) from by ring] at h
    have h1 : q ^ (k + 1) = 1 := by linear_combination -h
    have hn1 : ‖q ^ (k + 1)‖ = 1 := by rw [h1]; simp
    rw [norm_pow] at hn1
    have : ‖q‖ ^ (k + 1) < 1 :=
      pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero k)
    linarith
  have hden_pos : 0 < ‖qPochhammerInf q q‖ := norm_pos_iff.mpr hden_ne
  set ε : ℝ := ‖qPochhammerInf q q‖ / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have hev : ∀ᶠ n in atTop, ε < ‖qPochhammer q q n‖ := by
    have := hden.eventually (eventually_gt_nhds (half_lt_self hden_pos))
    simpa [hε_def] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max (M / ε) ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖cauchyCoeff a q k‖)), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hd_lt : ε < ‖qPochhammer q q n‖ := hN n hn
    unfold cauchyCoeff
    rw [norm_div]
    have hineq : ‖qPochhammer a q n‖ / ‖qPochhammer q q n‖ ≤ M / ε := by
      apply div_le_div₀ (le_trans (norm_nonneg _) (hM n)) (hM n) hε_pos hd_lt.le
    exact le_trans hineq (le_max_left _ _)
  · have hn' : n < N := Nat.lt_of_not_le hn
    apply le_trans _ (le_max_right (M / ε) _)
    exact Finset.le_sup' (fun k => ‖cauchyCoeff a q k‖)
      (Finset.mem_range.mpr (Nat.lt_succ_of_lt hn'))

/-! ### Summability of the Cauchy series -/

/-- The series $\sum_n c_n z^n$ is summable for $\|z\| < 1$. -/
theorem cauchy_summable {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) := by
  obtain ⟨C, hC⟩ := cauchyCoeff_bounded hq a
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  apply Summable.of_norm_bounded (g := fun n => C * ‖z‖ ^ n)
  · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hC n) le_rfl (pow_nonneg (norm_nonneg z) n) hCnn

/-! ### Functional equation for $G$ -/

/-- **Telescoping recursion for $(z;q)_\infty$.**
$(z; q)_\infty = (1 - z) \cdot (z q; q)_\infty$. Proof: partial products satisfy
`qPochhammer z q (n+1) = (1 - z) * qPochhammer (z*q) q n`; take `n → ∞`. -/
theorem qPochhammerInf_recursion {z q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf z q = (1 - z) * qPochhammerInf (z * q) q := by
  have h_fin : ∀ n : ℕ,
      qPochhammer z q (n + 1) = (1 - z) * qPochhammer (z * q) q n := by
    intro n
    induction n with
    | zero => simp [qPochhammer_succ, qPochhammer_zero]
    | succ n ih =>
        rw [qPochhammer_succ z q (n + 1), ih, qPochhammer_succ (z * q) q n,
            show (z * q) * q ^ n = z * q ^ (n + 1) from by ring]
        ring
  -- LHS limit: qPochhammer z q at indices n+1 still tends to qPochhammerInf z q.
  have hLHS : Tendsto (fun n => qPochhammer z q (n + 1)) atTop
                (𝓝 (qPochhammerInf z q)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_qPochhammer hq)
  -- RHS limit:
  have hRHS : Tendsto (fun n => (1 - z) * qPochhammer (z * q) q n) atTop
                (𝓝 ((1 - z) * qPochhammerInf (z * q) q)) :=
    (tendsto_qPochhammer (a := z * q) hq).const_mul (1 - z)
  -- The two functions agree pointwise by `h_fin`.
  have heq : (fun n => qPochhammer z q (n + 1))
              = (fun n => (1 - z) * qPochhammer (z * q) q n) := funext h_fin
  rw [heq] at hLHS
  exact tendsto_nhds_unique hLHS hRHS

/-- **Functional equation for $G$.**
$(1-z)\, G(z) = (1 - a z)\, G(q z)$, where $G(z) = (a z; q)_\infty / (z; q)_\infty$. -/
theorem cauchy_functional_eq_G (a z : ℂ) {q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    (1 - z) * (qPochhammerInf (a * z) q / qPochhammerInf z q)
      = (1 - a * z) *
          (qPochhammerInf (a * z * q) q / qPochhammerInf (z * q) q) := by
  have hzq : ‖z * q‖ < 1 := by
    rw [norm_mul]
    by_cases hzz : z = 0
    · simp [hzz]
    · have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzz
      calc ‖z‖ * ‖q‖ < ‖z‖ * 1 :=
              mul_lt_mul_of_pos_left hq hz_pos
        _ = ‖z‖ := mul_one _
        _ < 1 := hz
  have hz_ne : qPochhammerInf z q ≠ 0 := qPochhammerInf_z_q_ne_zero hz hq
  have hzq_ne : qPochhammerInf (z * q) q ≠ 0 :=
    qPochhammerInf_z_q_ne_zero hzq hq
  have hone_sub_z_ne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz1 : z = 1 := by linear_combination -h
    rw [hz1] at hz; norm_num at hz
  have hGz : qPochhammerInf z q = (1 - z) * qPochhammerInf (z * q) q :=
    qPochhammerInf_recursion hq
  have hGaz : qPochhammerInf (a * z) q
                = (1 - a * z) * qPochhammerInf (a * z * q) q :=
    qPochhammerInf_recursion hq
  rw [hGz, hGaz]
  field_simp

/-! ### Functional equation for $F$ -/

private theorem hasSum_one_sub_mul_F {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => if n = 0 then (1 : ℂ)
                          else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
      ((1 - z) * ∑' n, cauchyCoeff a q n * z ^ n) := by
  set F := ∑' n, cauchyCoeff a q n * z ^ n with hF_def
  have hSum : Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) :=
    cauchy_summable hq hz
  have hF : HasSum (fun n => cauchyCoeff a q n * z ^ n) F := hSum.hasSum
  have hshifted : HasSum (fun n => cauchyCoeff a q n * z ^ (n + 1)) (z * F) := by
    have h := hF.mul_left z
    convert h using 1; ext n; ring
  -- g n = if n = 0 then 0 else c_{n-1} z^n.  Sums to z * F by reindexing.
  let g : ℕ → ℂ := fun n => if n = 0 then 0 else cauchyCoeff a q (n - 1) * z ^ n
  have hg_succ_eq : (fun n => g (n + 1))
                = (fun n => cauchyCoeff a q n * z ^ (n + 1)) := by
    funext n; simp [g]
  have hg_zero : g 0 = 0 := by simp [g]
  have hg : HasSum g (z * F) := by
    have h1 : HasSum (fun n => g (n + 1)) (z * F) := by
      rw [hg_succ_eq]; exact hshifted
    have h2 : (z * F) = (z * F) - ∑ i ∈ Finset.range 1, g i := by
      simp [hg_zero]
    rw [h2] at h1
    exact (hasSum_nat_add_iff' (f := g) 1).mp h1
  have hdiff : HasSum (fun n => cauchyCoeff a q n * z ^ n - g n) (F - z * F) :=
    hF.sub hg
  have hfunc : (fun n : ℕ => if n = 0 then (1 : ℂ)
                              else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
                = (fun n : ℕ => cauchyCoeff a q n * z ^ n - g n) := by
    funext n
    by_cases hn : n = 0
    · subst hn; simp [g, cauchyCoeff_zero]
    · simp only [if_neg hn, g]; ring
  rw [hfunc]
  have h_target : (1 - z) * F = F - z * F := by ring
  rw [h_target]
  exact hdiff

private theorem hasSum_one_sub_az_mul_F_qz {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => if n = 0 then (1 : ℂ)
                          else (cauchyCoeff a q n * q ^ n
                                  - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n)
      ((1 - a * z) * ∑' n, cauchyCoeff a q n * (q * z) ^ n) := by
  set Fqz := ∑' n, cauchyCoeff a q n * (q * z) ^ n with hFqz_def
  have hqz : ‖q * z‖ < 1 := by
    rw [norm_mul]
    by_cases hzz : z = 0
    · simp [hzz]
    · have : 0 < ‖z‖ := norm_pos_iff.mpr hzz
      calc ‖q‖ * ‖z‖ < 1 * ‖z‖ := mul_lt_mul_of_pos_right hq this
        _ = ‖z‖ := one_mul _
        _ < 1 := hz
  have hF : HasSum (fun n => cauchyCoeff a q n * (q * z) ^ n) Fqz :=
    (cauchy_summable hq hqz).hasSum
  have hF' : HasSum (fun n => cauchyCoeff a q n * q ^ n * z ^ n) Fqz := by
    convert hF using 1; ext n; rw [mul_pow]; ring
  have hshifted : HasSum (fun n => a * cauchyCoeff a q n * q ^ n * z ^ (n + 1))
                          (a * z * Fqz) := by
    have h := hF'.mul_left (a * z)
    convert h using 1; ext n; ring
  let g : ℕ → ℂ := fun n => if n = 0 then 0
                              else a * cauchyCoeff a q (n - 1) * q ^ (n - 1) * z ^ n
  have hg_succ_eq : (fun n => g (n + 1))
                = (fun n => a * cauchyCoeff a q n * q ^ n * z ^ (n + 1)) := by
    funext n; simp [g]
  have hg_zero : g 0 = 0 := by simp [g]
  have hg : HasSum g (a * z * Fqz) := by
    have h1 : HasSum (fun n => g (n + 1)) (a * z * Fqz) := by
      rw [hg_succ_eq]; exact hshifted
    have h2 : (a * z * Fqz) = (a * z * Fqz) - ∑ i ∈ Finset.range 1, g i := by
      simp [hg_zero]
    rw [h2] at h1
    exact (hasSum_nat_add_iff' (f := g) 1).mp h1
  have hdiff : HasSum (fun n => cauchyCoeff a q n * q ^ n * z ^ n - g n)
                (Fqz - a * z * Fqz) := hF'.sub hg
  have hfunc : (fun n : ℕ => if n = 0 then (1 : ℂ)
                              else (cauchyCoeff a q n * q ^ n
                                      - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n)
                = (fun n : ℕ => cauchyCoeff a q n * q ^ n * z ^ n - g n) := by
    funext n
    by_cases hn : n = 0
    · subst hn; simp [g, cauchyCoeff_zero]
    · simp only [if_neg hn, g]; ring
  rw [hfunc]
  have h_target : (1 - a * z) * Fqz = Fqz - a * z * Fqz := by ring
  rw [h_target]
  exact hdiff

/-- **Functional equation for $F$.**
$(1-z)\, F(z) = (1 - a z)\, F(q z)$. -/
theorem cauchy_functional_eq_F {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    (1 - z) * ∑' n, cauchyCoeff a q n * z ^ n
      = (1 - a * z) * ∑' n, cauchyCoeff a q n * (q * z) ^ n := by
  have hL := hasSum_one_sub_mul_F (a := a) (q := q) (z := z) hq hz
  have hR := hasSum_one_sub_az_mul_F_qz (a := a) (q := q) (z := z) hq hz
  have hfunc : (fun n : ℕ => if n = 0 then (1 : ℂ)
                  else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
              = (fun n : ℕ => if n = 0 then (1 : ℂ)
                  else (cauchyCoeff a q n * q ^ n
                          - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n) := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [if_neg hn]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp only [Nat.succ_sub_one]
      have hrec := cauchyCoeff_succ_mul (a := a) hq m
      have hcoef : cauchyCoeff a q (m + 1) - cauchyCoeff a q m
                    = cauchyCoeff a q (m + 1) * q ^ (m + 1)
                        - a * cauchyCoeff a q m * q ^ m := by
        linear_combination hrec
      rw [hcoef]
  rw [hfunc] at hL
  exact hL.unique hR

/-! ### Iteration -/

/-- **Iterated functional equation.** -/
theorem iterated_functional_eq_disc {H : ℂ → ℂ} {a q : ℂ} (hq : ‖q‖ < 1)
    (hH : ∀ w, ‖w‖ < 1 → (1 - w) * H w = (1 - a * w) * H (q * w))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∀ n : ℕ, H z * qPochhammer z q n
              = H (q ^ n * z) * qPochhammer (a * z) q n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hqnz : ‖q ^ n * z‖ < 1 := by
        rw [norm_mul, norm_pow]
        calc ‖q‖ ^ n * ‖z‖
            ≤ 1 * ‖z‖ := by
              apply mul_le_mul_of_nonneg_right
                (pow_le_one₀ (norm_nonneg _) hq.le) (norm_nonneg _)
          _ = ‖z‖ := one_mul _
          _ < 1 := hz
      have key : (1 - q ^ n * z) * H (q ^ n * z)
                  = (1 - a * (q ^ n * z)) * H (q * (q ^ n * z)) := hH _ hqnz
      have hqq : q * (q ^ n * z) = q ^ (n + 1) * z := by ring
      rw [hqq] at key
      rw [qPochhammer_succ z q n, qPochhammer_succ (a * z) q n]
      have hzqn : (1 : ℂ) - z * q ^ n = 1 - q ^ n * z := by ring
      have hazqn : (1 : ℂ) - a * z * q ^ n = 1 - a * (q ^ n * z) := by ring
      rw [hzqn, hazqn]
      calc H z * (qPochhammer z q n * (1 - q ^ n * z))
          = (H z * qPochhammer z q n) * (1 - q ^ n * z) := by ring
        _ = (H (q ^ n * z) * qPochhammer (a * z) q n) * (1 - q ^ n * z) := by rw [ih]
        _ = qPochhammer (a * z) q n * ((1 - q ^ n * z) * H (q ^ n * z)) := by ring
        _ = qPochhammer (a * z) q n *
              ((1 - a * (q ^ n * z)) * H (q ^ (n + 1) * z)) := by rw [key]
        _ = H (q ^ (n + 1) * z) *
              (qPochhammer (a * z) q n * (1 - a * (q ^ n * z))) := by ring

/-! ### The limit of $F(q^n z)$ -/

/-- **$F(q^n z) \to 1$ as $n \to \infty$**, by Tannery's theorem. -/
theorem tendsto_F_qpow {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Tendsto (fun n : ℕ => ∑' k, cauchyCoeff a q k * (q ^ n * z) ^ k)
      atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := cauchyCoeff_bounded hq a
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  let g : ℕ → ℂ := fun k => if k = 0 then 1 else 0
  let bound : ℕ → ℝ := fun k => C * ‖z‖ ^ k
  have h_sum : Summable bound :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C
  have hab : ∀ k : ℕ, Tendsto (fun n : ℕ => cauchyCoeff a q k * (q ^ n * z) ^ k)
                              atTop (𝓝 (g k)) := by
    intro k
    by_cases hk : k = 0
    · simp [g, hk]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hpow : ∀ n : ℕ, cauchyCoeff a q (m + 1) * (q ^ n * z) ^ (m + 1)
                            = cauchyCoeff a q (m + 1) * z ^ (m + 1) * (q ^ (m + 1)) ^ n := by
        intro n
        rw [mul_pow, ← pow_mul, mul_comm n (m + 1), pow_mul]
        ring
      simp only [g, if_neg (Nat.succ_ne_zero m)]
      have hqpow : ‖q ^ (m + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero m)
      have htend : Tendsto (fun n : ℕ => (q ^ (m + 1)) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hqpow
      have hmul := htend.const_mul (cauchyCoeff a q (m + 1) * z ^ (m + 1))
      simp only [mul_zero] at hmul
      exact hmul.congr (fun n => (hpow n).symm)
  have h_bound : ∀ᶠ n in atTop, ∀ k : ℕ,
                    ‖cauchyCoeff a q k * (q ^ n * z) ^ k‖ ≤ bound k := by
    apply Filter.Eventually.of_forall
    intro n k
    simp only [bound]
    rw [norm_mul, norm_pow, norm_mul, norm_pow, mul_pow]
    calc ‖cauchyCoeff a q k‖ * ((‖q‖ ^ n) ^ k * ‖z‖ ^ k)
        = ‖cauchyCoeff a q k‖ * (‖q‖ ^ n) ^ k * ‖z‖ ^ k := by ring
      _ ≤ C * 1 * ‖z‖ ^ k := by
          gcongr
          · exact hC k
          · exact pow_le_one₀ (pow_nonneg (norm_nonneg _) n)
              (pow_le_one₀ (norm_nonneg _) hq.le)
      _ = C * ‖z‖ ^ k := by ring
  have h := tendsto_tsum_of_dominated_convergence h_sum hab h_bound
  have hgsum : (∑' k : ℕ, g k) = 1 := by
    rw [tsum_eq_single 0 (fun k hk => by simp [g, hk])]
    simp [g]
  rw [hgsum] at h
  exact h

/-! ### The main theorem -/

/-- **Infinite $q$-binomial / Cauchy identity** (step 8 of the blueprint roadmap).

For $\|q\| < 1$ and $\|z\| < 1$,
$$\sum_{n=0}^{\infty} \frac{(a; q)_n}{(q; q)_n}\, z^n
  \;=\; \frac{(a z; q)_\infty}{(z; q)_\infty}.$$

Proof: Heine's classical functional-equation argument. Define
$F(z) = \sum c_n z^n$ and $G(z) = (az;q)_\infty / (z;q)_\infty$ with
$c_n = (a;q)_n / (q;q)_n$; both satisfy $(1-z) H(z) = (1-az) H(qz)$;
iterate and pass to the limit $n \to \infty$. -/
theorem qBinom_infinite_thm (a z q : ℂ) (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => qPochhammer a q n / qPochhammer q q n * z ^ n)
      (qPochhammerInf (a * z) q / qPochhammerInf z q) := by
  change HasSum (fun n => cauchyCoeff a q n * z ^ n) _
  have hF_summable : Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) :=
    cauchy_summable hq hz
  set F : ℂ := ∑' n, cauchyCoeff a q n * z ^ n with hF_def
  have hden_ne : qPochhammerInf z q ≠ 0 := qPochhammerInf_z_q_ne_zero hz hq
  suffices hFG : F * qPochhammerInf z q = qPochhammerInf (a * z) q by
    have : F = qPochhammerInf (a * z) q / qPochhammerInf z q := by
      field_simp
      exact hFG
    rw [← this]
    exact hF_summable.hasSum
  let H : ℂ → ℂ := fun w => if ‖w‖ < 1 then ∑' k, cauchyCoeff a q k * w ^ k else 0
  have hH_disc : ∀ w, ‖w‖ < 1 → H w = ∑' k, cauchyCoeff a q k * w ^ k := by
    intro w hw; simp [H, hw]
  have hH_fe : ∀ w, ‖w‖ < 1 → (1 - w) * H w = (1 - a * w) * H (q * w) := by
    intro w hw
    rw [hH_disc w hw]
    have hqw : ‖q * w‖ < 1 := by
      rw [norm_mul]
      by_cases hww : w = 0
      · simp [hww]
      · have : 0 < ‖w‖ := norm_pos_iff.mpr hww
        calc ‖q‖ * ‖w‖ < 1 * ‖w‖ :=
            mul_lt_mul_of_pos_right hq this
          _ = ‖w‖ := one_mul _
          _ < 1 := hw
    rw [hH_disc _ hqw]
    exact cauchy_functional_eq_F hq hw
  have hiter := iterated_functional_eq_disc hq hH_fe hz
  have hF_eq_Hz : F = H z := (hH_disc z hz).symm
  have key : ∀ n : ℕ,
      F * qPochhammer z q n = H (q ^ n * z) * qPochhammer (a * z) q n := by
    intro n
    rw [hF_eq_Hz]; exact hiter n
  have hLHS_lim : Tendsto (fun n => F * qPochhammer z q n) atTop
      (𝓝 (F * qPochhammerInf z q)) :=
    (tendsto_qPochhammer hq).const_mul F
  have hqnz : ∀ n : ℕ, ‖q ^ n * z‖ < 1 := by
    intro n
    rw [norm_mul, norm_pow]
    calc ‖q‖ ^ n * ‖z‖
        ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) hq.le) (norm_nonneg _)
      _ = ‖z‖ := one_mul _
      _ < 1 := hz
  have hH_eq : (fun n => H (q ^ n * z))
                = (fun n => ∑' k, cauchyCoeff a q k * (q ^ n * z) ^ k) := by
    ext n; exact hH_disc _ (hqnz n)
  have hH_lim : Tendsto (fun n => H (q ^ n * z)) atTop (𝓝 1) := by
    rw [hH_eq]; exact tendsto_F_qpow hq hz
  have hRHS_lim : Tendsto (fun n => H (q ^ n * z) * qPochhammer (a * z) q n)
      atTop (𝓝 (1 * qPochhammerInf (a * z) q)) :=
    hH_lim.mul (tendsto_qPochhammer hq)
  rw [one_mul] at hRHS_lim
  have := tendsto_nhds_unique
    (by simpa [key] using hLHS_lim) hRHS_lim
  exact this

end CauchyIdentity

end qSeries
