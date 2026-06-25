/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import QSeries.Defs

/-!
# Infinite q-Pochhammer symbol

Under $\|q\| < 1$, the infinite product $(a;q)_\infty = \prod_{k \geq 0}(1 - aq^k)$
converges. We define it via `tprod` and prove convergence, non-vanishing, and
partial-product convergence.

## Main definitions

* `qSeries.qPochhammerInf a q` — the infinite q-Pochhammer symbol $(a;q)_\infty$.

## Main results

* `qSeries.multipliable_one_sub_smul_qpow` — multipliability for $\|q\| < 1$.
* `qSeries.tendsto_qPochhammer` — partial products converge to $(a;q)_\infty$.
* `qSeries.qPochhammerInf_z_q_ne_zero` — non-vanishing for $\|z\| < 1$, $\|q\| < 1$.
* `qSeries.qPochhammerInf_recursion` — telescoping $(z;q)_\infty = (1-z)(zq;q)_\infty$.
-/

open Finset Filter
open scoped Topology

namespace qSeries

/-- **Infinite q-Pochhammer symbol** $(a;q)_\infty = \prod_{k=0}^{\infty}(1 - aq^k)$.

Defined unconditionally as a `tprod`; convergence (under $\|q\| < 1$) is provided
by `multipliable_one_sub_smul_qpow`. -/
noncomputable def qPochhammerInf (a q : ℂ) : ℂ := ∏' k : ℕ, (1 - a * q ^ k)

/-- For $\|q\| < 1$, the product $\prod_{k \geq 0}(1 - aq^k)$ is multipliable. -/
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

/-- Helper: $(a;q)_\infty \neq 0$ when every factor is nonzero. -/
theorem qPochhammerInf_ne_zero_of_factors {a q : ℂ} (hq : ‖q‖ < 1)
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

/-- **Partial products converge to $(a;q)_\infty$.** -/
theorem tendsto_qPochhammer {a q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n => qPochhammer a q n) atTop (𝓝 (qPochhammerInf a q)) := by
  have hmul : Multipliable (fun k : ℕ => 1 - a * q ^ k) :=
    multipliable_one_sub_smul_qpow hq
  simpa [qPochhammer, qPochhammerInf] using hmul.hasProd.tendsto_prod_nat

/-- **Telescoping recursion for $(z;q)_\infty$.**
$(z;q)_\infty = (1 - z) \cdot (zq;q)_\infty$. -/
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
  have hLHS : Tendsto (fun n => qPochhammer z q (n + 1)) atTop
                (𝓝 (qPochhammerInf z q)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_qPochhammer hq)
  have hRHS : Tendsto (fun n => (1 - z) * qPochhammer (z * q) q n) atTop
                (𝓝 ((1 - z) * qPochhammerInf (z * q) q)) :=
    (tendsto_qPochhammer (a := z * q) hq).const_mul (1 - z)
  have heq : (fun n => qPochhammer z q (n + 1))
              = (fun n => (1 - z) * qPochhammer (z * q) q n) := funext h_fin
  rw [heq] at hLHS
  exact tendsto_nhds_unique hLHS hRHS

end qSeries
