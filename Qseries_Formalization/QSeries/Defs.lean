/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import Mathlib

/-!
# q-Pochhammer symbol and Gaussian binomial coefficient

This file defines the finite q-Pochhammer symbol $(a;q)_n$ and the Gaussian
binomial coefficient $\binom{n}{k}_q$, together with their basic properties.

## Main definitions

* `qSeries.qPochhammer a q n` — the finite q-Pochhammer symbol
  $(a;q)_n = \prod_{k=0}^{n-1}(1 - a q^k)$.
* `qSeries.qBinom n k q` — the Gaussian binomial coefficient $\binom{n}{k}_q$,
  defined via the q-Pascal recurrence.

## Main results

* `qSeries.qPochhammer_succ` — the recurrence $(a;q)_{n+1} = (a;q)_n (1 - aq^n)$.
* `qSeries.qBinom_succ_succ` — the q-Pascal recurrence.
* `qSeries.qBinom_eq_zero_of_lt` — vanishing above the diagonal.
* `qSeries.qBinom_self` — diagonal value is 1.
* `qSeries.qBinom_mul_qPochhammer_mul_qPochhammer` — closed-form identity
  $\binom{n}{k}_q (q;q)_k (q;q)_{n-k} = (q;q)_n$.
-/

open Finset Filter
open scoped Topology

namespace qSeries

variable {R : Type*}

/-- **Finite q-Pochhammer symbol.**
$(a;q)_n = \prod_{k=0}^{n-1} (1 - a q^k)$. -/
def qPochhammer [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ k ∈ range n, (1 - a * q ^ k)

/-- The empty q-Pochhammer product $(a;q)_0 = 1$. -/
@[simp]
theorem qPochhammer_zero [CommRing R] (a q : R) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]

/-- **Recurrence for q-Pochhammer.** $(a;q)_{n+1} = (a;q)_n \cdot (1 - a q^n)$. -/
theorem qPochhammer_succ [CommRing R] (a q : R) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by
  simp [qPochhammer, prod_range_succ]

/-- **Gaussian binomial coefficient** $\binom{n}{k}_q$.

Defined by the q-Pascal recurrence so that the result is always a polynomial
in $q$ (no division). The boundary cases are
$\binom{0}{0}_q = 1$, $\binom{0}{k+1}_q = 0$, $\binom{n+1}{0}_q = 1$. -/
def qBinom [CommRing R] : ℕ → ℕ → R → R
  | 0,     0,     _ => 1
  | 0,     _ + 1, _ => 0
  | _ + 1, 0,     _ => 1
  | n + 1, k + 1, q => qBinom n (k + 1) q + q ^ (n - k) * qBinom n k q

/-- The Gaussian binomial coefficient $\binom{0}{0}_q = 1$. -/
@[simp] theorem qBinom_zero_zero [CommRing R] (q : R) : qBinom 0 0 q = 1 := rfl

/-- The Gaussian binomial coefficient $\binom{0}{k+1}_q = 0$. -/
@[simp] theorem qBinom_zero_succ [CommRing R] (k : ℕ) (q : R) :
    qBinom 0 (k + 1) q = 0 := rfl

/-- The Gaussian binomial coefficient $\binom{n+1}{0}_q = 1$. -/
@[simp] theorem qBinom_succ_zero [CommRing R] (n : ℕ) (q : R) :
    qBinom (n + 1) 0 q = 1 := rfl

/-- The Gaussian binomial coefficient $\binom{n}{0}_q = 1$ for all $n$. -/
@[simp] theorem qBinom_zero_right [CommRing R] (n : ℕ) (q : R) :
    qBinom n 0 q = 1 := by cases n <;> rfl

/-- The q-Pascal recurrence $\binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}\binom{n}{k}_q$. -/
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

/-- **Closed-form identity.**
For $k \leq n$: $\binom{n}{k}_q (q;q)_k (q;q)_{n-k} = (q;q)_n$. -/
theorem qBinom_mul_qPochhammer_mul_qPochhammer [CommRing R] (q : R) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom n k q * qPochhammer q q k * qPochhammer q q (n - k)
        = qPochhammer q q n := by
  intro n
  induction n with
  | zero =>
    rintro k hk
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    rintro (_ | k) hk
    · simp
    obtain hlt | rfl : k + 1 ≤ n ∨ n = k := by omega
    · -- Interior case: write `n = k + 1 + m` and feed in both induction hypotheses.
      obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
      have ih1 := ih (show k + 1 ≤ k + 1 + m by omega)
      have ih2 := ih (show k ≤ k + 1 + m by omega)
      rw [show k + 1 + m - (k + 1) = m from by omega, qPochhammer_succ q q k] at ih1
      rw [show k + 1 + m - k = m + 1 from by omega, qPochhammer_succ q q m] at ih2
      rw [qBinom_succ_succ, show k + 1 + m + 1 - (k + 1) = m + 1 from by omega,
        show k + 1 + m - k = m + 1 from by omega, qPochhammer_succ q q k,
        qPochhammer_succ q q m, qPochhammer_succ q q (k + 1 + m)]
      linear_combination (1 - q * q ^ m) * ih1 + q ^ (m + 1) * (1 - q * q ^ k) * ih2
    · -- Diagonal case `k = n`.
      rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self _), qBinom_self,
        Nat.sub_self, Nat.sub_self, pow_zero, qPochhammer_zero]
      ring

end qSeries
