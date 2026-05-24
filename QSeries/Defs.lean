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

/-! ### Finite q-Pochhammer symbol -/

/-- **Finite q-Pochhammer symbol.**
$(a;q)_n = \prod_{k=0}^{n-1} (1 - a q^k)$. -/
def qPochhammer [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ k ∈ range n, (1 - a * q ^ k)

@[simp]
theorem qPochhammer_zero [CommRing R] (a q : R) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]

/-- **Recurrence for q-Pochhammer.** $(a;q)_{n+1} = (a;q)_n \cdot (1 - a q^n)$. -/
theorem qPochhammer_succ [CommRing R] (a q : R) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by
  simp [qPochhammer, prod_range_succ]

/-! ### Gaussian binomial coefficient -/

/-- **Gaussian binomial coefficient** $\binom{n}{k}_q$.

Defined by the q-Pascal recurrence so that the result is always a polynomial
in $q$ (no division). The boundary cases are
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

/-- **Closed-form identity.**
For $k \leq n$: $\binom{n}{k}_q (q;q)_k (q;q)_{n-k} = (q;q)_n$. -/
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
      · simp
      · rcases lt_or_eq_of_le hk with hlt | heq
        · have hk1 : k + 1 ≤ n := Nat.lt_succ_iff.mp hlt
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
        · have hkn : k = n := by omega
          rw [hkn, qBinom_succ_succ,
              qBinom_eq_zero_of_lt q (Nat.lt_succ_self _),
              qBinom_self, Nat.sub_self, pow_zero,
              show (n + 1) - (n + 1) = 0 from by omega,
              qPochhammer_zero]
          ring

end qSeries
