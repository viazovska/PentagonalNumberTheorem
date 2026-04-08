
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Int.Basic

open BigOperators Finset PowerSeries

variable {R : Type*} [CommRing R]

/-- The pentagonal numbers: (3k² - k)/2 for k ∈ ℤ -/
def pentagonal (k : ℤ) : ℕ :=
  Int.natAbs ((3 * k^2 - k) / 2)

/-- Helper function to get the sign and exponent for the pentagonal series -/
def pentagonal_coeff (k : ℤ) : R × ℕ :=
  ((-1 : R)^(Int.natAbs k), pentagonal k)

/-- Euler's Pentagonal Number Theorem for formal power series -/

theorem euler_pentagonal_theorem_alt (R : Type*) [CommRing R] :
  ∏ (n : ℕ) in range ∞, (1 - X^(n+1) : R⟦X⟧) =
  ∑ (k : ℤ), (-1 : R)^k * X^(pentagonal k) :=
by
  sorry





/-- The coefficient of X^n in the pentagonal series -/
def pentagonal_series_coeff (n : ℕ) : R :=
  ∑ k in (Finset.range (2 * n + 1)).filter (fun k =>
    pentagonal (k - n : ℤ) = n ∨ pentagonal (-(k - n : ℤ)) = n),
  (-1 : R)^(Int.natAbs (k - n))

/-- The main equality as power series coefficients -/
theorem euler_pentagonal_coeff (R : Type*) [CommRing R] (n : ℕ) :
  (∏ (k : ℕ), (1 - X^(k+1) : R⟦X⟧)).coeff n =
  pentagonal_series_coeff n :=
by
  sorry
