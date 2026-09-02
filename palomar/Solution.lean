/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import QSeries

/-!
# Palomar solution

Proves the statements of `Challenge.lean` from the project's own development. Each proof is a
bridge: unfold the project definitions and apply the corresponding project theorem. The
statements below must match `Challenge.lean` character for character in their `theorem`
signatures -- Comparator checks exactly that.
-/

namespace PentagonalNumberTheorem.Challenge

open QSeries

theorem euler_pentagonal_number {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q * q ^ k)) =
      (∑' k : ℕ, (-1 : ℂ) ^ k * q ^ (((k : ℤ) * (3 * (k : ℤ) - 1) / 2).toNat))
        + ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) *
            q ^ ((-((k : ℤ) + 1) * (3 * -((k : ℤ) + 1) - 1) / 2).toNat) :=
  QSeries.euler_pentagonal_number hq

theorem jacobiTripleProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    (∏' k : ℕ, (1 - q * q ^ k)) * (∏' k : ℕ, (1 - -z * q ^ k)) *
        (∏' k : ℕ, (1 - -q / z * q ^ k)) =
      (∑' k : ℕ, z ^ k * q ^ k.choose 2)
        + ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2 :=
  QSeries.jacobiTripleProduct hq hz hz'

end PentagonalNumberTheorem.Challenge
