/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import Mathlib
import PentagonalNumberTheorem

/-!
# Public solution

Proves the statements of `Challenge.lean` from this project's own development. Each proof is a
bridge: the challenge states the result with every project definition unfolded into Mathlib
vocabulary, and the project theorem discharges it directly, which typechecks precisely because
the two statements are definitionally equal.

The theorem signatures below must match `Challenge.lean` exactly -- that is what Comparator
compares. This module deliberately does **not** import `Challenge`.

`import Mathlib` above is **required and must not be removed**, even though
`PentagonalNumberTheorem` already provides every declaration this file mentions. Comparator
compares the two statements as elaborated terms, not as source text, so the instances they
pick up have to agree. `Challenge.lean` imports all of Mathlib, where `‖·‖` on `ℂ` resolves
through `CommCStarAlgebra.toNormedCommRing` / `instCommCStarAlgebraComplex`; the project's own
imports stop short of the C*-algebra hierarchy, so without this line the same source text
elaborates through `NormedField.toNormedCommRing` / `Complex.instNormedField` instead. The two
are definitionally equal -- which is why this file still compiles without the import -- but
Comparator rejects the mismatch, reporting "Challenge and solution theorem statement do not
match" on the first affected theorem. It affects the two `ℂ`-valued statements,
`jacobiTripleProduct` and `euler_pentagonal_number`; the two Franklin statements are over `ℤ`
and match either way.
-/

namespace PentagonalNumberTheorem.Challenge

open Finset

/-! ## Primary result — Franklin's involution -/

theorem franklin_pentagonal_number_theorem (n : ℕ) :
    (∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2 ∧
        ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 0).card : ℤ)
          - ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
              fun S => S.card % 2 = 1).card : ℤ)
          = (-1 : ℤ) ^ k.natAbs)
      ∨ ((¬ ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2) ∧
        ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 0).card : ℤ)
          - ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
              fun S => S.card % 2 = 1).card : ℤ)
          = 0) :=
  PentagonalNumberTheorem.Franklin.euler_pentagonal_number_theorem_packaged n

theorem franklin_coeff_prod_eq_pe_sub_po (n : ℕ) :
    (PowerSeries.coeff n) (∏ k ∈ Icc 1 n, (1 - PowerSeries.X ^ k : PowerSeries ℤ))
      = ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 0).card : ℤ)
        - ((((Icc 1 n).powerset.filter fun S => S.sum id = n).filter
            fun S => S.card % 2 = 1).card : ℤ) :=
  PentagonalNumberTheorem.Franklin.coeff_prod_eq_pe_sub_po n

/-! ## Accompanying extension — the q-series / Jacobi triple product route -/

theorem jacobiTripleProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hz' : z ≠ 0) :
    (∏' k : ℕ, (1 - q * q ^ k)) * (∏' k : ℕ, (1 - -z * q ^ k)) *
        (∏' k : ℕ, (1 - -q / z * q ^ k)) =
      (∑' k : ℕ, z ^ k * q ^ k.choose 2)
        + ∑' m : ℕ, (z⁻¹) ^ (m + 1) * q ^ (m + 2).choose 2 :=
  QSeries.jacobiTripleProduct hq hz hz'

theorem euler_pentagonal_number {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q * q ^ k)) =
      (∑' k : ℕ, (-1 : ℂ) ^ k * q ^ (((k : ℤ) * (3 * (k : ℤ) - 1) / 2).toNat))
        + ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) *
            q ^ ((-((k : ℤ) + 1) * (3 * -((k : ℤ) + 1) - 1) / 2).toNat) :=
  QSeries.euler_pentagonal_number hq

end PentagonalNumberTheorem.Challenge
