/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import EulerPentagonalNumberTheorem_Franklin
import QSeries

/-!
# Euler's pentagonal number theorem — top-level entry point

This module imports both formalizations in this repository. They are independent: neither
route uses a lemma from the other.

* `EulerPentagonalNumberTheorem_Franklin` — Franklin's sign-reversing involution on partitions
  into distinct parts, giving the coefficient identity
  `[qⁿ] ∏_{k=1}^{n} (1 - qᵏ) = p_e(n) - p_o(n)`, which is `(-1)^k` at generalized pentagonal
  `n = k(3k-1)/2` and `0` otherwise.

* `QSeries` — a development of q-Pochhammer symbols, the Gaussian binomial coefficient, Euler's
  two identities and the Cauchy identity, culminating in the Jacobi triple product both as a
  formal power series identity over an arbitrary commutative ring
  (`QSeries.FormalPowerSeries.jacobiTripleProduct`) and analytically over `ℂ` for `‖q‖ < 1`
  (`QSeries.jacobiTripleProduct`), from which Euler's pentagonal number theorem for the infinite
  product follows by specialization (`QSeries.euler_pentagonal_number`).
-/
