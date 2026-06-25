/-
Copyright (c) 2026 Jonathan Conrad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad
-/
import EulerPentagonalNumberTheorem_Franklin.Defs
import EulerPentagonalNumberTheorem_Franklin.Helpers
import EulerPentagonalNumberTheorem_Franklin.Lemmas
import EulerPentagonalNumberTheorem_Franklin.FormalPowerSeries

/-! # Pentagonal Number Theorem — Main Module

This file imports all components of the formalization of the
Pentagonal Number Theorem, following the source document
"Pentagonal Number Theorem" by Jonathan Conrad, Paula Mürmann, Maryna Viazovska (May 11, 2026).

## Main results

* `Defs.lean`: Core definitions (partitions into distinct parts, base, slope,
  slopeSet, the three partition classes α/β/special, Franklin's involution operations)
* `Helpers.lean`: Helper lemmas about `consecutiveTopRun`, partition membership,
  and properties of αOp/βOp
* `Lemmas.lean`: Main theorems including Lemma 11 (disjointness of α/β/special),
  Lemma 12 (union decomposition), Definition 13 properties (smkSet/spkSet cardinality
  and sum), Lemma 14 (special partition characterization), Lemmas 16–19 (Franklin's
  involution: well-definedness and inverse properties), Lemma 20–21 (bijection and
  cardinality equality), Lemma 22 (parity flip), Lemma 23 (parity-restricted cardinality
  equalities), and Lemma 24 (main result): pe(n) - po(n) = (-1)^k for pentagonal n,
  0 otherwise.
* `FormalPowerSeries.lean`: Informal statements of the formal power series identities
  (Lemma 3, Lemma 5, Theorem 7, Theorem 25)
-/
