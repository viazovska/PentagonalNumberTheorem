/- minimal_hybrid_lean.lean — Lean half of the minimal hybrid PNT proof.

   Lean discharges the four hard structural lemmas that the Stainless half
   (`minimal_hybrid_stainless.scala`) ASSUMES via `@extern`, and then states and
   proves the cardinality conclusion — Euler's Pentagonal Number Theorem —
   which Stainless cannot express. Each `bridge_*` lemma below is the Lean
   statement the corresponding Stainless `@extern` must be checked against.

   Builds against the verified development in `Aristotle/` (see `INTERFACE.md`
   for the Finset ↔ sorted-List representation correspondence).
-/
import Aristotle.Lemmas
open Finset

/- ====================================================================== -/
/-  Bridge: the lemmas ASSUMED in minimal_hybrid_stainless.scala,          -/
/-  PROVED here (one line each, citing the verified Aristotle theorems).   -/
/-  Human-check: each statement matches the @extern signature.            -/
/- ====================================================================== -/

-- @extern alpha_in_beta   :  S ∈ 𝒫_α  →  α(S) ∈ 𝒫_β
theorem bridge_alpha_in_beta (n : ℕ) (S : Finset ℕ) (h : S ∈ DPalpha n) :
    alphaOp S ∈ DPbeta n := alphaOp_mem_DPbeta n S h

-- @extern beta_in_alpha    :  S ∈ 𝒫_β  →  β(S) ∈ 𝒫_α
theorem bridge_beta_in_alpha (n : ℕ) (S : Finset ℕ) (h : S ∈ DPbeta n) :
    betaOp S ∈ DPalpha n := betaOp_mem_DPalpha n S h

-- @extern beta_alpha_id    :  S ∈ 𝒫_α  →  β(α(S)) = S
theorem bridge_beta_alpha_id (n : ℕ) (S : Finset ℕ) (h : S ∈ DPalpha n) :
    betaOp (alphaOp S) = S := betaOp_alphaOp n S h

-- @extern alpha_beta_id    :  S ∈ 𝒫_β  →  α(β(S)) = S
theorem bridge_alpha_beta_id (n : ℕ) (S : Finset ℕ) (h : S ∈ DPbeta n) :
    alphaOp (betaOp S) = S := alphaOp_betaOp n S h

/- ====================================================================== -/
/-  The conclusion Stainless cannot state: Euler's Pentagonal Number       -/
/-  Theorem, p_e(n) − p_o(n), assembled from the verified Aristotle proofs. -/
/- ====================================================================== -/

/-- Non-pentagonal n: the even and odd distinct-partition counts coincide. -/
theorem pnt_nonpentagonal (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 - k)
    (h2 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 + k) :
    (pe n : ℤ) - po n = 0 := pe_minus_po_nonpent n hn h1 h2

/-- Pentagonal n = (3k²−k)/2 : the signed count is (−1)^k. -/
theorem pnt_pentagonal_minus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 - k) :
    (pe n : ℤ) - po n = (-1) ^ k := pe_minus_po_pent_minus n k hk hn

/-- Pentagonal n = (3k²+k)/2 : the signed count is (−1)^k. -/
theorem pnt_pentagonal_plus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 + k) :
    (pe n : ℤ) - po n = (-1) ^ k := pe_minus_po_pent_plus n k hk hn
