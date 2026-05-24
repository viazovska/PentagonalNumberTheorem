import QSeries.EulerIdentities
import QSeries.JTP_KeyIdentity

/-!
# Core lemmas for the Jacobi triple product proof

These lemmas express the product `(q;q)_∞ (-z;q)_∞` as a single series, ready to
be combined with the expansion of `(-q/z;q)_∞` in a Cauchy product (see
`QSeries.JacobiTripleProduct`).

Key identity: $(q;q)_∞ / (q;q)_n = (q^{n+1};q)_∞$ (telescoping)
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-! ## Telescoping identity for qPochhammerInf -/

/-
Telescoping: $(q;q)_∞ = (q;q)_n ⋅ (q^{n+1};q)_∞$.
-/
theorem qPochhammerInf_eq_mul {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf q q = qPochhammer q q n * qPochhammerInf (q * q ^ n) q := by
  induction' n with n ih;
  · norm_num [ qPochhammer ];
  · rw [ ih, qPochhammer_succ ];
    rw [ mul_assoc, qPochhammerInf_recursion ] ; ring;
    grind

/-
Euler 2nd identity at $z = -q^{n+1}$:
$(q^{n+1};q)_∞ = ∑_m (-1)^m q^{C(m,2) + m(n+1)} / (q;q)_m$
-/
theorem euler_second_at_neg_qpow {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * (-q ^ (n + 1)) ^ m / qPochhammer q q m)
      (qPochhammerInf (q ^ (n + 1)) q) := by
  convert euler_second_identity hq _ using 1;
  · norm_num;
  · simpa using pow_lt_one₀ ( norm_nonneg q ) hq ( by linarith )

/-
The product $(q;q)_∞ (-z;q)_∞$ as a HasSum.
-/
theorem qPochhammerInf_prod_hasSum {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q)
      (qPochhammerInf q q * qPochhammerInf (-z) q) := by
  convert HasSum.mul_left ( qPochhammerInf q q ) ( euler_second_identity hq hz ) using 1;
  ext n; rw [ qPochhammerInf_eq_mul hq n ] ; ring;
  grind +suggestions

/-- Key identity: the n-th coefficient of the product (q;q)_∞ (-z;q)_∞
expanded using Euler 2nd, multiplied by (q;q)_∞, gives the JTP coefficient.
Specifically: qPochhammerInf (q * q^n) q = qPochhammerInf (q^(n+1)) q. -/
theorem qPochhammerInf_shift {q : ℂ} (n : ℕ) :
    qPochhammerInf (q * q ^ n) q = qPochhammerInf (q ^ (n + 1)) q := by
  congr 1; ring


end

end qSeries
