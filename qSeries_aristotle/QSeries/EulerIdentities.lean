import QSeries.CauchyIdentity
import QSeries.FiniteBinomial

/-!
# Euler's q-exponential identities

Two classical specializations of the Cauchy identity:

1. **First Euler identity** ($a = 0$):
   $$\frac{1}{(z;q)_\infty} = \sum_{n \geq 0} \frac{z^n}{(q;q)_n}.$$

2. **Second Euler identity** (limit of the finite q-binomial theorem):
   $$(-z;q)_\infty = \sum_{n \geq 0} \frac{q^{\binom{n}{2}}}{(q;q)_n} z^n.$$

## Main results

* `qSeries.euler_first_identity` — the first Euler identity.
* `qSeries.euler_second_identity` — the second Euler identity.
-/

open Finset Filter
open scoped Topology

namespace qSeries

variable {R : Type*}

/-! ## First Euler identity -/

/-- $(0;q)_n = 1$ for all $n$. -/
@[simp]
theorem qPochhammer_zero_left [CommRing R] (q : R) (n : ℕ) :
    qPochhammer 0 q n = 1 := by
  simp [qPochhammer]

/-- $(0;q)_\infty = 1$. -/
@[simp]
theorem qPochhammerInf_zero_left (q : ℂ) : qPochhammerInf 0 q = 1 := by
  simp [qPochhammerInf]

/-- **First Euler identity.**
$$\sum_{n=0}^{\infty} \frac{z^n}{(q;q)_n} = \frac{1}{(z;q)_\infty}$$
for $\|q\| < 1$ and $\|z\| < 1$. -/
theorem euler_first_identity {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / qPochhammer q q n)
      (1 / qPochhammerInf z q) := by
  have h := qBinom_infinite_thm 0 z q hq hz
  simp only [qPochhammer_zero_left, one_div] at h
  convert h using 1
  · ext n; ring
  · simp [zero_mul]

/-! ## Second Euler identity -/

section SecondEuler

/-
The finite q-binomial theorem at $z = -1$ gives 0 for $n \geq 1$:
$\prod_{k=0}^{n-1}(1 - q^k) = 0$ for $n \geq 1$.
-/
theorem qBinom_finite_at_neg_one [CommRing R] (q : R) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * qBinom n k q * (-1) ^ k = 0 := by
  rw [ ← qBinom_finite_thm ];
  exact Finset.prod_eq_zero ( Finset.mem_range.mpr hn ) ( by ring )

/-
Summability of $\sum q^{\binom{n}{2}} z^n / (q;q)_n$ for $\|z\| < 1$.
-/
theorem euler_second_summable {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n) := by
  -- We'll use the fact that if the series $\sum a_n$ converges, then so does $\sum c a_n$ for any constant $c$.
  have h_const_mul : Summable (fun n => z ^ n / qPochhammer q q n) := by
    convert euler_first_identity hq hz |> HasSum.summable using 1;
  rw [ ← summable_norm_iff ] at *;
  simp_all +decide [ mul_div_assoc ];
  exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => mul_le_of_le_one_left ( by positivity ) ( pow_le_one₀ ( by positivity ) hq.le ) ) h_const_mul

/-
**Second Euler identity.**
$$(-z;q)_\infty = \sum_{n=0}^{\infty} \frac{q^{\binom{n}{2}}}{(q;q)_n} z^n$$
for $\|q\| < 1$ and $\|z\| < 1$.
-/
theorem euler_second_identity {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n / qPochhammer q q n)
      (qPochhammerInf (-z) q) := by
  -- By the finite q-binomial theorem, we have:
  have h_finite : ∀ N : ℕ, ∏ k ∈ Finset.range N, (1 + z * q ^ k) = ∑ k ∈ Finset.range (N + 1), q ^ k.choose 2 * qBinom N k q * z ^ k := by
    exact fun N => qBinom_finite_thm q z N;
  -- By the properties of the q-Pochhammer symbol and the finite q-binomial theorem, we can rewrite the limit expression.
  have h_limit : Filter.Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), q ^ k.choose 2 * qBinom N k q * z ^ k) Filter.atTop (nhds (qPochhammerInf (-z) q)) := by
    have h_limit : Filter.Tendsto (fun N => ∏ k ∈ Finset.range N, (1 + z * q ^ k)) Filter.atTop (nhds (qPochhammerInf (-z) q)) := by
      convert tendsto_qPochhammer ( show ‖q‖ < 1 from hq ) using 1;
      exact funext fun n => Finset.prod_congr rfl fun _ _ => by ring;
    aesop;
  -- By the properties of the q-Pochhammer symbol and the finite q-binomial theorem, we can rewrite the limit expression using the fact that $qBinom N k q * qPochhammer q q k * qPochhammer q q (N - k) = qPochhammer q q N$.
  have h_rewrite : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), q ^ k.choose 2 * qBinom N k q * z ^ k = ∑ k ∈ Finset.range (N + 1), q ^ k.choose 2 * z ^ k / qPochhammer q q k * qPochhammer q q N / qPochhammer q q (N - k) := by
    intro N
    apply Finset.sum_congr rfl
    intro k hk
    have h_eq : qBinom N k q = qPochhammer q q N / (qPochhammer q q k * qPochhammer q q (N - k)) := by
      have := qBinom_mul_qPochhammer_mul_qPochhammer q ( show k ≤ N from Finset.mem_range_succ_iff.mp hk );
      rw [ eq_div_iff ];
      · rw [ ← mul_assoc, this ];
      · exact mul_ne_zero ( qPochhammer_q_q_ne_zero hq k ) ( qPochhammer_q_q_ne_zero hq ( N - k ) )
    rw [h_eq]
    field_simp [mul_comm, mul_assoc, mul_left_comm];
  -- By the properties of the q-Pochhammer symbol and the finite q-binomial theorem, we can rewrite the limit expression using the fact that $qPochhammer q q N / qPochhammer q q (N - k) \to 1$ as $N \to \infty$.
  have h_limit_rewrite : Filter.Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), q ^ k.choose 2 * z ^ k / qPochhammer q q k * (qPochhammer q q N / qPochhammer q q (N - k))) Filter.atTop (nhds (∑' k, q ^ k.choose 2 * z ^ k / qPochhammer q q k)) := by
    have h_limit_rewrite : ∀ k : ℕ, Filter.Tendsto (fun N => qPochhammer q q N / qPochhammer q q (N - k)) Filter.atTop (nhds 1) := by
      intro k
      have h_limit_rewrite : Filter.Tendsto (fun N => qPochhammer q q (N + k) / qPochhammer q q N) Filter.atTop (nhds 1) := by
        have h_limit_rewrite : Filter.Tendsto (fun N => qPochhammer q q (N + k)) Filter.atTop (nhds (qPochhammerInf q q)) ∧ Filter.Tendsto (fun N => qPochhammer q q N) Filter.atTop (nhds (qPochhammerInf q q)) := by
          exact ⟨ tendsto_qPochhammer hq |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat k, tendsto_qPochhammer hq ⟩;
        convert h_limit_rewrite.1.div h_limit_rewrite.2 _ using 1 <;> norm_num [ qPochhammerInf_zero_left ];
        · rw [ div_self ];
          convert qPochhammerInf_z_q_ne_zero hq hq using 1;
        · exact qPochhammerInf_z_q_ne_zero ( by simpa ) hq;
      rw [ ← Filter.tendsto_add_atTop_iff_nat k ] ; aesop;
    have h_limit_rewrite : Filter.Tendsto (fun N => ∑' k, (if k < N + 1 then q ^ k.choose 2 * z ^ k / qPochhammer q q k * (qPochhammer q q N / qPochhammer q q (N - k)) else 0)) Filter.atTop (nhds (∑' k, q ^ k.choose 2 * z ^ k / qPochhammer q q k)) := by
      refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
      use fun k => ‖q ^ k.choose 2 * z ^ k / qPochhammer q q k‖ * ( SupSet.sSup ( Set.range ( fun N => ‖qPochhammer q q N / qPochhammer q q ( N - k )‖ ) ) );
      · have h_bounded : ∃ C, ∀ k : ℕ, sSup (Set.range (fun N => ‖qPochhammer q q N / qPochhammer q q (N - k)‖)) ≤ C := by
          have h_bounded : ∃ C, ∀ k : ℕ, ∀ N : ℕ, ‖qPochhammer q q N / qPochhammer q q (N - k)‖ ≤ C := by
            have h_bounded : ∃ C, ∀ N : ℕ, ‖qPochhammer q q N‖ ≤ C := by
              have h_bounded : Filter.Tendsto (fun N => ‖qPochhammer q q N‖) Filter.atTop (nhds (‖qPochhammerInf q q‖)) := by
                convert Filter.Tendsto.norm ( tendsto_qPochhammer hq ) using 1;
              exact ⟨ _, fun N => le_csSup ( h_bounded.bddAbove_range ) ⟨ N, rfl ⟩ ⟩;
            have h_bounded : ∃ C, ∀ N : ℕ, ‖1 / qPochhammer q q N‖ ≤ C := by
              have h_bounded : Filter.Tendsto (fun N => ‖1 / qPochhammer q q N‖) Filter.atTop (nhds (‖1 / qPochhammerInf q q‖)) := by
                convert Filter.Tendsto.norm ( tendsto_const_nhds.div ( tendsto_qPochhammer hq ) _ ) using 2 ; norm_num;
                exact qPochhammerInf_z_q_ne_zero ( by simpa ) hq;
              exact ⟨ _, fun N => le_csSup ( h_bounded.bddAbove_range ) ⟨ N, rfl ⟩ ⟩;
            obtain ⟨ C, hC ⟩ := h_bounded;
            use h_bounded.choose * C;
            intro k N; specialize hC ( N - k ) ; simp_all +decide [ div_eq_mul_inv ] ;
            exact mul_le_mul ( h_bounded.choose_spec N ) hC ( by positivity ) ( by exact le_trans ( by positivity ) ( h_bounded.choose_spec 0 ) );
          exact ⟨ h_bounded.choose, fun k => csSup_le ( Set.range_nonempty _ ) ( Set.forall_mem_range.mpr fun N => h_bounded.choose_spec k N ) ⟩;
        obtain ⟨ C, hC ⟩ := h_bounded;
        refine' Summable.of_nonneg_of_le ( fun k => mul_nonneg ( norm_nonneg _ ) ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ N, rfl ⟩ ; positivity ) ) ( fun k => mul_le_mul_of_nonneg_left ( hC k ) ( norm_nonneg _ ) ) _;
        refine' Summable.mul_right _ _;
        convert euler_second_summable hq hz |> Summable.norm using 1;
      · intro k;
        rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop k ] with N hN using if_pos <| by linarith ) ] ; simpa using tendsto_const_nhds.mul ( h_limit_rewrite k ) ;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN;
        intro k; split_ifs <;> norm_num;
        · gcongr;
          refine' le_csSup _ _;
          · have := h_limit_rewrite k;
            exact Filter.Tendsto.bddAbove_range ( by simpa using this.norm );
          · exact ⟨ N, rfl ⟩;
        · exact mul_nonneg ( div_nonneg ( mul_nonneg ( pow_nonneg ( norm_nonneg _ ) _ ) ( pow_nonneg ( norm_nonneg _ ) _ ) ) ( norm_nonneg _ ) ) ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ N, rfl ⟩ ; positivity );
    convert h_limit_rewrite using 2;
    rw [ tsum_eq_sum ];
    exacts [ Finset.sum_congr rfl fun i hi => by rw [ if_pos ( Finset.mem_range.mp hi ) ], fun i hi => if_neg ( by simpa using hi ) ];
  convert tendsto_nhds_unique h_limit_rewrite ( h_limit.congr fun N => by rw [ h_rewrite N ] ; exact Finset.sum_congr rfl fun _ _ => by ring ) using 1;
  constructor <;> intro h <;> rw [ Summable.tsum_eq_zero_add ] at * <;> norm_num at *;
  any_goals exact euler_second_summable hq hz;
  · convert tendsto_nhds_unique h_limit_rewrite ( h_limit.congr fun N => by rw [ h_rewrite N ] ; exact Finset.sum_congr rfl fun _ _ => by ring ) using 1;
  · convert Summable.hasSum _ using 1;
    · rw [ ← h, eq_comm, Summable.tsum_eq_zero_add ];
      · norm_num [ qPochhammer ];
      · convert euler_second_summable hq hz using 1;
    · convert euler_second_summable hq hz using 1

end SecondEuler

end qSeries