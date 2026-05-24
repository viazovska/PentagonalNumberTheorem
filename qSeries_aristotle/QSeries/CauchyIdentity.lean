import QSeries.InfPochhammer

/-!
# The Cauchy identity (infinite q-binomial theorem)

This file proves the **infinite q-binomial / Cauchy identity**:
for $\|q\| < 1$ and $\|z\| < 1$,
$$\sum_{n=0}^{\infty} \frac{(a;q)_n}{(q;q)_n} z^n = \frac{(az;q)_\infty}{(z;q)_\infty}.$$

The proof follows Heine's classical functional-equation argument.

## Main results

* `qSeries.qBinom_infinite_thm` — the Cauchy identity.
-/

open Finset Filter
open scoped Topology

namespace qSeries

section CauchyIdentity

/-! ### The coefficient sequence -/

/-- The coefficient sequence $c_n = (a;q)_n / (q;q)_n$. -/
noncomputable def cauchyCoeff (a q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer a q n / qPochhammer q q n

@[simp] theorem cauchyCoeff_zero (a q : ℂ) : cauchyCoeff a q 0 = 1 := by
  simp [cauchyCoeff]

/-- **Coefficient recurrence.** $c_{n+1}(1 - q^{n+1}) = c_n(1 - aq^n)$. -/
theorem cauchyCoeff_succ_mul {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) (n : ℕ) :
    cauchyCoeff a q (n + 1) * (1 - q ^ (n + 1))
      = cauchyCoeff a q n * (1 - a * q ^ n) := by
  unfold cauchyCoeff
  have hqn : qPochhammer q q n ≠ 0 := qPochhammer_q_q_ne_zero hq n
  have hqn1 : qPochhammer q q (n + 1) ≠ 0 := qPochhammer_q_q_ne_zero hq (n + 1)
  rw [qPochhammer_succ a q n, qPochhammer_succ q q n,
      show (1 : ℂ) - q * q ^ n = 1 - q ^ (n + 1) from by ring]
  have hq_ne : (1 : ℂ) - q ^ (n + 1) ≠ 0 := by
    intro habs
    apply hqn1
    rw [qPochhammer_succ q q n,
        show (1 : ℂ) - q * q ^ n = 1 - q ^ (n + 1) from by ring,
        habs, mul_zero]
  field_simp

/-- **Boundedness of the coefficients.** -/
theorem cauchyCoeff_bounded {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    ∃ C, ∀ n, ‖cauchyCoeff a q n‖ ≤ C := by
  have hnum : Tendsto (fun n => ‖qPochhammer a q n‖) atTop
      (𝓝 ‖qPochhammerInf a q‖) := (tendsto_qPochhammer hq).norm
  have hden : Tendsto (fun n => ‖qPochhammer q q n‖) atTop
      (𝓝 ‖qPochhammerInf q q‖) := (tendsto_qPochhammer hq).norm
  obtain ⟨M, hM⟩ : ∃ M, ∀ n, ‖qPochhammer a q n‖ ≤ M := by
    rcases hnum.bddAbove_range with ⟨M, hM⟩
    exact ⟨M, fun n => hM ⟨n, rfl⟩⟩
  have hden_ne : qPochhammerInf q q ≠ 0 := by
    apply qPochhammerInf_ne_zero_of_factors hq
    intro k h
    rw [show (1 : ℂ) - q * q ^ k = 1 - q ^ (k + 1) from by ring] at h
    have h1 : q ^ (k + 1) = 1 := by linear_combination -h
    have hn1 : ‖q ^ (k + 1)‖ = 1 := by rw [h1]; simp
    rw [norm_pow] at hn1
    have : ‖q‖ ^ (k + 1) < 1 :=
      pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero k)
    linarith
  have hden_pos : 0 < ‖qPochhammerInf q q‖ := norm_pos_iff.mpr hden_ne
  set ε : ℝ := ‖qPochhammerInf q q‖ / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have hev : ∀ᶠ n in atTop, ε < ‖qPochhammer q q n‖ := by
    have := hden.eventually (eventually_gt_nhds (half_lt_self hden_pos))
    simpa [hε_def] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max (M / ε) ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖cauchyCoeff a q k‖)), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hd_lt : ε < ‖qPochhammer q q n‖ := hN n hn
    unfold cauchyCoeff
    rw [norm_div]
    have hineq : ‖qPochhammer a q n‖ / ‖qPochhammer q q n‖ ≤ M / ε := by
      apply div_le_div₀ (le_trans (norm_nonneg _) (hM n)) (hM n) hε_pos hd_lt.le
    exact le_trans hineq (le_max_left _ _)
  · have hn' : n < N := Nat.lt_of_not_le hn
    apply le_trans _ (le_max_right (M / ε) _)
    exact Finset.le_sup' (fun k => ‖cauchyCoeff a q k‖)
      (Finset.mem_range.mpr (Nat.lt_succ_of_lt hn'))

/-! ### Summability of the Cauchy series -/

/-- The series $\sum_n c_n z^n$ is summable for $\|z\| < 1$. -/
theorem cauchy_summable {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) := by
  obtain ⟨C, hC⟩ := cauchyCoeff_bounded hq a
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  apply Summable.of_norm_bounded (g := fun n => C * ‖z‖ ^ n)
  · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hC n) le_rfl (pow_nonneg (norm_nonneg z) n) hCnn

/-! ### Functional equations -/

/-- **Functional equation for $G$.**
$(1-z)\, G(z) = (1 - az)\, G(qz)$. -/
theorem cauchy_functional_eq_G (a z : ℂ) {q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    (1 - z) * (qPochhammerInf (a * z) q / qPochhammerInf z q)
      = (1 - a * z) *
          (qPochhammerInf (a * z * q) q / qPochhammerInf (z * q) q) := by
  have hzq : ‖z * q‖ < 1 := by
    rw [norm_mul]
    by_cases hzz : z = 0
    · simp [hzz]
    · have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzz
      calc ‖z‖ * ‖q‖ < ‖z‖ * 1 :=
              mul_lt_mul_of_pos_left hq hz_pos
        _ = ‖z‖ := mul_one _
        _ < 1 := hz
  have hz_ne : qPochhammerInf z q ≠ 0 := qPochhammerInf_z_q_ne_zero hz hq
  have hzq_ne : qPochhammerInf (z * q) q ≠ 0 :=
    qPochhammerInf_z_q_ne_zero hzq hq
  have hGz : qPochhammerInf z q = (1 - z) * qPochhammerInf (z * q) q :=
    qPochhammerInf_recursion hq
  have hGaz : qPochhammerInf (a * z) q
                = (1 - a * z) * qPochhammerInf (a * z * q) q :=
    qPochhammerInf_recursion hq
  rw [hGz, hGaz]
  have hone_sub_z_ne : (1 : ℂ) - z ≠ 0 := by
    intro h; have hz1 : z = 1 := by linear_combination -h
    rw [hz1] at hz; norm_num at hz
  field_simp

/-! ### Functional equation for F (via power series) -/

private theorem hasSum_one_sub_mul_F {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => if n = 0 then (1 : ℂ)
                          else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
      ((1 - z) * ∑' n, cauchyCoeff a q n * z ^ n) := by
  set F := ∑' n, cauchyCoeff a q n * z ^ n
  have hSum : Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) :=
    cauchy_summable hq hz
  have hF : HasSum (fun n => cauchyCoeff a q n * z ^ n) F := hSum.hasSum
  have hshifted : HasSum (fun n => cauchyCoeff a q n * z ^ (n + 1)) (z * F) := by
    have h := hF.mul_left z
    convert h using 1; ext n; ring
  let g : ℕ → ℂ := fun n => if n = 0 then 0 else cauchyCoeff a q (n - 1) * z ^ n
  have hg_succ_eq : (fun n => g (n + 1))
                = (fun n => cauchyCoeff a q n * z ^ (n + 1)) := by
    funext n; simp [g]
  have hg_zero : g 0 = 0 := by simp [g]
  have hg : HasSum g (z * F) := by
    have h1 : HasSum (fun n => g (n + 1)) (z * F) := by
      rw [hg_succ_eq]; exact hshifted
    have h2 : (z * F) = (z * F) - ∑ i ∈ Finset.range 1, g i := by
      simp [hg_zero]
    rw [h2] at h1
    exact (hasSum_nat_add_iff' (f := g) 1).mp h1
  have hdiff : HasSum (fun n => cauchyCoeff a q n * z ^ n - g n) (F - z * F) :=
    hF.sub hg
  have hfunc : (fun n : ℕ => if n = 0 then (1 : ℂ)
                              else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
                = (fun n : ℕ => cauchyCoeff a q n * z ^ n - g n) := by
    funext n
    by_cases hn : n = 0
    · subst hn; simp [g, cauchyCoeff_zero]
    · simp only [if_neg hn, g]; ring
  rw [hfunc]
  have h_target : (1 - z) * F = F - z * F := by ring
  rw [h_target]
  exact hdiff

private theorem hasSum_one_sub_az_mul_F_qz {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => if n = 0 then (1 : ℂ)
                          else (cauchyCoeff a q n * q ^ n
                                  - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n)
      ((1 - a * z) * ∑' n, cauchyCoeff a q n * (q * z) ^ n) := by
  set Fqz := ∑' n, cauchyCoeff a q n * (q * z) ^ n
  have hqz : ‖q * z‖ < 1 := by
    rw [norm_mul]
    by_cases hzz : z = 0
    · simp [hzz]
    · have : 0 < ‖z‖ := norm_pos_iff.mpr hzz
      calc ‖q‖ * ‖z‖ < 1 * ‖z‖ := mul_lt_mul_of_pos_right hq this
        _ = ‖z‖ := one_mul _
        _ < 1 := hz
  have hF : HasSum (fun n => cauchyCoeff a q n * (q * z) ^ n) Fqz :=
    (cauchy_summable hq hqz).hasSum
  have hF' : HasSum (fun n => cauchyCoeff a q n * q ^ n * z ^ n) Fqz := by
    convert hF using 1; ext n; rw [mul_pow]; ring
  have hshifted : HasSum (fun n => a * cauchyCoeff a q n * q ^ n * z ^ (n + 1))
                          (a * z * Fqz) := by
    have h := hF'.mul_left (a * z)
    convert h using 1; ext n; ring
  let g : ℕ → ℂ := fun n => if n = 0 then 0
                              else a * cauchyCoeff a q (n - 1) * q ^ (n - 1) * z ^ n
  have hg_succ_eq : (fun n => g (n + 1))
                = (fun n => a * cauchyCoeff a q n * q ^ n * z ^ (n + 1)) := by
    funext n; simp [g]
  have hg_zero : g 0 = 0 := by simp [g]
  have hg : HasSum g (a * z * Fqz) := by
    have h1 : HasSum (fun n => g (n + 1)) (a * z * Fqz) := by
      rw [hg_succ_eq]; exact hshifted
    have h2 : (a * z * Fqz) = (a * z * Fqz) - ∑ i ∈ Finset.range 1, g i := by
      simp [hg_zero]
    rw [h2] at h1
    exact (hasSum_nat_add_iff' (f := g) 1).mp h1
  have hdiff : HasSum (fun n => cauchyCoeff a q n * q ^ n * z ^ n - g n)
                (Fqz - a * z * Fqz) := hF'.sub hg
  have hfunc : (fun n : ℕ => if n = 0 then (1 : ℂ)
                              else (cauchyCoeff a q n * q ^ n
                                      - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n)
                = (fun n : ℕ => cauchyCoeff a q n * q ^ n * z ^ n - g n) := by
    funext n
    by_cases hn : n = 0
    · subst hn; simp [g, cauchyCoeff_zero]
    · simp only [if_neg hn, g]; ring
  rw [hfunc]
  have h_target : (1 - a * z) * Fqz = Fqz - a * z * Fqz := by ring
  rw [h_target]
  exact hdiff

/-- **Functional equation for $F$.**
$(1-z)\, F(z) = (1 - az)\, F(qz)$. -/
theorem cauchy_functional_eq_F {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    (1 - z) * ∑' n, cauchyCoeff a q n * z ^ n
      = (1 - a * z) * ∑' n, cauchyCoeff a q n * (q * z) ^ n := by
  have hL := hasSum_one_sub_mul_F (a := a) (q := q) (z := z) hq hz
  have hR := hasSum_one_sub_az_mul_F_qz (a := a) (q := q) (z := z) hq hz
  have hfunc : (fun n : ℕ => if n = 0 then (1 : ℂ)
                  else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
              = (fun n : ℕ => if n = 0 then (1 : ℂ)
                  else (cauchyCoeff a q n * q ^ n
                          - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n) := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [if_neg hn]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp only [Nat.succ_sub_one]
      have hrec := cauchyCoeff_succ_mul (a := a) hq m
      have hcoef : cauchyCoeff a q (m + 1) - cauchyCoeff a q m
                    = cauchyCoeff a q (m + 1) * q ^ (m + 1)
                        - a * cauchyCoeff a q m * q ^ m := by
        linear_combination hrec
      rw [hcoef]
  rw [hfunc] at hL
  exact hL.unique hR

/-! ### Iteration -/

/-- **Iterated functional equation.** -/
theorem iterated_functional_eq_disc {H : ℂ → ℂ} {a q : ℂ} (hq : ‖q‖ < 1)
    (hH : ∀ w, ‖w‖ < 1 → (1 - w) * H w = (1 - a * w) * H (q * w))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∀ n : ℕ, H z * qPochhammer z q n
              = H (q ^ n * z) * qPochhammer (a * z) q n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hqnz : ‖q ^ n * z‖ < 1 := by
        rw [norm_mul, norm_pow]
        calc ‖q‖ ^ n * ‖z‖
            ≤ 1 * ‖z‖ := by
              apply mul_le_mul_of_nonneg_right
                (pow_le_one₀ (norm_nonneg _) hq.le) (norm_nonneg _)
          _ = ‖z‖ := one_mul _
          _ < 1 := hz
      have key : (1 - q ^ n * z) * H (q ^ n * z)
                  = (1 - a * (q ^ n * z)) * H (q * (q ^ n * z)) := hH _ hqnz
      have hqq : q * (q ^ n * z) = q ^ (n + 1) * z := by ring
      rw [hqq] at key
      rw [qPochhammer_succ z q n, qPochhammer_succ (a * z) q n]
      have hzqn : (1 : ℂ) - z * q ^ n = 1 - q ^ n * z := by ring
      have hazqn : (1 : ℂ) - a * z * q ^ n = 1 - a * (q ^ n * z) := by ring
      rw [hzqn, hazqn]
      calc H z * (qPochhammer z q n * (1 - q ^ n * z))
          = (H z * qPochhammer z q n) * (1 - q ^ n * z) := by ring
        _ = (H (q ^ n * z) * qPochhammer (a * z) q n) * (1 - q ^ n * z) := by rw [ih]
        _ = qPochhammer (a * z) q n * ((1 - q ^ n * z) * H (q ^ n * z)) := by ring
        _ = qPochhammer (a * z) q n *
              ((1 - a * (q ^ n * z)) * H (q ^ (n + 1) * z)) := by rw [key]
        _ = H (q ^ (n + 1) * z) *
              (qPochhammer (a * z) q n * (1 - a * (q ^ n * z))) := by ring

/-! ### The limit of F(q^n z) -/

/-- **$F(q^n z) \to 1$ as $n \to \infty$**, by Tannery's theorem. -/
theorem tendsto_F_qpow {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Tendsto (fun n : ℕ => ∑' k, cauchyCoeff a q k * (q ^ n * z) ^ k)
      atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := cauchyCoeff_bounded hq a
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  let g : ℕ → ℂ := fun k => if k = 0 then 1 else 0
  let bound : ℕ → ℝ := fun k => C * ‖z‖ ^ k
  have h_sum : Summable bound :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C
  have hab : ∀ k : ℕ, Tendsto (fun n : ℕ => cauchyCoeff a q k * (q ^ n * z) ^ k)
                              atTop (𝓝 (g k)) := by
    intro k
    by_cases hk : k = 0
    · simp [g, hk]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hpow : ∀ n : ℕ, cauchyCoeff a q (m + 1) * (q ^ n * z) ^ (m + 1)
                            = cauchyCoeff a q (m + 1) * z ^ (m + 1) * (q ^ (m + 1)) ^ n := by
        intro n
        rw [mul_pow, ← pow_mul, mul_comm n (m + 1), pow_mul]
        ring
      simp only [g, if_neg (Nat.succ_ne_zero m)]
      have hqpow : ‖q ^ (m + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero m)
      have htend : Tendsto (fun n : ℕ => (q ^ (m + 1)) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hqpow
      have hmul := htend.const_mul (cauchyCoeff a q (m + 1) * z ^ (m + 1))
      simp only [mul_zero] at hmul
      exact hmul.congr (fun n => (hpow n).symm)
  have h_bound : ∀ᶠ n in atTop, ∀ k : ℕ,
                    ‖cauchyCoeff a q k * (q ^ n * z) ^ k‖ ≤ bound k := by
    apply Filter.Eventually.of_forall
    intro n k
    simp only [bound]
    rw [norm_mul, norm_pow, norm_mul, norm_pow, mul_pow]
    calc ‖cauchyCoeff a q k‖ * ((‖q‖ ^ n) ^ k * ‖z‖ ^ k)
        = ‖cauchyCoeff a q k‖ * (‖q‖ ^ n) ^ k * ‖z‖ ^ k := by ring
      _ ≤ C * 1 * ‖z‖ ^ k := by
          gcongr
          · exact hC k
          · exact pow_le_one₀ (pow_nonneg (norm_nonneg _) n)
              (pow_le_one₀ (norm_nonneg _) hq.le)
      _ = C * ‖z‖ ^ k := by ring
  have h := tendsto_tsum_of_dominated_convergence h_sum hab h_bound
  have hgsum : (∑' k : ℕ, g k) = 1 := by
    rw [tsum_eq_single 0 (fun k hk => by simp [g, hk])]
    simp [g]
  rw [hgsum] at h
  exact h

/-! ### The main theorem -/

/-- **Infinite q-binomial / Cauchy identity.**

For $\|q\| < 1$ and $\|z\| < 1$,
$$\sum_{n=0}^{\infty} \frac{(a;q)_n}{(q;q)_n} z^n = \frac{(az;q)_\infty}{(z;q)_\infty}.$$ -/
theorem qBinom_infinite_thm (a z q : ℂ) (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => qPochhammer a q n / qPochhammer q q n * z ^ n)
      (qPochhammerInf (a * z) q / qPochhammerInf z q) := by
  change HasSum (fun n => cauchyCoeff a q n * z ^ n) _
  have hF_summable : Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) :=
    cauchy_summable hq hz
  set F : ℂ := ∑' n, cauchyCoeff a q n * z ^ n
  have hden_ne : qPochhammerInf z q ≠ 0 := qPochhammerInf_z_q_ne_zero hz hq
  suffices hFG : F * qPochhammerInf z q = qPochhammerInf (a * z) q by
    have : F = qPochhammerInf (a * z) q / qPochhammerInf z q := by
      field_simp
      exact hFG
    rw [← this]
    exact hF_summable.hasSum
  let H : ℂ → ℂ := fun w => if ‖w‖ < 1 then ∑' k, cauchyCoeff a q k * w ^ k else 0
  have hH_disc : ∀ w, ‖w‖ < 1 → H w = ∑' k, cauchyCoeff a q k * w ^ k := by
    intro w hw; simp [H, hw]
  have hH_fe : ∀ w, ‖w‖ < 1 → (1 - w) * H w = (1 - a * w) * H (q * w) := by
    intro w hw
    rw [hH_disc w hw]
    have hqw : ‖q * w‖ < 1 := by
      rw [norm_mul]
      by_cases hww : w = 0
      · simp [hww]
      · have : 0 < ‖w‖ := norm_pos_iff.mpr hww
        calc ‖q‖ * ‖w‖ < 1 * ‖w‖ :=
            mul_lt_mul_of_pos_right hq this
          _ = ‖w‖ := one_mul _
          _ < 1 := hw
    rw [hH_disc _ hqw]
    exact cauchy_functional_eq_F hq hw
  have hiter := iterated_functional_eq_disc hq hH_fe hz
  have hF_eq_Hz : F = H z := (hH_disc z hz).symm
  have key : ∀ n : ℕ,
      F * qPochhammer z q n = H (q ^ n * z) * qPochhammer (a * z) q n := by
    intro n
    rw [hF_eq_Hz]; exact hiter n
  have hLHS_lim : Tendsto (fun n => F * qPochhammer z q n) atTop
      (𝓝 (F * qPochhammerInf z q)) :=
    (tendsto_qPochhammer hq).const_mul F
  have hqnz : ∀ n : ℕ, ‖q ^ n * z‖ < 1 := by
    intro n
    rw [norm_mul, norm_pow]
    calc ‖q‖ ^ n * ‖z‖
        ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) hq.le) (norm_nonneg _)
      _ = ‖z‖ := one_mul _
      _ < 1 := hz
  have hH_eq : (fun n => H (q ^ n * z))
                = (fun n => ∑' k, cauchyCoeff a q k * (q ^ n * z) ^ k) := by
    ext n; exact hH_disc _ (hqnz n)
  have hH_lim : Tendsto (fun n => H (q ^ n * z)) atTop (𝓝 1) := by
    rw [hH_eq]; exact tendsto_F_qpow hq hz
  have hRHS_lim : Tendsto (fun n => H (q ^ n * z) * qPochhammer (a * z) q n)
      atTop (𝓝 (1 * qPochhammerInf (a * z) q)) :=
    hH_lim.mul (tendsto_qPochhammer hq)
  rw [one_mul] at hRHS_lim
  exact tendsto_nhds_unique (by simpa [key] using hLHS_lim) hRHS_lim

end CauchyIdentity

end qSeries
