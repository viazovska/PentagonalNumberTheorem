import PentagonalNumberTheorem.odd_and_even_distinct_partitions

/-!
# Franklin's bijection — option-2 reformulation

Instead of defining a single involution `φ : Partitions → Partitions`
that fixes the pentagonal partitions, we factor the proof through:

* the **fixed-point set** `pentagonal_fixed_points n`,
* the complements `even_nonfixed n` and `odd_nonfixed n`,
* an explicit `Equiv` between those two complements built from
  `alpha_involution` / `beta_involution`.

Then `p_e n - p_o n = |fixed_even n| - |fixed_odd n|` reduces to a
direct cardinality computation, with no `if-then-else` cascade and no
need to prove `franklin ∘ franklin = id` on fixed points.
-/

open Finset

/-! ## Fixed points of Franklin's involution

The fixed points are exactly the partitions on which neither
`alpha_crit` nor `beta_crit` holds. Combinatorially, they are the
"staircases" `{b, b+1, …, 2b-1}` (size `b`, sum `b(3b-1)/2`) and
`{b, b+1, …, 2b-2}` (size `b-1`, sum `b(3b+1)/2 - b = (3b²+b)/2 - b`,
i.e. the other family of pentagonal numbers).
-/

/-- A staircase of length `b` starting at `b`: `{b, b+1, …, 2b-1}`. -/
def staircase_lower (b : ℕ) : Finset ℕ := Finset.Ico b (2 * b)

/-- A short staircase of length `b-1` starting at `b`:
    `{b, b+1, …, 2b-2}`. Empty when `b = 0`. -/
def staircase_upper (b : ℕ) : Finset ℕ := Finset.Ico b (2 * b - 1)

/-- Pentagonal fixed points of Franklin's involution at `n`: all
    partitions `s ∈ all_distinct_partitions n` for which neither
    `alpha_crit` nor `beta_crit` holds. -/
def pentagonal_fixed_points (n : ℕ) : Finset (Finset ℕ) :=
  (all_distinct_partitions n).filter (fun s =>
    if h : s.Nonempty then
      ¬ alpha_crit s h ∧ ¬ beta_crit s h
    else
      True)

/-- The fixed points that have an even number of parts. -/
def fixed_even (n : ℕ) : Finset (Finset ℕ) :=
  (pentagonal_fixed_points n).filter (fun s => s.card % 2 = 0)

/-- The fixed points that have an odd number of parts. -/
def fixed_odd (n : ℕ) : Finset (Finset ℕ) :=
  (pentagonal_fixed_points n).filter (fun s => s.card % 2 = 1)

/-! ## Characterization of fixed points

These two lemmas connect the abstract `pentagonal_fixed_points n` to
the concrete staircase families.
-/

/-- A nonempty partition fails both `alpha_crit` and `beta_crit` iff it
    is a staircase `{b, b+1, …, 2b-1}` or `{b, b+1, …, 2b-2}` for some
    `b ≥ 1`. -/
lemma fixed_point_iff_staircase (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x) :
    (¬ alpha_crit s hne ∧ ¬ beta_crit s hne) ↔
      (∃ b ≥ 1, s = staircase_lower b) ∨ (∃ b ≥ 1, s = staircase_upper b) := by
  sorry

/-- The lower staircase `{b, …, 2b-1}` partitions `b(3b-1)/2`. -/
lemma staircase_lower_sum (b : ℕ) :
    (staircase_lower b).sum id = b * (3 * b - 1) / 2 := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 from by norm_num)
  have hdvd : 2 ∣ b * (3 * b - 1) := by
    rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (3 * b - 1), by rw [hk]; ring⟩
    · refine ⟨b * (3 * k + 1), ?_⟩
      subst hk
      have : 3 * (2 * k + 1) - 1 = 2 * (3 * k + 1) := by omega
      rw [this]; ring
  rw [Nat.mul_div_cancel' hdvd]
  unfold staircase_lower
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [id_eq]
  rw [show 2 * b - b = b from by omega, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [show 2 * (b * b + ∑ i ∈ Finset.range b, i) =
          2 * (b * b) + (∑ i ∈ Finset.range b, i) * 2 from by ring,
      Finset.sum_range_id_mul_two]
  rcases b with _ | b'
  · simp
  · have h1 : (b' + 1) - 1 = b' := by omega
    have h2 : 3 * (b' + 1) - 1 = 3 * b' + 2 := by omega
    rw [h1, h2]; ring

/-- The upper staircase `{b, …, 2b-2}` partitions `b(3b-1)/2 - (2b-1)`. -/
lemma staircase_upper_sum (b : ℕ) (hb : b ≥ 1) :
    (staircase_upper b).sum id = b * (3 * b - 1) / 2 - (2 * b - 1) := by
  have hlow := staircase_lower_sum b
  have heq : (staircase_lower b).sum id = (staircase_upper b).sum id + (2 * b - 1) := by
    unfold staircase_lower staircase_upper
    have h2b : 2 * b = (2 * b - 1) + 1 := by omega
    rw [h2b, Finset.sum_Ico_succ_top (by omega : b ≤ 2 * b - 1)]
    rfl
  omega

/-! ## The non-fixed sets

These are the domain and codomain of the Franklin bijection.
-/

/-- Even partitions that are not pentagonal fixed points. -/
def even_nonfixed (n : ℕ) : Finset (Finset ℕ) :=
  even_distinct_partitions n \ pentagonal_fixed_points n

/-- Odd partitions that are not pentagonal fixed points. -/
def odd_nonfixed (n : ℕ) : Finset (Finset ℕ) :=
  odd_distinct_partitions n \ pentagonal_fixed_points n

/-- A non-fixed partition satisfies at least one of the two criteria. -/
lemma nonfixed_iff_crit (s : Finset ℕ) (n : ℕ)
    (hmem : s ∈ all_distinct_partitions n) (hne : s.Nonempty) :
    s ∉ pentagonal_fixed_points n ↔
      alpha_crit s hne = true ∨ beta_crit s hne = true := by
  have hkey : s ∈ pentagonal_fixed_points n ↔
      ¬ alpha_crit s hne = true ∧ ¬ beta_crit s hne = true := by
    rw [pentagonal_fixed_points, Finset.mem_filter, dif_pos hne]
    exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
  rw [hkey, not_and_or, not_not, not_not]

/-- `alpha_crit` and `beta_crit` are mutually exclusive. -/
lemma alpha_beta_crit_exclusive (s : Finset ℕ) (hne : s.Nonempty) :
    ¬ (alpha_crit s hne = true ∧ beta_crit s hne = true) := by
  rintro ⟨ha, hb⟩
  simp only [alpha_crit, beta_crit, base_and_slope, decide_eq_true_eq] at ha hb
  rcases ha with ⟨ha1, _⟩ | ha2 <;> rcases hb with ⟨hb1, _⟩ | hb2 <;> omega

/-! ## The forward map: even-nonfixed → odd-nonfixed

We package alpha and beta into a single `franklin_map` defined on
non-fixed partitions (regardless of parity). The proofs below assemble:

1. `franklin_map_card`: changes parity (drops or adds one part).
2. `franklin_map_sum`:  preserves the sum.
3. `franklin_map_pos`:  preserves positivity of parts.
4. `franklin_map_nonfixed`: lands again in the non-fixed set.
5. `franklin_map_involutive`: applying it twice gives the identity.
-/

/-- The Franklin map on a non-fixed partition. -/
noncomputable def franklin_map (s : Finset ℕ) (hne : s.Nonempty)
    (hcrit : alpha_crit s hne ∨ beta_crit s hne) : Finset ℕ :=
  if h : alpha_crit s hne then alpha_involution s hne h
  else beta_involution s hne (hcrit.resolve_left h)

/-- From `beta_crit`, the slope cardinality is strictly less than the base. -/
private lemma beta_crit_sigma_lt_b (s : Finset ℕ) (hne : s.Nonempty)
    (hcrit : beta_crit s hne = true) :
    let b := s.min' hne
    let m := s.max' hne
    let σ := s.filter (fun x => Finset.Icc x m ⊆ s)
    σ.card < b := by
  simp only [beta_crit, base_and_slope, decide_eq_true_eq] at hcrit
  rcases hcrit with ⟨h1, _⟩ | h2
  · exact h1
  · omega

/-- Beta preserves the sum.

Proof structure (substantial — deferred):
* sum decomposes as `(s \ σ).sum + σ.image(·-1).sum + σ.card`.
* `(s \ σ).sum = s.sum - σ.sum` via `Finset.sum_sdiff hσ_sub`.
* `σ.image(·-1).sum = σ.sum - σ.card` since each part `x ∈ σ` has `x ≥ 1`
  (so `(·-1)` is injective on σ and shifts each by -1).
* `{σ.card}.sum = σ.card`.
* Net change: `-σ.sum + (σ.sum - σ.card) + σ.card = 0`.

Disjointness obligations:
* `Disjoint (s \ σ) (σ.image (· - 1))` — uses maximality of `σ` (a `k-1 ∉ s`
  argument from `slope_is_interval`).
* `σ.card ∉ s` (so `σ.card ∉ s \ σ`) — from `σ.card < b ≤ all elements`.
* `σ.card ∉ σ.image(·-1)` — from `beta_crit` ruling out `σ.card + 1 = b ∈ σ`. -/
lemma beta_preserves_sum (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : beta_crit s hne = true) :
    (beta_involution s hne hcrit).sum id = s.sum id := by
  sorry

/-- Beta-applied to a nonempty positive partition gives a nonempty result.
    (Mirrors `alpha_involution_nonempty`.) -/
lemma beta_involution_nonempty (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : beta_crit s hne = true) :
    (beta_involution s hne hcrit).Nonempty := by
  apply Finset.nonempty_of_ne_empty
  intro hempty
  have hzero : (beta_involution s hne hcrit).sum id = 0 := by simp [hempty]
  have hpres := beta_preserves_sum s hne hpos hcrit
  have hpos' : 0 < s.sum id := Finset.sum_pos (fun x hx => hpos x hx) hne
  linarith

/-- The Franklin map preserves nonemptiness. -/
lemma franklin_map_nonempty (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne ∨ beta_crit s hne) :
    (franklin_map s hne hcrit).Nonempty := by
  unfold franklin_map
  split_ifs with h
  · exact alpha_involution_nonempty s hne hpos h
  · exact beta_involution_nonempty s hne hpos (hcrit.resolve_left h)

/-- Alpha drops one part. -/
lemma alpha_card (s : Finset ℕ) (hne : s.Nonempty)
    (hcrit : alpha_crit s hne = true) :
    (alpha_involution s hne hcrit).card + 1 = s.card := by
  let b := s.min' hne
  let m := s.max' hne
  let σ := s.filter (fun x => Finset.Icc x m ⊆ s)
  let T := σ.filter (fun x => x + b > m)
  change ((s \ T).erase b ∪ T.image (· + 1)).card + 1 = s.card
  have hT_sub : T ⊆ s := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hb_mem : b ∈ s := Finset.min'_mem s hne
  have hcard : T.card = b := top_b_slope_card s hne hcrit
  have hb_not_T : b ∉ T := by
    rw [Finset.mem_filter, not_and]
    intro hb_σ
    have hlt : b < σ.card := by
      have h := hcrit
      simp only [alpha_crit, base_and_slope, decide_eq_true_eq] at h
      exact h.elim (fun ⟨_, hns⟩ => absurd hb_σ hns) id
    have hσne : σ.Nonempty := ⟨b, hb_σ⟩
    have hk_in_s : σ.min' hσne ∈ s := Finset.filter_subset _ _ (Finset.min'_mem σ hσne)
    have hk_eq : σ.min' hσne = b :=
      le_antisymm (Finset.min'_le σ b hb_σ) (Finset.min'_le s _ hk_in_s)
    have hσ_eq : σ = Finset.Icc (σ.min' hσne) m := slope_is_interval s hne hσne
    have hσ_card : σ.card = m + 1 - b := by rw [hσ_eq, Nat.card_Icc, hk_eq]
    omega
  have hdj : Disjoint ((s \ T).erase b) (T.image (· + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx_im
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx_im
    have ht1_not_T : t + 1 ∉ T := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)).2
    have ht1_mem_s : t + 1 ∈ s := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)).1
    have ht_Icc : Finset.Icc t m ⊆ s := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
    have ht_top : t + b > m := (Finset.mem_filter.mp ht).2
    have htm : t + 1 ≤ m := Finset.le_max' s _ ht1_mem_s
    exact ht1_not_T (Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨ht1_mem_s, fun z hz =>
        ht_Icc (Finset.mem_Icc.mpr ⟨le_trans (by omega) (Finset.mem_Icc.mp hz).1,
                                      (Finset.mem_Icc.mp hz).2⟩)⟩,
      by omega⟩)
  rw [Finset.card_union_of_disjoint hdj]
  rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
  rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hb_mem, hb_not_T⟩)]
  have hpartition : (s \ T).card + T.card = s.card := by
    rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hT_sub]
  have hsdiff_pos : 1 ≤ (s \ T).card :=
    Finset.card_pos.mpr ⟨b, Finset.mem_sdiff.mpr ⟨hb_mem, hb_not_T⟩⟩
  omega

/-- Beta adds one part. -/
lemma beta_card (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : beta_crit s hne = true) :
    (beta_involution s hne hcrit).card = s.card + 1 := by
  let b := s.min' hne
  let m := s.max' hne
  let σ := s.filter (fun x => Finset.Icc x m ⊆ s)
  change ((s \ σ) ∪ σ.image (· - 1) ∪ {σ.card}).card = s.card + 1
  have hσ_sub : σ ⊆ s := Finset.filter_subset _ _
  have hm_σ : m ∈ σ := by
    rw [Finset.mem_filter]
    refine ⟨Finset.max'_mem s hne, fun z hz => ?_⟩
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hz
    rw [le_antisymm h2 h1]; exact Finset.max'_mem s hne
  have hσne : σ.Nonempty := ⟨m, hm_σ⟩
  have hσ_eq : σ = Finset.Icc (σ.min' hσne) m := slope_is_interval s hne hσne
  have hpos_σ : ∀ x ∈ σ, 1 ≤ x := fun x hx => hpos x (hσ_sub hx)
  have hσcard_lt_b : σ.card < b := beta_crit_sigma_lt_b s hne hcrit
  have hσcard_not_s : σ.card ∉ s := fun h => by
    have : b ≤ σ.card := Finset.min'_le s _ h; omega
  -- Disjoint (s \ σ) and σ.image (· - 1) — uses maximality of σ.
  have hdj1 : Disjoint (s \ σ) (σ.image (· - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hximg
    obtain ⟨t, htσ, rfl⟩ := Finset.mem_image.mp hximg
    have ht1_pos : 1 ≤ t := hpos_σ t htσ
    have hxs : t - 1 ∈ s := (Finset.mem_sdiff.mp hx).1
    have hxnσ : t - 1 ∉ σ := (Finset.mem_sdiff.mp hx).2
    have ht_in_Icc : t ∈ Finset.Icc (σ.min' hσne) m := hσ_eq ▸ htσ
    obtain ⟨hk_le_t, ht_le_m⟩ := Finset.mem_Icc.mp ht_in_Icc
    rcases eq_or_lt_of_le hk_le_t with heq | hlt
    · -- t = σ.min'. Then t - 1 = σ.min' - 1 ∈ s. By maximality of σ,
      -- σ.min' - 1 ∈ σ — contradicting σ.min' being the min of σ.
      exfalso
      have hsm : σ.min' hσne - 1 ∈ σ := by
        rw [Finset.mem_filter]
        refine ⟨heq ▸ hxs, ?_⟩
        intro z hz
        rw [Finset.mem_Icc] at hz
        obtain ⟨hz1, hz2⟩ := hz
        rcases eq_or_lt_of_le hz1 with heqz | hgtz
        · rw [← heqz]; exact heq ▸ hxs
        · have hz_in_σ : z ∈ σ := by
            rw [hσ_eq, Finset.mem_Icc]
            exact ⟨by omega, hz2⟩
          exact hσ_sub hz_in_σ
      have hmin_le : σ.min' hσne ≤ σ.min' hσne - 1 := Finset.min'_le σ _ hsm
      omega
    · -- t > σ.min', so t - 1 ≥ σ.min', so t - 1 ∈ σ.
      apply hxnσ
      rw [hσ_eq, Finset.mem_Icc]
      omega
  have hcrit' := hcrit
  simp only [beta_crit, base_and_slope, decide_eq_true_eq] at hcrit'
  -- σ.card not in σ.image (· - 1)
  have hσcard_not_image : σ.card ∉ σ.image (· - 1) := by
    intro h
    obtain ⟨t, htσ, ht_eq⟩ := Finset.mem_image.mp h
    have ht_pos : 1 ≤ t := hpos_σ t htσ
    have ht_eq' : t = σ.card + 1 := by omega
    have hb_le_t : b ≤ t := Finset.min'_le s t (hσ_sub htσ)
    set σunf := s.filter (fun x => Finset.Icc x (s.max' hne) ⊆ s)
    rcases hcrit' with ⟨_, hbnσ⟩ | h2
    · -- b ∉ σ. From σ.card < b ≤ t = σ.card + 1, we get t = b.
      have hsl : σunf.card < s.min' hne := hσcard_lt_b
      have hbt : s.min' hne ≤ t := hb_le_t
      have hte : t = σunf.card + 1 := ht_eq'
      have htb : t = s.min' hne := by omega
      apply hbnσ
      rw [← htb]; exact htσ
    · have hsl : σunf.card < s.min' hne := hσcard_lt_b
      have hbt : s.min' hne ≤ t := hb_le_t
      have hte : t = σunf.card + 1 := ht_eq'
      have h2' : σunf.card + 2 ≤ s.min' hne := h2
      omega
  -- Disjoint of singleton with the rest
  have hdj2 : Disjoint ((s \ σ) ∪ σ.image (· - 1)) {σ.card} := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [Finset.mem_union]
    rintro (hmem | hmem)
    · exact hσcard_not_s (Finset.mem_sdiff.mp hmem).1
    · exact hσcard_not_image hmem
  -- (·-1) is injective on σ
  have himg_inj : Set.InjOn (· - 1 : ℕ → ℕ) σ := by
    intro a ha c hc hac
    have hapos : 1 ≤ a := hpos_σ a ha
    have hcpos : 1 ≤ c := hpos_σ c hc
    simp only at hac; omega
  -- Card computations
  rw [Finset.card_union_of_disjoint hdj2, Finset.card_union_of_disjoint hdj1,
      Finset.card_singleton, Finset.card_image_of_injOn himg_inj]
  -- Goal: ((s \ σ).card + σ.card) + 1 = s.card + 1
  have hpartition : (s \ σ).card + σ.card = s.card := by
    rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hσ_sub]
  omega

/-- The Franklin map flips the parity of the number of parts. -/
lemma franklin_map_card (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne ∨ beta_crit s hne) :
    (franklin_map s hne hcrit).card % 2 ≠ s.card % 2 := by
  unfold franklin_map
  split_ifs with h
  · have := alpha_card s hne h
    omega
  · have := beta_card s hne hpos (hcrit.resolve_left h)
    omega

/-- The Franklin map preserves the partitioned sum. -/
lemma franklin_map_sum (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne ∨ beta_crit s hne) :
    (franklin_map s hne hcrit).sum id = s.sum id := by
  unfold franklin_map
  split_ifs with h
  · exact alpha_preserves_sum s hne h
  · exact beta_preserves_sum s hne hpos (hcrit.resolve_left h)

/-- Alpha preserves positivity of parts. -/
lemma alpha_pos (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne = true) :
    ∀ x ∈ alpha_involution s hne hcrit, 0 < x := by
  intro x hx
  unfold alpha_involution at hx
  rw [Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact hpos x (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)).1
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    omega

/-- Beta preserves positivity of parts. -/
lemma beta_pos (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : beta_crit s hne = true) :
    ∀ x ∈ beta_involution s hne hcrit, 0 < x := by
  set b := s.min' hne with hb_def
  set m := s.max' hne with hm_def
  set σ := s.filter (fun x => Finset.Icc x m ⊆ s) with hσ_def
  intro x hx
  unfold beta_involution at hx
  rw [Finset.mem_union, Finset.mem_union] at hx
  -- structure: (s \ σ) ∪ σ.image (· - 1) ∪ {σ.card}
  rcases hx with (hx | hx) | hx
  · exact hpos x (Finset.mem_sdiff.mp hx).1
  · obtain ⟨t, htσ, rfl⟩ := Finset.mem_image.mp hx
    have hts : t ∈ s := Finset.filter_subset _ _ htσ
    have htge : b ≤ t := Finset.min'_le s t hts
    have hbpos : 1 ≤ b := hpos b (Finset.min'_mem s hne)
    have hcrit' := hcrit
    simp only [beta_crit, base_and_slope, decide_eq_true_eq] at hcrit'
    rw [← hm_def, ← hb_def, ← hσ_def] at hcrit'
    rcases hcrit' with ⟨_, hbns⟩ | hbgs
    · have htgt : b < t := by
        rcases lt_or_eq_of_le htge with h | h
        · exact h
        · exfalso; apply hbns; rw [h]; exact htσ
      omega
    · omega
  · rw [Finset.mem_singleton] at hx
    have hm_σ : m ∈ σ := by
      rw [Finset.mem_filter]
      refine ⟨Finset.max'_mem s hne, fun z hz => ?_⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hz
      rw [le_antisymm h2 h1]
      exact Finset.max'_mem s hne
    rw [hx]
    exact Finset.card_pos.mpr ⟨m, hm_σ⟩

/-- The Franklin map preserves positivity of parts. -/
lemma franklin_map_pos (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne ∨ beta_crit s hne) :
    ∀ x ∈ franklin_map s hne hcrit, 0 < x := by
  unfold franklin_map
  split_ifs with h
  · exact alpha_pos s hne hpos h
  · exact beta_pos s hne hpos (hcrit.resolve_left h)

/-- The image of a non-fixed partition is again non-fixed: the new
    partition satisfies the *opposite* criterion. -/
lemma franklin_map_lands_nonfixed (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne ∨ beta_crit s hne) :
    ∃ hne' : (franklin_map s hne hcrit).Nonempty,
      alpha_crit (franklin_map s hne hcrit) hne' ∨
      beta_crit (franklin_map s hne hcrit) hne' := by
  sorry

/-- Applying the Franklin map twice gives the identity. -/
lemma franklin_map_involutive (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne ∨ beta_crit s hne) :
    let s' := franklin_map s hne hcrit
    let hne' := franklin_map_nonempty s hne hpos hcrit
    let hpos' : ∀ x ∈ s', 0 < x := franklin_map_pos s hne hpos hcrit
    let hcrit' := (franklin_map_lands_nonfixed s hne hpos hcrit).snd
    franklin_map s' hne' hcrit' = s := by
  sorry

/-! ## Packaging as `Equiv`

Now we assemble `franklin_map` into an `Equiv (even_nonfixed n) (odd_nonfixed n)`.
The forward map sends an even non-fixed partition to its image under
`franklin_map` (which has odd parity). The inverse is the same map
in the opposite direction.
-/

/-- A non-fixed partition is nonempty (the empty partition partitions 0
    and is its own fixed point trivially). -/
lemma nonfixed_nonempty {n : ℕ} {s : Finset ℕ}
    (hs : s ∉ pentagonal_fixed_points n) (hmem : s ∈ all_distinct_partitions n) :
    s.Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hs
  rw [pentagonal_fixed_points, Finset.mem_filter]
  refine ⟨hmem, ?_⟩
  subst hempty
  simp

lemma even_nonfixed_nonempty {n : ℕ} {s : Finset ℕ}
    (hs : s ∈ even_nonfixed n) : s.Nonempty := by
  rw [even_nonfixed, Finset.mem_sdiff] at hs
  obtain ⟨hmem, hnf⟩ := hs
  apply nonfixed_nonempty hnf
  rw [even_distinct_partitions, Finset.mem_filter] at hmem
  rw [all_distinct_partitions, Finset.mem_filter]
  exact ⟨hmem.1, hmem.2.1, hmem.2.2.1⟩

lemma odd_nonfixed_nonempty {n : ℕ} {s : Finset ℕ}
    (hs : s ∈ odd_nonfixed n) : s.Nonempty := by
  rw [odd_nonfixed, Finset.mem_sdiff] at hs
  obtain ⟨hmem, hnf⟩ := hs
  apply nonfixed_nonempty hnf
  rw [odd_distinct_partitions, Finset.mem_filter] at hmem
  rw [all_distinct_partitions, Finset.mem_filter]
  exact ⟨hmem.1, hmem.2.1, hmem.2.2.1⟩

lemma even_nonfixed_pos {n : ℕ} {s : Finset ℕ}
    (hs : s ∈ even_nonfixed n) : ∀ x ∈ s, 0 < x := by
  rw [even_nonfixed, Finset.mem_sdiff, even_distinct_partitions, Finset.mem_filter] at hs
  exact hs.1.2.2.1

lemma odd_nonfixed_pos {n : ℕ} {s : Finset ℕ}
    (hs : s ∈ odd_nonfixed n) : ∀ x ∈ s, 0 < x := by
  rw [odd_nonfixed, Finset.mem_sdiff, odd_distinct_partitions, Finset.mem_filter] at hs
  exact hs.1.2.2.1

lemma even_nonfixed_crit {n : ℕ} {s : Finset ℕ} (hs : s ∈ even_nonfixed n) :
    alpha_crit s (even_nonfixed_nonempty hs) = true ∨
    beta_crit s (even_nonfixed_nonempty hs) = true := by
  have hsdiff := hs
  rw [even_nonfixed, Finset.mem_sdiff] at hsdiff
  obtain ⟨hmem_even, hnotfix⟩ := hsdiff
  have hmem_all : s ∈ all_distinct_partitions n := by
    rw [even_distinct_partitions, Finset.mem_filter] at hmem_even
    rw [all_distinct_partitions, Finset.mem_filter]
    exact ⟨hmem_even.1, hmem_even.2.1, hmem_even.2.2.1⟩
  exact (nonfixed_iff_crit s n hmem_all (even_nonfixed_nonempty hs)).mp hnotfix

lemma odd_nonfixed_crit {n : ℕ} {s : Finset ℕ} (hs : s ∈ odd_nonfixed n) :
    alpha_crit s (odd_nonfixed_nonempty hs) = true ∨
    beta_crit s (odd_nonfixed_nonempty hs) = true := by
  have hsdiff := hs
  rw [odd_nonfixed, Finset.mem_sdiff] at hsdiff
  obtain ⟨hmem_odd, hnotfix⟩ := hsdiff
  have hmem_all : s ∈ all_distinct_partitions n := by
    rw [odd_distinct_partitions, Finset.mem_filter] at hmem_odd
    rw [all_distinct_partitions, Finset.mem_filter]
    exact ⟨hmem_odd.1, hmem_odd.2.1, hmem_odd.2.2.1⟩
  exact (nonfixed_iff_crit s n hmem_all (odd_nonfixed_nonempty hs)).mp hnotfix

/-- A non-fixed even partition is sent to a non-fixed odd partition. -/
lemma franklin_map_lands_odd {n : ℕ} {s : Finset ℕ} (hs : s ∈ even_nonfixed n) :
    franklin_map s (even_nonfixed_nonempty hs) (even_nonfixed_crit hs) ∈ odd_nonfixed n := by
  set hne := even_nonfixed_nonempty hs
  set hcrit := even_nonfixed_crit hs
  have hpos : ∀ x ∈ s, 0 < x := even_nonfixed_pos hs
  have hsdiff := hs
  rw [even_nonfixed, Finset.mem_sdiff] at hsdiff
  obtain ⟨hmem_even, hnotfix⟩ := hsdiff
  rw [even_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem_even
  obtain ⟨hs_sub, hs_sum, _, hs_card⟩ := hmem_even
  -- properties of the image under franklin_map
  have him_sum : (franklin_map s hne hcrit).sum id = n := by
    rw [franklin_map_sum s hne hpos hcrit]; exact hs_sum
  have him_pos : ∀ x ∈ franklin_map s hne hcrit, 0 < x := franklin_map_pos s hne hpos hcrit
  have him_card_ne : (franklin_map s hne hcrit).card % 2 ≠ s.card % 2 :=
    franklin_map_card s hne hpos hcrit
  have him_card_odd : (franklin_map s hne hcrit).card % 2 = 1 := by omega
  -- image ⊆ range(n+1)
  have him_sub : (franklin_map s hne hcrit) ⊆ Finset.range (n + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hxle : x ≤ (franklin_map s hne hcrit).sum id :=
      Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx
    rw [him_sum] at hxle
    omega
  -- image is in all_distinct_partitions n
  have hmem_all : franklin_map s hne hcrit ∈ all_distinct_partitions n := by
    rw [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨him_sub, him_sum, him_pos⟩
  rw [odd_nonfixed, Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [odd_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨him_sub, him_sum, him_pos, him_card_odd⟩
  · obtain ⟨hne', hcrit'⟩ := franklin_map_lands_nonfixed s hne hpos hcrit
    exact (nonfixed_iff_crit _ n hmem_all hne').mpr hcrit'

/-- A non-fixed odd partition is sent to a non-fixed even partition. -/
lemma franklin_map_lands_even {n : ℕ} {s : Finset ℕ} (hs : s ∈ odd_nonfixed n) :
    franklin_map s (odd_nonfixed_nonempty hs) (odd_nonfixed_crit hs) ∈ even_nonfixed n := by
  set hne := odd_nonfixed_nonempty hs
  set hcrit := odd_nonfixed_crit hs
  have hpos : ∀ x ∈ s, 0 < x := odd_nonfixed_pos hs
  have hsdiff := hs
  rw [odd_nonfixed, Finset.mem_sdiff] at hsdiff
  obtain ⟨hmem_odd, hnotfix⟩ := hsdiff
  rw [odd_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem_odd
  obtain ⟨hs_sub, hs_sum, _, hs_card⟩ := hmem_odd
  have him_sum : (franklin_map s hne hcrit).sum id = n := by
    rw [franklin_map_sum s hne hpos hcrit]; exact hs_sum
  have him_pos : ∀ x ∈ franklin_map s hne hcrit, 0 < x := franklin_map_pos s hne hpos hcrit
  have him_card_ne : (franklin_map s hne hcrit).card % 2 ≠ s.card % 2 :=
    franklin_map_card s hne hpos hcrit
  have him_card_even : (franklin_map s hne hcrit).card % 2 = 0 := by omega
  have him_sub : (franklin_map s hne hcrit) ⊆ Finset.range (n + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hxle : x ≤ (franklin_map s hne hcrit).sum id :=
      Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx
    rw [him_sum] at hxle
    omega
  have hmem_all : franklin_map s hne hcrit ∈ all_distinct_partitions n := by
    rw [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨him_sub, him_sum, him_pos⟩
  rw [even_nonfixed, Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [even_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨him_sub, him_sum, him_pos, him_card_even⟩
  · obtain ⟨hne', hcrit'⟩ := franklin_map_lands_nonfixed s hne hpos hcrit
    exact (nonfixed_iff_crit _ n hmem_all hne').mpr hcrit'

/-- The Franklin bijection between non-fixed even and non-fixed odd
    partitions. -/
noncomputable def franklin_equiv (n : ℕ) :
    {s // s ∈ even_nonfixed n} ≃ {s // s ∈ odd_nonfixed n} where
  toFun s :=
    ⟨franklin_map s.1 (even_nonfixed_nonempty s.2) (even_nonfixed_crit s.2),
     franklin_map_lands_odd s.2⟩
  invFun s :=
    ⟨franklin_map s.1 (odd_nonfixed_nonempty s.2) (odd_nonfixed_crit s.2),
     franklin_map_lands_even s.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    dsimp only
    exact franklin_map_involutive s.1 (even_nonfixed_nonempty s.2)
      (even_nonfixed_pos s.2) (even_nonfixed_crit s.2)
  right_inv := by
    intro s
    apply Subtype.ext
    dsimp only
    exact franklin_map_involutive s.1 (odd_nonfixed_nonempty s.2)
      (odd_nonfixed_pos s.2) (odd_nonfixed_crit s.2)

/-! ## Cardinality consequences -/

/-- The two non-fixed sets have the same cardinality. -/
theorem even_nonfixed_card_eq_odd_nonfixed_card (n : ℕ) :
    (even_nonfixed n).card = (odd_nonfixed n).card := by
  rw [← Fintype.card_coe (even_nonfixed n), ← Fintype.card_coe (odd_nonfixed n)]
  exact Fintype.card_congr (franklin_equiv n)

/-- `fixed_even n` is contained in `even_distinct_partitions n`. -/
lemma fixed_even_subset (n : ℕ) :
    fixed_even n ⊆ even_distinct_partitions n := by
  intro s hs
  rw [fixed_even, Finset.mem_filter, pentagonal_fixed_points, Finset.mem_filter,
      all_distinct_partitions, Finset.mem_filter] at hs
  rw [even_distinct_partitions, Finset.mem_filter]
  exact ⟨hs.1.1.1, hs.1.1.2.1, hs.1.1.2.2, hs.2⟩

/-- `fixed_odd n` is contained in `odd_distinct_partitions n`. -/
lemma fixed_odd_subset (n : ℕ) :
    fixed_odd n ⊆ odd_distinct_partitions n := by
  intro s hs
  rw [fixed_odd, Finset.mem_filter, pentagonal_fixed_points, Finset.mem_filter,
      all_distinct_partitions, Finset.mem_filter] at hs
  rw [odd_distinct_partitions, Finset.mem_filter]
  exact ⟨hs.1.1.1, hs.1.1.2.1, hs.1.1.2.2, hs.2⟩

/-- The non-fixed even set equals `even_distinct_partitions \ fixed_even`. -/
lemma even_nonfixed_eq_sdiff (n : ℕ) :
    even_nonfixed n = even_distinct_partitions n \ fixed_even n := by
  ext s
  rw [even_nonfixed, Finset.mem_sdiff, Finset.mem_sdiff, fixed_even, Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hnotfix⟩
    exact ⟨hmem, fun ⟨hfix, _⟩ => hnotfix hfix⟩
  · rintro ⟨hmem, hnot⟩
    refine ⟨hmem, fun hfix => hnot ⟨hfix, ?_⟩⟩
    rw [even_distinct_partitions, Finset.mem_filter] at hmem
    exact hmem.2.2.2

/-- The non-fixed odd set equals `odd_distinct_partitions \ fixed_odd`. -/
lemma odd_nonfixed_eq_sdiff (n : ℕ) :
    odd_nonfixed n = odd_distinct_partitions n \ fixed_odd n := by
  ext s
  rw [odd_nonfixed, Finset.mem_sdiff, Finset.mem_sdiff, fixed_odd, Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hnotfix⟩
    exact ⟨hmem, fun ⟨hfix, _⟩ => hnotfix hfix⟩
  · rintro ⟨hmem, hnot⟩
    refine ⟨hmem, fun hfix => hnot ⟨hfix, ?_⟩⟩
    rw [odd_distinct_partitions, Finset.mem_filter] at hmem
    exact hmem.2.2.2

/-- `p_e n - p_o n` collapses to the signed count of fixed points. -/
theorem p_e_sub_p_o_eq_fixed_diff (n : ℕ) :
    (p_e n : ℤ) - (p_o n : ℤ) =
      (fixed_even n).card - (fixed_odd n).card := by
  have hcard_eq := even_nonfixed_card_eq_odd_nonfixed_card n
  have hdecomp_even :
      (even_distinct_partitions n).card = (even_nonfixed n).card + (fixed_even n).card := by
    have hsub := fixed_even_subset n
    have hunion : even_nonfixed n ∪ fixed_even n = even_distinct_partitions n := by
      rw [even_nonfixed_eq_sdiff]; exact Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint (even_nonfixed n) (fixed_even n) := by
      rw [even_nonfixed_eq_sdiff]; exact Finset.sdiff_disjoint
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hdecomp_odd :
      (odd_distinct_partitions n).card = (odd_nonfixed n).card + (fixed_odd n).card := by
    have hsub := fixed_odd_subset n
    have hunion : odd_nonfixed n ∪ fixed_odd n = odd_distinct_partitions n := by
      rw [odd_nonfixed_eq_sdiff]; exact Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint (odd_nonfixed n) (fixed_odd n) := by
      rw [odd_nonfixed_eq_sdiff]; exact Finset.sdiff_disjoint
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  unfold p_e p_o
  rw [hdecomp_even, hdecomp_odd]
  have hcast : (↑(even_nonfixed n).card : ℤ) = ↑(odd_nonfixed n).card := by exact_mod_cast hcard_eq
  push_cast
  linarith

/-! ## Pentagonal closed form

With the Franklin bijection out of the way, the remaining content is
purely arithmetic: count the staircase fixed points at each `n` and
match them against the pentagonal numbers `k(3k−1)/2`.
-/

/-- The fixed-point difference at a pentagonal index. -/
theorem fixed_diff_at_pentagonal (k : ℤ) (n : ℕ) (hn : (n : ℤ) = k * (3 * k - 1) / 2) :
    ((fixed_even n).card : ℤ) - ((fixed_odd n).card : ℤ) =
      (-1 : ℤ) ^ (Int.natAbs k) := by
  sorry

/-- Off the pentagonal sequence, the fixed-point sets are equinumerous
    (in fact both empty). -/
theorem fixed_diff_off_pentagonal (n : ℕ)
    (hn : ¬ ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2) :
    ((fixed_even n).card : ℤ) - ((fixed_odd n).card : ℤ) = 0 := by
  sorry

/-! ## Euler's pentagonal number theorem -/

theorem euler_pentagonal_number_theorem' (n : ℕ) :
    (∃ k : ℤ, ((n : ℤ) = k * (3 * k - 1) / 2) ∧
      ((p_e n : ℤ) - (p_o n : ℤ) = (-1 : ℤ) ^ Int.natAbs k)) ∨
    ((¬ ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2) ∧
      ((p_e n : ℤ) - (p_o n : ℤ) = 0)) := by
  by_cases hk : ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2
  · left
    obtain ⟨k, hkn⟩ := hk
    refine ⟨k, hkn, ?_⟩
    rw [p_e_sub_p_o_eq_fixed_diff]
    exact_mod_cast fixed_diff_at_pentagonal k n hkn
  · right
    refine ⟨hk, ?_⟩
    rw [p_e_sub_p_o_eq_fixed_diff]
    exact_mod_cast fixed_diff_off_pentagonal n hk
