import Mathlib

/- Define the set of partitions of n to distinct parts -/
def all_distinct_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun s => Finset.sum s id = n ∧ ∀ x ∈ s, x > 0)
   (Finset.powerset (Finset.range (n + 1)))

/- Test 1
def c1 : Finset (Finset ℕ) := all_distinct_partitions 3
#eval c1.card

Define the set of partitions of n to even number of distinct parts -/
def even_distinct_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun s => ( Finset.sum s id = n ) ∧ (∀ x ∈ s, x > 0 ) ∧ ( s.card % 2 = 0) )
   (Finset.powerset (Finset.range (n + 1)))

/-- Test 2
def c2 : Finset (Finset ℕ) := even_distinct_partitions 6
#eval c2.card

Define the set of partitions of n to odd number of distinct parts -/
def odd_distinct_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun s => ( Finset.sum s id = n ) ∧ ( ∀ x ∈ s, x > 0 ) ∧ ( s.card % 2 = 1 ))
  (Finset.powerset (Finset.range (n + 1)))


/- Test 3
def c3 : Finset (Finset ℕ) := odd_distinct_partitions 6
#eval c3.card -/
def p_e (n : ℕ) : ℕ := (even_distinct_partitions n).card

def p_o (n : ℕ) : ℕ := (odd_distinct_partitions n).card

/- Test 4
#eval p_e 5

#eval p_e 2
#eval p_o 2
 -/

/- \begin{theorem}Let $n$ be a natural number.
If there exists $k\in\mathbb{Z}$ such that $n=(3k^2-k)/2$ then
$p_e(n)-p_0(n)=(-1)^k$,
otherwise $p_e(n)-p_0(n)=0$\end{theorem} -/

/-- Given a nonempty partition into distinct parts, returns `(base, slope)` where:
    - `base` is the smallest part (the minimum element)
    - `slope` is the maximal consecutive sequence of integers ending at the largest part.
    A part `x` is in the slope iff the entire interval `[x, max]` lies within `s`. -/
def base_and_slope (s : Finset ℕ) (h : s.Nonempty) : ℕ × Finset ℕ :=
  let m := s.max' h
  let base := s.min' h
  let slope_set := s.filter (fun x => Finset.Icc x m ⊆ s)

  (base, slope_set)


/-- Alpha applies when base < |slope|, OR base = |slope| and base is not in the slope.
    The excluded case (base = |slope| and base ∈ slope) is the fixed point {b,...,2b-1}. -/
def alpha_crit (s : Finset ℕ) (h : s.Nonempty) : Bool :=
  let (base, slope) := base_and_slope s h
  (base ≤ slope.card ∧ base ∉ slope) ∨ (base < slope.card)


/-- Move base to slope: remove base, shift only the top `base` slope elements up by 1. -/
def alpha_involution (s : Finset ℕ) (hne : s.Nonempty) (hcrit : alpha_crit s hne = true) : Finset ℕ :=
  let (base, slope) := base_and_slope s hne
  let m := s.max' hne
  let top_b_slope := slope.filter (fun x => x + base > m)
  (s \ top_b_slope).erase base ∪ top_b_slope.image (· + 1)

/-- Beta applies when base > |slope|, unless applying it would create a duplicate part.
    Duplicates arise exactly when base ∈ slope (fixed point {b,...,2b-2}) unless base ≥ |slope|+2. -/
def beta_crit (s : Finset ℕ) (h : s.Nonempty) : Bool :=
  let (base, slope) := base_and_slope s h
  (base > slope.card ∧ base ∉ slope) ∨ (slope.card + 2 ≤ base)

/-- Move slope to base: shift all slope elements down by 1, add new bottom row of size |slope|. -/
def beta_involution (s : Finset ℕ) (hne : s.Nonempty) (hcrit : beta_crit s hne = true) : Finset ℕ :=
  let (base, slope) := base_and_slope s hne
  (s \ slope) ∪ slope.image (· - 1) ∪ {slope.card}


/-- The top-b slice of the slope has exactly b elements. -/
lemma top_b_slope_card (s : Finset ℕ) (hne : s.Nonempty)
    (hcrit : alpha_crit s hne = true) :
    ((s.filter (fun x => Finset.Icc x (s.max' hne) ⊆ s)).filter
      (fun x => x + s.min' hne > s.max' hne)).card = s.min' hne := by
  sorry

/-- Alpha preserves the sum of parts. -/
lemma alpha_preserves_sum (s : Finset ℕ) (hne : s.Nonempty)
    (hcrit : alpha_crit s hne = true) :
    (alpha_involution s hne hcrit).sum id = s.sum id := by
  let b := s.min' hne
  let m := s.max' hne
  let σ := s.filter (fun x => Finset.Icc x m ⊆ s)
  let T := σ.filter (fun x => x + b > m)
  change ((s \ T).erase b ∪ T.image (· + 1)).sum id = s.sum id
  have hT_sub   : T ⊆ s      := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hb_mem   : b ∈ s      := Finset.min'_mem s hne
  have hcard    : T.card = b := top_b_slope_card s hne hcrit
  have hb_not_T : b ∉ T     := sorry
  have hdj : Disjoint ((s \ T).erase b) (T.image (· + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx_im
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx_im
    have ht1_not_T : t + 1 ∉ T         := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)).2
    have ht1_mem_s : t + 1 ∈ s         := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)).1
    have ht_Icc    : Finset.Icc t m ⊆ s := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
    have ht_top    : t + b > m         := (Finset.mem_filter.mp ht).2
    have htm       : t + 1 ≤ m         := Finset.le_max' s _ ht1_mem_s
    exact ht1_not_T (Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨ht1_mem_s, fun z hz =>
        ht_Icc (Finset.mem_Icc.mpr ⟨le_trans (by omega) (Finset.mem_Icc.mp hz).1,
                                      (Finset.mem_Icc.mp hz).2⟩)⟩,
      by omega⟩)
  have h1 : (s \ T).sum (id : ℕ → ℕ) + T.sum (id : ℕ → ℕ) = s.sum (id : ℕ → ℕ) :=
    Finset.sum_sdiff hT_sub
  have h2 : ((s \ T).erase b).sum (id : ℕ → ℕ) + b = (s \ T).sum (id : ℕ → ℕ) := by
    have h := Finset.sum_sdiff (f := (id : ℕ → ℕ))
      (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨hb_mem, hb_not_T⟩))
    rw [← Finset.erase_eq, Finset.sum_singleton] at h
    linarith [show id b = b from rfl]
  have h3 : (T.image (· + 1)).sum (id : ℕ → ℕ) = T.sum (id : ℕ → ℕ) + T.card := by
    rw [Finset.sum_image (fun a _ c _ h => by omega)]
    simp [Finset.sum_add_distrib, Finset.sum_const, mul_comm]
  rw [Finset.sum_union hdj, h3]
  linarith

/-- After alpha, the result is nonempty. -/
lemma alpha_involution_nonempty (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne = true) :
    (alpha_involution s hne hcrit).Nonempty := by
  apply Finset.nonempty_of_ne_empty
  intro hempty
  have hzero : (alpha_involution s hne hcrit).sum id = 0 := by simp [hempty]
  have hpres := alpha_preserves_sum s hne hcrit
  have hpos' : 0 < s.sum id := Finset.sum_pos (fun x hx => hpos x hx) hne
  linarith

/-- After alpha, the result satisfies beta_crit. -/
lemma alpha_gives_beta_crit (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne = true) :
    beta_crit (alpha_involution s hne hcrit)
              (alpha_involution_nonempty s hne hpos hcrit) = true := by
  sorry

/-- Applying alpha_involution to a partition satisfying alpha_crit yields a partition
    satisfying beta_crit. -/
theorem beta_crit_after_alpha (s : Finset ℕ) (hne : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 < x)
    (hcrit : alpha_crit s hne = true) :
    let s' := alpha_involution s hne hcrit
    ∃ hne' : s'.Nonempty, beta_crit s' hne' = true :=
  ⟨alpha_involution_nonempty s hne hpos hcrit, alpha_gives_beta_crit s hne hpos hcrit⟩

/-- Franklin's map: apply alpha if alpha_crit holds, beta if beta_crit holds, identity otherwise. -/
def franklin (s : Finset ℕ) (hne : s.Nonempty) : Finset ℕ :=
  if h : alpha_crit s hne = true then alpha_involution s hne h
  else if h : beta_crit s hne = true then beta_involution s hne h
  else s

/-- Franklin's map is an involution on non-fixed-point partitions. -/
theorem Franklin_is_involution (s : Finset ℕ) (hne : s.Nonempty)
    (hcrit : (alpha_crit s hne = true) ∨ (beta_crit s hne = true)) :
    ∃ hne' : (franklin s hne).Nonempty, franklin (franklin s hne) hne' = s := by
  sorry

/-- Franklin's map changes the parity of the number of parts. -/
theorem Franklin_changes_parity (s : Finset ℕ) (hne : s.Nonempty)
    (hcrit : (alpha_crit s hne = true) ∨ (beta_crit s hne = true)) :
    ∃ hne' : (franklin s hne).Nonempty,
      (franklin s hne).card % 2 ≠ s.card % 2 := by
  sorry


/-- Euler’s pentagonal number theorem. -/
theorem euler_pentagonal_number_theorem (n : ℕ) :
  (∃ k : ℤ, (n = (k * (3 * k - 1)) / 2) ∧
  ((p_e n : ℤ) - (p_o n : ℤ) = (-1 : ℤ) ^ (Int.natAbs k) )) ∨
  ((¬ ∃ k : ℤ, n = (k * (3 * k - 1)) / 2 ) ∧
    ((p_e n : ℤ) - (p_o n : ℤ) = 0 )) :=
sorry
