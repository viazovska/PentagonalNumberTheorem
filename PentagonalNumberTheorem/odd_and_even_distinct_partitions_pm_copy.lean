import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat


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

/-- The base of a partition: its smallest element -/
def base (S : Finset ℕ) (hS : S.Nonempty) : ℕ := S.min' hS

/-- Length of the maximal consecutive run descending from max(S) -/
def consecutiveRunDown (S : Finset ℕ) : ℕ → ℕ
  | 0     => if 0 ∈ S then 1 else 0
  | n + 1 => if (n + 1) ∈ S then consecutiveRunDown S n + 1 else 0

/-- The slope of a partition -/
def slope (S : Finset ℕ) (hS : S.Nonempty) : ℕ :=
  consecutiveRunDown S (S.max' hS)

/-- The slope set: the top s consecutive elements of S -/
def slopeSet (S : Finset ℕ) (hS : S.Nonempty) : Finset ℕ :=
  let m := S.max' hS
  let s := slope S hS
  S.filter (fun x => m + 1 - s ≤ x)

lemma slope_pos_nonempty (S : Finset ℕ) (hS : S.Nonempty) : 0 < slope S hS := by
  rcases hm : S.max' hS with _ | m
  · have h0 : 0 ∈ S := by simpa [hm] using Finset.max'_mem S hS
    rw [slope, hm]
    simp [consecutiveRunDown, h0]
  · have hmem : m + 1 ∈ S := by simpa [hm] using Finset.max'_mem S hS
    rw [slope, hm]
    simp [consecutiveRunDown, hmem]

lemma sum_range_id_mul_two' (n : ℕ) : (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (∑ i ∈ Finset.range (n + 1), i) * 2 = ((∑ i ∈ Finset.range n, i) + n) * 2 := by
          rw [Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range n, i) * 2 + n * 2 := by omega
        _ = n * (n - 1) + n * 2 := by rw [ih]
        _ = n * ((n - 1) + 2) := by rw [← Nat.mul_add]
        _ = n * (n + 1) := by
          by_cases hn : n = 0
          · subst n
            simp
          · have htmp : (n - 1) + 2 = n + 1 := by omega
            rw [htmp]
        _ = (n + 1) * ((n + 1) - 1) := by simp [Nat.mul_comm]

lemma sum_range_id' (n : ℕ) : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two' n, Nat.mul_div_cancel _ Nat.zero_lt_two]

/-- Condition for α to be applicable -/
def alpha_applicable (S : Finset ℕ) (hS : S.Nonempty) : Prop :=
  let b := base S hS
  let s := slope S hS
  let D := slopeSet S hS
  (b ≤ s ∧ b ∉ D) ∨ (b ≤ s - 1)

/-- Operation α: remove b and max(S)-b+1, add max(S)+1 -/
def alpha (S : Finset ℕ) (hS : S.Nonempty) : Finset ℕ :=
  let b := base S hS
  let m := S.max' hS
  (S \ {b, m - b + 1}) ∪ {m + 1}

/-- Condition for β to be applicable -/
def beta_applicable (S : Finset ℕ) (hS : S.Nonempty) : Prop :=
  let b := base S hS
  let s := slope S hS
  let D := slopeSet S hS
  (b > s ∧ b ∉ D) ∨ (b ≥ s + 2)

/-- Operation β: add s and max(S)-s, remove max(S) -/
def beta (S : Finset ℕ) (hS : S.Nonempty) : Finset ℕ :=
  let s := slope S hS
  let m := S.max' hS
  (S ∪ {s, m - s}) \ {m}

/-- Partitions of n to which α is applicable -/
noncomputable def alpha_partitions (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact Finset.filter
    (fun S => if h : S.Nonempty then alpha_applicable S h else False)
    (all_distinct_partitions n)

/-- Partitions of n to which β is applicable -/
noncomputable def beta_partitions (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact Finset.filter
    (fun S => if h : S.Nonempty then beta_applicable S h else False)
    (all_distinct_partitions n)

theorem alpha_beta_disjoint (n : ℕ) :
    Disjoint (alpha_partitions n) (beta_partitions n) := by
  rw [Finset.disjoint_left]
  intro S hα hβ
  simp only [alpha_partitions, beta_partitions, Finset.mem_filter] at hα hβ
  obtain ⟨_, hα_cond⟩ := hα
  obtain ⟨_, hβ_cond⟩ := hβ
  by_cases h : S.Nonempty
  · simp only [dif_pos h] at hα_cond hβ_cond
    simp only [alpha_applicable, beta_applicable] at hα_cond hβ_cond
    rcases hα_cond with (⟨hbs, _⟩ | hbs) <;>
    rcases hβ_cond with (⟨hsb, _⟩ | hsb) <;>
    omega
  · simp only [dif_neg h] at hα_cond

lemma neither_alpha_nor_beta_applicable_iff
    (S : Finset ℕ) (hS : S.Nonempty) :
    (¬ alpha_applicable S hS ∧ ¬ beta_applicable S hS) ↔
      base S hS ∈ slopeSet S hS ∧
        (base S hS = slope S hS ∨ base S hS = slope S hS + 1) := by
  classical
  let b := base S hS
  let s := slope S hS
  let D := slopeSet S hS
  by_cases hD : b ∈ D
  · have hαiff : alpha_applicable S hS ↔ b ≤ s - 1 := by
      simp [alpha_applicable, b, s, D, hD]
    have hβiff : beta_applicable S hS ↔ b ≥ s + 2 := by
      simp [beta_applicable, b, s, D, hD]
    constructor
    · intro h
      have h1 : ¬ b ≤ s - 1 := by
        intro hb
        exact h.1 (hαiff.mpr hb)
      have h2 : ¬ b ≥ s + 2 := by
        intro hb
        exact h.2 (hβiff.mpr hb)
      have hs_le_b : s ≤ b := by
        by_contra hs
        exact h1 (by omega)
      have hb_le_succ : b ≤ s + 1 := by
        by_contra hb
        exact h2 (by omega)
      have hs_pos : 0 < s := by
        simpa [s] using slope_pos_nonempty S hS
      have hs : b = s ∨ b = s + 1 := by omega
      refine ⟨by simpa [b, D] using hD, ?_⟩
      simpa [b, s] using hs
    · intro h
      have hs_pos : 0 < s := by
        simpa [s] using slope_pos_nonempty S hS
      have hs : b = s ∨ b = s + 1 := by
        simpa [b, s, D] using h.2
      constructor
      · intro hα
        have hb : b ≤ s - 1 := hαiff.mp hα
        rcases hs with hs | hs
        · have : s ≤ s - 1 := by simpa [hs] using hb
          omega
        · have : s + 1 ≤ s - 1 := by simpa [hs] using hb
          omega
      · intro hβ
        have hb : b ≥ s + 2 := hβiff.mp hβ
        rcases hs with hs | hs
        · have : s ≥ s + 2 := by simpa [hs] using hb
          omega
        · have : s + 1 ≥ s + 2 := by simpa [hs] using hb
          omega
  · constructor
    · intro h
      rcases le_or_gt b s with hle | hgt
      · have hα : alpha_applicable S hS := by
          left
          exact ⟨by simpa [b, s] using hle, by simpa [b, D] using hD⟩
        exact (h.1 hα).elim
      · have hβ : beta_applicable S hS := by
          left
          exact ⟨by simpa [b, s] using hgt, by simpa [b, D] using hD⟩
        exact (h.2 hβ).elim
    · intro h
      exact (hD (by simpa [b, D] using h.1)).elim

lemma neither_alpha_nor_beta_applicable_imp_s_eq_b_or_b_sub_one
    (S : Finset ℕ) (hS : S.Nonempty)
    (h : ¬ alpha_applicable S hS ∧ ¬ beta_applicable S hS) :
    slope S hS = base S hS ∨ slope S hS = base S hS - 1 := by
  rcases (neither_alpha_nor_beta_applicable_iff S hS).mp h with ⟨_, hs⟩
  omega

lemma nonempty_of_alpha_mem (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ alpha_partitions n) : S.Nonempty := by
  simp only [alpha_partitions, Finset.mem_filter] at hS
  obtain ⟨_, hcond⟩ := hS
  by_contra h
  simp only [dif_neg h] at hcond

lemma nonempty_of_beta_mem (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ beta_partitions n) : S.Nonempty := by
  simp only [beta_partitions, Finset.mem_filter] at hS
  obtain ⟨_, hcond⟩ := hS
  by_contra h
  simp only [dif_neg h] at hcond

lemma alpha_applicable_of_mem (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ alpha_partitions n) :
    alpha_applicable S (nonempty_of_alpha_mem n S hS) := by
  simp only [alpha_partitions, Finset.mem_filter] at hS
  obtain ⟨_, hcond⟩ := hS
  simp only [dif_pos (nonempty_of_alpha_mem n S hS)] at hcond
  exact hcond

lemma mem_alpha_partitions_of_mem_all_distinct_of_applicable
    (n : ℕ) (S : Finset ℕ) (hne : S.Nonempty)
    (hmem : S ∈ all_distinct_partitions n)
    (hα : alpha_applicable S hne) :
    S ∈ alpha_partitions n := by
  simp only [alpha_partitions, Finset.mem_filter]
  refine ⟨hmem, ?_⟩
  simp [hne, hα]

lemma beta_applicable_of_mem (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ beta_partitions n) :
    beta_applicable S (nonempty_of_beta_mem n S hS) := by
  simp only [beta_partitions, Finset.mem_filter] at hS
  obtain ⟨_, hcond⟩ := hS
  simp only [dif_pos (nonempty_of_beta_mem n S hS)] at hcond
  exact hcond

lemma mem_beta_partitions_of_mem_all_distinct_of_applicable
    (n : ℕ) (S : Finset ℕ) (hne : S.Nonempty)
    (hmem : S ∈ all_distinct_partitions n)
    (hβ : beta_applicable S hne) :
    S ∈ beta_partitions n := by
  simp only [beta_partitions, Finset.mem_filter]
  refine ⟨hmem, ?_⟩
  simp [hne, hβ]

lemma mem_of_le_consecutiveRunDown (S : Finset ℕ) :
    ∀ {n k : ℕ}, 0 < k → k ≤ consecutiveRunDown S n → n + 1 - k ∈ S := by
  intro n
  induction n with
  | zero =>
      intro k hkpos hk
      by_cases h0 : 0 ∈ S
      · simp [consecutiveRunDown, h0] at hk
        have hk1 : k = 1 := by omega
        subst k
        simpa using h0
      · simp [consecutiveRunDown, h0] at hk
        omega
  | succ n ih =>
      intro k hkpos hk
      by_cases hmem : n + 1 ∈ S
      · simp [consecutiveRunDown, hmem] at hk
        by_cases hk1 : k = 1
        · subst k
          simpa using hmem
        · have hkpred_pos : 0 < k - 1 := by omega
          have hkpred_le : k - 1 ≤ consecutiveRunDown S n := by omega
          have hrec : n + 1 - (k - 1) ∈ S := ih hkpred_pos hkpred_le
          have hk_eq : n + 2 - k = n + 1 - (k - 1) := by omega
          simpa [hk_eq] using hrec
      · simp [consecutiveRunDown, hmem] at hk
        omega

lemma alpha_nonempty (S : Finset ℕ) (hne : S.Nonempty) : (alpha S hne).Nonempty := by
  refine ⟨S.max' hne + 1, ?_⟩
  simp [alpha]
lemma alpha_mem_all_distinct (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ alpha_partitions n) :
    alpha S (nonempty_of_alpha_mem n S hS) ∈ all_distinct_partitions n := by
  set hne := nonempty_of_alpha_mem n S hS
  set b := base S hne
  set m := S.max' hne
  -- Extract S's partition properties and the α condition
  simp only [alpha_partitions, Finset.mem_filter, dif_pos hne] at hS
  obtain ⟨hmem, hα⟩ := hS
  simp only [all_distinct_partitions, Finset.mem_filter,
             Finset.mem_powerset] at hmem
  obtain ⟨hrange, hsum, hpos⟩ := hmem
  -- Basic facts about b and m
  have hb_mem  : b ∈ S := Finset.min'_mem S hne
  have hb_pos  : 0 < b := hpos b hb_mem
  have hb_le_m : b ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
  have hb_le_s : b ≤ slope S hne := by
    rcases hα with hα | hα
    · simpa [b] using hα.1
    · have hsminus : b ≤ slope S hne - 1 := by simpa [b] using hα
      omega
  -- m-b+1 ∈ S because slope ≥ b in both cases of the α condition
  have hmb_mem : m - b + 1 ∈ S := by
    have hrun : m + 1 - b ∈ S := by
      simpa [m] using mem_of_le_consecutiveRunDown S hb_pos hb_le_s
    have hm_eq : m + 1 - b = m - b + 1 := by omega
    simpa [hm_eq] using hrun
  -- b ≠ m-b+1, otherwise slope < b contradicting α
  have hdiff : b ≠ m - b + 1 := by
    intro heq
    rcases hα with hα | hα
    · have hb_mem_D : b ∈ slopeSet S hne := by
        simp [slopeSet, b, hb_mem]
        omega
      exact hα.2 (by simpa [b] using hb_mem_D)
    · have hsminus : b ≤ slope S hne - 1 := by simpa [b] using hα
      have hb_lt_s : b + 1 ≤ slope S hne := by omega
      have hlow_mem : m + 1 - (b + 1) ∈ S := by
        simpa [m] using mem_of_le_consecutiveRunDown S (by omega) hb_lt_s
      have hmin_le : b ≤ m + 1 - (b + 1) := Finset.min'_le S _ hlow_mem
      omega
  -- Two distinct elements sum to m+1, so m+1 ≤ n
  have hm_lt_n : m + 1 ≤ n := by
    have hpair : ({b, m - b + 1} : Finset ℕ).sum id ≤ S.sum id :=
      Finset.sum_le_sum_of_subset (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hb_mem
        · exact hmb_mem)
    have hpair' : b + (m - b + 1) ≤ S.sum id := by
      simpa [Finset.sum_pair hdiff] using hpair
    have hpair'' : b + (m - b + 1) ≤ n := by
      rw [← hsum]
      exact hpair'
    omega
  have hm1_notin_S : m + 1 ∉ S := by
    intro hm1
    have hle : m + 1 ≤ m := Finset.le_max' S (m + 1) hm1
    omega
  have hm1_not_mem : m + 1 ∉ S \ ({b, m - b + 1} : Finset ℕ) := by
    intro hx
    exact hm1_notin_S (Finset.mem_sdiff.mp hx).1
  -- The disjointness needed for sum_union
  have hdisj : Disjoint (S \ {b, m - b + 1}) ({m + 1} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    simpa using hm1_not_mem
  -- Sum is preserved: remove b and m-b+1, add m+1
  have hsum' : (alpha S hne).sum id = n := by
    have hsdiff := Finset.sum_sdiff (s₁ := ({b, m - b + 1} : Finset ℕ)) (s₂ := S) (f := id)
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hb_mem
        · exact hmb_mem)
    rw [alpha, Finset.sum_union hdisj, Finset.sum_singleton]
    simp only [id_eq]
    have hsdiff' : ∑ x ∈ S \ ({b, m - b + 1} : Finset ℕ), x + (b + (m - b + 1)) = S.sum id := by
      simpa [Finset.sum_pair hdiff] using hsdiff
    rw [hsum] at hsdiff'
    omega
  -- Conclude membership
  rw [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, hsum', ?_⟩
  · intro x hx
    have hx' : x ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
      simpa [alpha, b, m] using hx
    rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
    · exact hrange (Finset.mem_sdiff.mp hxsdiff).1
    · have hxeq : x = m + 1 := by simpa using hxsingle
      rw [hxeq]
      simp [Finset.mem_range]
      omega
  · intro x hx
    have hx' : x ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
      simpa [alpha, b, m] using hx
    rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
    · exact hpos x (Finset.mem_sdiff.mp hxsdiff).1
    · have hxeq : x = m + 1 := by simpa using hxsingle
      rw [hxeq]
      omega

lemma slope_pos_of_pos (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x) : 0 < slope S hne := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hpos _ (Finset.max'_mem S hne))) with ⟨k, hk⟩
  have hk_mem : k + 1 ∈ S := by simpa [hk] using Finset.max'_mem S hne
  rw [slope, hk, consecutiveRunDown, if_pos hk_mem]
  omega

lemma le_consecutiveRunDown_of_mem (S : Finset ℕ) :
    ∀ {n k : ℕ}, k ≤ n + 1 →
      (∀ i, 0 < i → i ≤ k → n + 1 - i ∈ S) →
      k ≤ consecutiveRunDown S n := by
  intro n
  induction n with
  | zero =>
      intro k hk hmem
      have hk' : k ≤ 1 := by omega
      rcases Nat.eq_zero_or_eq_succ_pred k with rfl | hkpos
      · simp [consecutiveRunDown]
      · have hk1 : k = 1 := by omega
        subst k
        have h0 : 0 ∈ S := by simpa using hmem 1 (by omega) (by omega)
        simp [consecutiveRunDown, h0]
  | succ n ih =>
      intro k hk hmem
      rcases Nat.eq_zero_or_eq_succ_pred k with rfl | hkpos
      · simp [consecutiveRunDown]
      · let k' := k - 1
        have hk_succ : k = k' + 1 := by
          dsimp [k']
          omega
        have htop : n + 1 ∈ S := by
          simpa [hk_succ] using hmem 1 (by omega) (by omega)
        have hk' : k' ≤ n + 1 := by
          dsimp [k']
          omega
        have hmem' : ∀ i, 0 < i → i ≤ k' → n + 1 - i ∈ S := by
          intro i hi0 hik
          have hkik : i + 1 ≤ k := by
            rw [hk_succ]
            omega
          have h := hmem (i + 1) (by omega) hkik
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        have hrec : k' ≤ consecutiveRunDown S n := ih hk' hmem'
        rw [hk_succ]
        rw [consecutiveRunDown, if_pos htop]
        omega

lemma beta_nonempty_of_applicable (S : Finset ℕ) (hne : S.Nonempty)
    (hβ : beta_applicable S hne) : (beta S hne).Nonempty := by
  let s := slope S hne
  let m := S.max' hne
  have hs_lt_b : s < base S hne := by
    rcases hβ with hβ | hβ
    · simpa [beta_applicable, s] using hβ.1
    · omega
  have hs_lt_m : s < m := by
    exact lt_of_lt_of_le hs_lt_b (Finset.min'_le S m (Finset.max'_mem S hne))
  refine ⟨s, ?_⟩
  change s ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
  simp [hs_lt_m.ne, m, s]

lemma beta_mem_all_distinct (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ beta_partitions n) :
    beta S (nonempty_of_beta_mem n S hS) ∈ all_distinct_partitions n := by
  set hne := nonempty_of_beta_mem n S hS
  set s := slope S hne
  set m := S.max' hne
  set b := base S hne
  simp only [beta_partitions, Finset.mem_filter, dif_pos hne] at hS
  obtain ⟨hmem, hβ⟩ := hS
  simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
  obtain ⟨hrange, hsum, hpos⟩ := hmem
  have hm_mem : m ∈ S := Finset.max'_mem S hne
  have hb_mem : b ∈ S := Finset.min'_mem S hne
  have hs_pos : 0 < s := by
    simpa [s] using slope_pos_of_pos S hne hpos
  have hs_lt_b : s < b := by
    rcases hβ with hβ | hβ
    · simpa [beta_applicable, b, s] using hβ.1
    · omega
  have hs_lt_m : s < m := by
    exact lt_of_lt_of_le hs_lt_b (Finset.min'_le S m hm_mem)
  have hs_not_mem : s ∉ S := by
    intro hs_mem
    exact (not_lt_of_ge (Finset.min'_le S s hs_mem)) hs_lt_b
  have hb_le_runstart : b ≤ m - s + 1 := by
    have hrunstart_mem : m - s + 1 ∈ S := by
      have hs_le : s ≤ slope S hne := by simp [s]
      have h := mem_of_le_consecutiveRunDown S hs_pos hs_le
      have hm_eq : m + 1 - s = m - s + 1 := by omega
      simpa [m, s, hm_eq] using h
    exact Finset.min'_le S _ hrunstart_mem
  have hs_lt_hms : s < m - s := by
    rcases hβ with hβ | hβ
    · have hb_not_D := hβ.2
      have hb_cut : b < m + 1 - s := by
        by_contra hge
        have hb_mem_D : b ∈ slopeSet S hne := by
          simp [slopeSet, b, hb_mem]
          omega
        exact hb_not_D hb_mem_D
      omega
    · omega
  have hs_ne_hms : s ≠ m - s := ne_of_lt hs_lt_hms
  have hms_pos : 0 < m - s := by
    exact lt_trans hs_pos hs_lt_hms
  have hms_not_mem : m - s ∉ S := by
    intro hms_mem
    have hs1_le : s + 1 ≤ slope S hne := by
      apply le_consecutiveRunDown_of_mem S (n := m) (k := s + 1)
      · omega
      · intro i hi0 hik
        by_cases his : i = s + 1
        · subst his
          simpa [m] using hms_mem
        · have hik' : i ≤ s := by omega
          have h := mem_of_le_consecutiveRunDown S hi0 (by simpa [s] using hik')
          simpa [m] using h
    omega
  have h_union_disj : Disjoint S ({s, m - s} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro x hxS hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl
    · exact hs_not_mem hxS
    · exact hms_not_mem hxS
  have hsum' : (beta S hne).sum id = n := by
    have hsdiff := Finset.sum_sdiff (s₁ := ({m} : Finset ℕ))
      (s₂ := S ∪ ({s, m - s} : Finset ℕ)) (f := id) (by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact Finset.mem_union.mpr (Or.inl hm_mem))
    have hbetaeq : (beta S hne).sum id + m = n + (s + (m - s)) := by
      have hsdiff' : (beta S hne).sum id + m = ∑ x ∈ S ∪ ({s, m - s} : Finset ℕ), x := by
        simpa [beta] using hsdiff
      calc
        (beta S hne).sum id + m = ∑ x ∈ S ∪ ({s, m - s} : Finset ℕ), x := hsdiff'
        _ = S.sum id + ∑ x ∈ ({s, m - s} : Finset ℕ), x := by
              simpa using (Finset.sum_union h_union_disj : ∑ x ∈ S ∪ ({s, m - s} : Finset ℕ), x =
                ∑ x ∈ S, x + ∑ x ∈ ({s, m - s} : Finset ℕ), x)
        _ = n + (s + (m - s)) := by
              rw [Finset.sum_pair hs_ne_hms, hsum]
    omega
  rw [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, hsum', ?_⟩
  · intro x hx
    have hx' : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) := by
      simpa [beta, s, m] using hx
    have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hx').1
    rcases Finset.mem_union.mp hxU with hxS | hxpair
    · exact hrange hxS
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
      rcases hxpair with rfl | rfl
      · have hm_range := hrange hm_mem
        simp [Finset.mem_range] at hm_range
        simp [Finset.mem_range]
        omega
      · have hm_range := hrange hm_mem
        simp [Finset.mem_range] at hm_range
        simp [Finset.mem_range]
        omega
  · intro x hx
    have hx' : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) := by
      simpa [beta, s, m] using hx
    have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hx').1
    rcases Finset.mem_union.mp hxU with hxS | hxpair
    · exact hpos x hxS
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
      rcases hxpair with rfl | rfl
      · exact hs_pos
      · exact hms_pos

lemma alpha_maps_applicable_to_beta_applicable
    (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hα : alpha_applicable S hne) :
    beta_applicable (alpha S hne) (alpha_nonempty S hne) := by
  set b := base S hne
  set m := S.max' hne
  set T := alpha S hne
  set hneT := alpha_nonempty S hne
  have hb_mem : b ∈ S := Finset.min'_mem S hne
  have hb_pos : 0 < b := hpos b hb_mem
  have hb_le_m : b ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
  have hb_le_m : b ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
  have hb_le_s : b ≤ slope S hne := by
    rcases hα with hα | hα
    · simpa [alpha_applicable, b] using hα.1
    · have hsminus : b ≤ slope S hne - 1 := by
        simpa [alpha_applicable, b] using hα
      omega
  have hmb_mem : m - b + 1 ∈ S := by
    have hrun : m + 1 - b ∈ S := by
      simpa [m] using mem_of_le_consecutiveRunDown S hb_pos hb_le_s
    have hm_eq : m + 1 - b = m - b + 1 := by omega
    simpa [hm_eq] using hrun
  have hdiff : b ≠ m - b + 1 := by
    intro heq
    rcases hα with hα | hα
    · have hb_mem_D : b ∈ slopeSet S hne := by
        simp [slopeSet, b, hb_mem]
        omega
      exact hα.2 (by simpa [alpha_applicable, b] using hb_mem_D)
    · have hsminus : b ≤ slope S hne - 1 := by
        simpa [alpha_applicable, b] using hα
      have hb_lt_s : b + 1 ≤ slope S hne := by omega
      have hlow_mem : m + 1 - (b + 1) ∈ S := by
        simpa [m] using mem_of_le_consecutiveRunDown S (by omega) hb_lt_s
      have hmin_le : b ≤ m + 1 - (b + 1) := Finset.min'_le S _ hlow_mem
      omega
  have hb_lt_partner : b < m - b + 1 := by
    have hle : b ≤ m - b + 1 := Finset.min'_le S _ hmb_mem
    exact lt_of_le_of_ne hle hdiff
  have hcutoff_ge : b + 2 ≤ m + 2 - b := by
    omega
  have hb_lt_partner : b < m - b + 1 := by
    have hle : b ≤ m - b + 1 := Finset.min'_le S _ hmb_mem
    exact lt_of_le_of_ne hle hdiff
  have hcutoff_ge : b + 2 ≤ m + 2 - b := by
    omega
  have hm1_memT : m + 1 ∈ T := by
    have hm1_single : m + 1 ∈ ({m + 1} : Finset ℕ) := by simp
    change m + 1 ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ)
    exact Finset.mem_union.mpr (Or.inr hm1_single)
  have hpartner_not_memT : m - b + 1 ∉ T := by
    intro hx
    have hx' : m - b + 1 ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
      simpa [T, alpha, b, m] using hx
    rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
    · exact (Finset.mem_sdiff.mp hxsdiff).2 (by simp)
    · have : m - b + 1 = m + 1 := by simpa using hxsingle
      omega
  have hmaxT : T.max' hneT = m + 1 := by
    apply le_antisymm
    · apply Finset.max'_le T hneT (m + 1)
      intro x hx
      have hx' : x ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
        simpa [T, alpha, b, m] using hx
      rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
      · have hxS : x ∈ S := (Finset.mem_sdiff.mp hxsdiff).1
        exact (Finset.le_max' S x hxS).trans (by simp [m])
      · have : x = m + 1 := by simpa using hxsingle
        omega
    · exact Finset.le_max' T (m + 1) hm1_memT
  have hb_le_slopeT : b ≤ slope T hneT := by
    rw [slope, hmaxT]
    apply le_consecutiveRunDown_of_mem T
    · omega
    · intro i hi0 hik
      by_cases hi1 : i = 1
      · subst i
        exact hm1_memT
      · have him1_pos : 0 < i - 1 := by omega
        have him1_le : i - 1 ≤ slope S hne := by omega
        have hmemS : m + 1 - (i - 1) ∈ S := by
          exact mem_of_le_consecutiveRunDown S him1_pos him1_le
        have hmemT : m + 2 - i ∈ T := by
          have hxS : m + 2 - i ∈ S := by
            have hxeq : m + 2 - i = m + 1 - (i - 1) := by omega
            simpa [hxeq] using hmemS
          have hxb : m + 2 - i ≠ b := by
            have hi_ge_two : 2 ≤ i := by omega
            omega
          have hxpartner : m + 2 - i ≠ m - b + 1 := by
            have hi_ge_two : 2 ≤ i := by omega
            omega
          have : m + 2 - i ∈ S \ ({b, m - b + 1} : Finset ℕ) := by
            simp [hxS, hxb, hxpartner]
          exact Finset.mem_union.mpr <| Or.inl this
        simpa [T] using hmemT
  have hslopeT_le : slope T hneT ≤ b := by
    by_contra hlt
    have hb1_le : b + 1 ≤ slope T hneT := by omega
    have hpartner_memT : m - b + 1 ∈ T := by
      have hmem := mem_of_le_consecutiveRunDown T (n := m + 1) (k := b + 1) (by omega) (by
        rw [slope, hmaxT] at hb1_le
        exact hb1_le)
      have hm_eq : m + 1 - b = m - b + 1 := by omega
      simpa [hmaxT, hm_eq] using hmem
    exact hpartner_not_memT hpartner_memT
  have hslopeT : slope T hneT = b := by omega
  have hbaseT_gt : b < base T hneT := by
    have hbT_mem : base T hneT ∈ T := Finset.min'_mem T hneT
    have hall_gt : ∀ x ∈ T, b < x := by
      intro x hx
      have hx' : x ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
        simpa [T, alpha, b, m] using hx
      rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
      · have hxS : x ∈ S := (Finset.mem_sdiff.mp hxsdiff).1
        have hb_le_x : b ≤ x := Finset.min'_le S x hxS
        have hxb : x ≠ b := by
          exact fun hxeq => (Finset.mem_sdiff.mp hxsdiff).2 (by simp [hxeq])
        omega
      · have : x = m + 1 := by simpa using hxsingle
        omega
    exact hall_gt _ hbT_mem
  by_cases hbaseD : base T hneT ∈ slopeSet T hneT
  · right
    have hbase_ge_cutoff : m + 2 - b ≤ base T hneT := by
      have hbaseD' := hbaseD
      simp [slopeSet, hmaxT, hslopeT] at hbaseD'
      omega
    rw [hslopeT]
    exact le_trans hcutoff_ge hbase_ge_cutoff
  · left
    refine ⟨?_, hbaseD⟩
    rw [hslopeT]
    exact hbaseT_gt

lemma beta_maps_applicable_to_alpha_applicable
    (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hβ : beta_applicable S hne) :
    alpha_applicable (beta S hne) (beta_nonempty_of_applicable S hne hβ) := by
  set s := slope S hne
  set m := S.max' hne
  set T := beta S hne
  set hneT := beta_nonempty_of_applicable S hne hβ
  have hm_mem : m ∈ S := Finset.max'_mem S hne
  have hb_mem : base S hne ∈ S := Finset.min'_mem S hne
  have hs_pos : 0 < s := by
    simpa [s] using slope_pos_of_pos S hne hpos
  have hs_lt_b : s < base S hne := by
    rcases hβ with hβ | hβ
    · simpa [beta_applicable, s] using hβ.1
    · omega
  have hs_lt_m : s < m := by
    exact lt_of_lt_of_le hs_lt_b (Finset.min'_le S m hm_mem)
  have hb_le_runstart : base S hne ≤ m - s + 1 := by
    have hrunstart_mem : m - s + 1 ∈ S := by
      have hs_le : s ≤ slope S hne := by simp [s]
      have h := mem_of_le_consecutiveRunDown S hs_pos hs_le
      have hm_eq : m + 1 - s = m - s + 1 := by omega
      simpa [m, s, hm_eq] using h
    exact Finset.min'_le S _ hrunstart_mem
  have hs_lt_hms : s < m - s := by
    rcases hβ with hβ | hβ
    · have hb_not_D := hβ.2
      have hb_cut : base S hne < m + 1 - s := by
        by_contra hge
        have hb_mem_D : base S hne ∈ slopeSet S hne := by
          simp [slopeSet, hb_mem]
          omega
        exact hb_not_D hb_mem_D
      omega
    · have hs2b : s + 2 ≤ base S hne := by
          simpa [beta_applicable, s] using hβ
      have hs1_hms : s + 1 ≤ m - s := by
        have hs2_hms1 : s + 2 ≤ m - s + 1 := le_trans hs2b hb_le_runstart
        omega
      omega
  have hs_memT : s ∈ T := by
    change s ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inr (by simp))
    · simp
      omega
  have hall_ge_s : ∀ x ∈ T, s ≤ x := by
    intro x hx
    have hx' : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) := by
      simpa [T, beta, s, m] using hx
    have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hx').1
    rcases Finset.mem_union.mp hxU with hxS | hxpair
    · have hb_le_x : base S hne ≤ x := Finset.min'_le S x hxS
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
      rcases hxpair with rfl | rfl
      · omega
      · omega
  have hbaseT : base T hneT = s := by
    apply le_antisymm
    · exact Finset.min'_le T s hs_memT
    · exact hall_ge_s _ (Finset.min'_mem T hneT)
  have hm1_memT : m - 1 ∈ T := by
    by_cases hs1 : s = 1
    · change m - 1 ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · refine Finset.mem_union.mpr (Or.inr ?_)
        simp [hs1]
      · simp
        omega
    · have hs2 : 2 ≤ s := by omega
      have hm1S : m - 1 ∈ S := by
        have h := mem_of_le_consecutiveRunDown S (n := m) (k := 2) (by omega)
          (by simpa [s] using hs2)
        simpa [m] using h
      change m - 1 ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union.mpr (Or.inl hm1S)
      · simp
        omega
  have hmaxT : T.max' hneT = m - 1 := by
    apply le_antisymm
    · apply Finset.max'_le T hneT (m - 1)
      intro x hx
      have hx' : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) := by
        simpa [T, beta, s, m] using hx
      have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hx').1
      rcases Finset.mem_union.mp hxU with hxS | hxpair
      · have hx_ne_m : x ≠ m := by
          exact fun hxeq => (Finset.mem_sdiff.mp hx').2 (by simp [hxeq])
        have hx_le_m : x ≤ m := Finset.le_max' S x hxS
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with rfl | rfl <;> omega
    · exact Finset.le_max' T _ hm1_memT
  have hs_le_slopeT : s ≤ slope T hneT := by
    rw [slope, hmaxT]
    apply le_consecutiveRunDown_of_mem T
    · omega
    · intro i hi0 hik
      by_cases his : i = s
      · subst his
        have hms_memT : m - s ∈ T := by
          change m - s ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union.mpr (Or.inr ?_)
            simp
          · simp
            omega
        have hm_eq : m - 1 + 1 - s = m - s := by omega
        simpa [hm_eq] using hms_memT
      · have hik_lt : i < s := by omega
        have hmemiS : m - i ∈ S := by
          have hii : i + 1 ≤ s := by omega
          have h := mem_of_le_consecutiveRunDown S (n := m) (k := i + 1) (by omega)
            (by simpa [s] using hii)
          have hm_eq : m + 1 - (i + 1) = m - i := by omega
          simpa [m, hm_eq] using h
        have hmemiT : m - i ∈ T := by
          change m - i ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · exact Finset.mem_union.mpr (Or.inl hmemiS)
          · simp
            omega
        have hm_eq : m - 1 + 1 - i = m - i := by omega
        simpa [hm_eq] using hmemiT
  by_cases hs_in_D : s ∈ slopeSet T hneT
  · right
    have hbaseT' : base (beta S hne) hneT = s := by
      simpa [T] using hbaseT
    rw [hbaseT']
    have hcut : m - slope T hneT ≤ s := by
      simp [slopeSet, hmaxT] at hs_in_D
      omega
    have hm_s_gt_s : s + 1 ≤ m - s := by
      exact Nat.succ_le_of_lt hs_lt_hms
    have hs1_le_slopeT : s + 1 ≤ slope T hneT := by
      have hm_s_le_slopeT : m - s ≤ slope T hneT := by omega
      exact le_trans hm_s_gt_s hm_s_le_slopeT
    have hs1_le_slopeT' : s + 1 ≤ slope (beta S hne) hneT := by
      simpa [T] using hs1_le_slopeT
    omega
  · left
    rw [hbaseT]
    exact ⟨hs_le_slopeT, hs_in_D⟩

theorem alpha_maps_to_beta (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ alpha_partitions n) :
    alpha S (nonempty_of_alpha_mem n S hS) ∈ beta_partitions n := by
  classical
  let hne := nonempty_of_alpha_mem n S hS
  let T := alpha S hne
  have hmemT : T ∈ all_distinct_partitions n := by
    simpa [T, hne] using alpha_mem_all_distinct n S hS
  have hneT : T.Nonempty := by
    simpa [T, hne] using alpha_nonempty S hne
  have hα : alpha_applicable S hne := by
    simpa [hne] using alpha_applicable_of_mem n S hS
  have hmemS : S ∈ all_distinct_partitions n := by
    have htmp : S ∈ all_distinct_partitions n ∧ alpha_applicable S hne := by
      simpa [alpha_partitions, hne] using hS
    exact htmp.1
  have hpos : ∀ x ∈ S, 0 < x := by
    simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
    exact hmemS.2.2
  have hβT : beta_applicable T hneT := by
    simpa [T, hne] using alpha_maps_applicable_to_beta_applicable S hne hpos hα
  exact mem_beta_partitions_of_mem_all_distinct_of_applicable n T hneT hmemT hβT

theorem beta_maps_to_alpha (n : ℕ) (S : Finset ℕ)
    (hS : S ∈ beta_partitions n) :
    beta S (nonempty_of_beta_mem n S hS) ∈ alpha_partitions n := by
  classical
  let hne := nonempty_of_beta_mem n S hS
  let T := beta S hne
  have hmemT : T ∈ all_distinct_partitions n := by
    simpa [T, hne] using beta_mem_all_distinct n S hS
  have hβ : beta_applicable S hne := by
    simpa [hne] using beta_applicable_of_mem n S hS
  have hmemS : S ∈ all_distinct_partitions n := by
    have htmp : S ∈ all_distinct_partitions n ∧ beta_applicable S hne := by
      simpa [beta_partitions, hne] using hS
    exact htmp.1
  have hpos : ∀ x ∈ S, 0 < x := by
    simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
    exact hmemS.2.2
  have hneT : T.Nonempty := by
    simpa [T, hne] using beta_nonempty_of_applicable S hne hβ
  have hαT : alpha_applicable T hneT := by
    simpa [T, hne] using beta_maps_applicable_to_alpha_applicable S hne hpos hβ
  exact mem_alpha_partitions_of_mem_all_distinct_of_applicable n T hneT hmemT hαT

lemma beta_alpha_eq_self (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hα : alpha_applicable S hne) :
    beta (alpha S hne) (alpha_nonempty S hne) = S := by
  classical
  set b := base S hne
  set m := S.max' hne
  set T := alpha S hne
  set hneT := alpha_nonempty S hne
  have hb_mem : b ∈ S := Finset.min'_mem S hne
  have hb_pos : 0 < b := hpos b hb_mem
  have hb_le_m : b ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
  have hb_le_s : b ≤ slope S hne := by
    rcases hα with hα | hα
    · simpa [alpha_applicable, b] using hα.1
    · have hsminus : b ≤ slope S hne - 1 := by
        simpa [alpha_applicable, b] using hα
      omega
  have hmb_mem : m - b + 1 ∈ S := by
    have hrun : m + 1 - b ∈ S := by
      simpa [m] using mem_of_le_consecutiveRunDown S hb_pos hb_le_s
    have hm_eq : m + 1 - b = m - b + 1 := by omega
    simpa [hm_eq] using hrun
  have hdiff : b ≠ m - b + 1 := by
    intro heq
    rcases hα with hα | hα
    · have hb_mem_D : b ∈ slopeSet S hne := by
        simp [slopeSet, b, hb_mem]
        omega
      exact hα.2 (by simpa [alpha_applicable, b] using hb_mem_D)
    · have hsminus : b ≤ slope S hne - 1 := by
        simpa [alpha_applicable, b] using hα
      have hb_lt_s : b + 1 ≤ slope S hne := by omega
      have hlow_mem : m + 1 - (b + 1) ∈ S := by
        simpa [m] using mem_of_le_consecutiveRunDown S (by omega) hb_lt_s
      have hmin_le : b ≤ m + 1 - (b + 1) := Finset.min'_le S _ hlow_mem
      omega
  have hb_lt_partner : b < m - b + 1 := by
    have hle : b ≤ m - b + 1 := Finset.min'_le S _ hmb_mem
    exact lt_of_le_of_ne hle hdiff
  have hcutoff_ge : b + 2 ≤ m + 2 - b := by
    omega
  have hm1_memT : m + 1 ∈ T := by
    have hm1_single : m + 1 ∈ ({m + 1} : Finset ℕ) := by simp
    change m + 1 ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ)
    exact Finset.mem_union.mpr (Or.inr hm1_single)
  have hpartner_not_memT : m - b + 1 ∉ T := by
    intro hx
    have hx' : m - b + 1 ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
      simpa [T, alpha, b, m] using hx
    rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
    · exact (Finset.mem_sdiff.mp hxsdiff).2 (by simp)
    · have : m - b + 1 = m + 1 := by simpa using hxsingle
      omega
  have hmaxT : T.max' hneT = m + 1 := by
    apply le_antisymm
    · apply Finset.max'_le T hneT (m + 1)
      intro x hx
      have hx' : x ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
        simpa [T, alpha, b, m] using hx
      rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
      · have hxS : x ∈ S := (Finset.mem_sdiff.mp hxsdiff).1
        exact (Finset.le_max' S x hxS).trans (by simp [m])
      · have : x = m + 1 := by simpa using hxsingle
        omega
    · exact Finset.le_max' T (m + 1) hm1_memT
  have hb_le_slopeT : b ≤ slope T hneT := by
    rw [slope, hmaxT]
    apply le_consecutiveRunDown_of_mem T
    · omega
    · intro i hi0 hik
      by_cases hi1 : i = 1
      · subst i
        exact hm1_memT
      · have him1_pos : 0 < i - 1 := by omega
        have him1_le : i - 1 ≤ slope S hne := by omega
        have hmemS : m + 1 - (i - 1) ∈ S := by
          exact mem_of_le_consecutiveRunDown S him1_pos him1_le
        have hmemT : m + 2 - i ∈ T := by
          have hxS : m + 2 - i ∈ S := by
            have hxeq : m + 2 - i = m + 1 - (i - 1) := by omega
            simpa [hxeq] using hmemS
          have hxb : m + 2 - i ≠ b := by
            have hi_ge_two : 2 ≤ i := by omega
            omega
          have hxpartner : m + 2 - i ≠ m - b + 1 := by
            have hi_ge_two : 2 ≤ i := by omega
            omega
          have : m + 2 - i ∈ S \ ({b, m - b + 1} : Finset ℕ) := by
            simp [hxS, hxb, hxpartner]
          exact Finset.mem_union.mpr <| Or.inl this
        simpa [T] using hmemT
  have hslopeT_le : slope T hneT ≤ b := by
    by_contra hlt
    have hb1_le : b + 1 ≤ slope T hneT := by omega
    have hpartner_memT : m - b + 1 ∈ T := by
      have hmem := mem_of_le_consecutiveRunDown T (n := m + 1) (k := b + 1) (by omega) (by
        rw [slope, hmaxT] at hb1_le
        exact hb1_le)
      have hm_eq : m + 1 - b = m - b + 1 := by omega
      simpa [hmaxT, hm_eq] using hmem
    exact hpartner_not_memT hpartner_memT
  have hslopeT : slope T hneT = b := by omega
  have hm_eq : m + 1 - b = m - b + 1 := by omega
  have hm1_notin_S : m + 1 ∉ S := by
    intro hm1
    have hle : m + 1 ≤ m := Finset.le_max' S (m + 1) hm1
    omega
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (T ∪ ({b, m - b + 1} : Finset ℕ)) \ ({m + 1} : Finset ℕ) := by
      simpa [beta, T, hmaxT, hslopeT, hm_eq] using hx
    have hxU : x ∈ T ∪ ({b, m - b + 1} : Finset ℕ) := (Finset.mem_sdiff.mp hx').1
    rcases Finset.mem_union.mp hxU with hxT | hxpair
    · have hxT' : x ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) := by
        simpa [T, alpha, b, m] using hxT
      rcases Finset.mem_union.mp hxT' with hxsdiff | hxsingle
      · exact (Finset.mem_sdiff.mp hxsdiff).1
      · have hxeq : x = m + 1 := by simpa using hxsingle
        exact False.elim ((Finset.mem_sdiff.mp hx').2 (by simp [hxeq]))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
      rcases hxpair with rfl | rfl
      · exact hb_mem
      · exact hmb_mem
  · intro hxS
    have hx_ne_max : x ≠ m + 1 := by
      intro hxeq
      exact hm1_notin_S (hxeq ▸ hxS)
    have hxU : x ∈ T ∪ ({b, m - b + 1} : Finset ℕ) := by
      by_cases hxb : x = b
      · exact Finset.mem_union.mpr (Or.inr (by simp [hxb]))
      · by_cases hxp : x = m - b + 1
        · exact Finset.mem_union.mpr (Or.inr (by simp [hxp]))
        · have hxnotpair : x ∉ ({b, m - b + 1} : Finset ℕ) := by
            simp [Finset.mem_insert, Finset.mem_singleton, hxb, hxp]
          have hxsdiff : x ∈ S \ ({b, m - b + 1} : Finset ℕ) :=
            Finset.mem_sdiff.mpr ⟨hxS, hxnotpair⟩
          have hxT : x ∈ T := by
            have : x ∈ (S \ ({b, m - b + 1} : Finset ℕ)) ∪ ({m + 1} : Finset ℕ) :=
              Finset.mem_union.mpr (Or.inl hxsdiff)
            simpa [T, alpha, b, m] using this
          exact Finset.mem_union.mpr (Or.inl hxT)
    have hxfinal : x ∈ (T ∪ ({b, m - b + 1} : Finset ℕ)) \ ({m + 1} : Finset ℕ) :=
      Finset.mem_sdiff.mpr ⟨hxU, by simp [hx_ne_max]⟩
    simpa [beta, T, hmaxT, hslopeT, hm_eq] using hxfinal

lemma alpha_beta_eq_self (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hβ : beta_applicable S hne) :
    alpha (beta S hne) (beta_nonempty_of_applicable S hne hβ) = S := by
  classical
  set s := slope S hne
  set m := S.max' hne
  set T := beta S hne
  set hneT := beta_nonempty_of_applicable S hne hβ
  have hm_mem : m ∈ S := Finset.max'_mem S hne
  have hs_pos : 0 < s := by
    simpa [s] using slope_pos_of_pos S hne hpos
  have hs_lt_b : s < base S hne := by
    rcases hβ with hβ | hβ
    · simpa [beta_applicable, s] using hβ.1
    · omega
  have hs_lt_m : s < m := by
    exact lt_of_lt_of_le hs_lt_b (Finset.min'_le S m hm_mem)
  have hb_mem : base S hne ∈ S := Finset.min'_mem S hne
  have hb_le_runstart : base S hne ≤ m - s + 1 := by
    have hrunstart_mem : m - s + 1 ∈ S := by
      have hs_le : s ≤ slope S hne := by simp [s]
      have h := mem_of_le_consecutiveRunDown S hs_pos hs_le
      have hm_eq : m + 1 - s = m - s + 1 := by omega
      simpa [m, s, hm_eq] using h
    exact Finset.min'_le S _ hrunstart_mem
  have hs_lt_hms : s < m - s := by
    rcases hβ with hβ | hβ
    · have hb_not_D := hβ.2
      have hb_cut : base S hne < m + 1 - s := by
        by_contra hge
        have hb_mem_D : base S hne ∈ slopeSet S hne := by
          simp [slopeSet, hb_mem]
          omega
        exact hb_not_D hb_mem_D
      omega
    · have hs2b : s + 2 ≤ base S hne := by
        simpa [beta_applicable, s] using hβ
      have hs2_hms1 : s + 2 ≤ m - s + 1 := le_trans hs2b hb_le_runstart
      omega
  have hs_ne_hms : s ≠ m - s := ne_of_lt hs_lt_hms
  have hs_not_mem : s ∉ S := by
    intro hs_mem
    exact (not_lt_of_ge (Finset.min'_le S s hs_mem)) hs_lt_b
  have hms_not_mem : m - s ∉ S := by
    intro hms_mem
    have hs1_le : s + 1 ≤ slope S hne := by
      apply le_consecutiveRunDown_of_mem S (n := m) (k := s + 1)
      · omega
      · intro i hi0 hik
        by_cases his : i = s + 1
        · subst his
          simpa [m] using hms_mem
        · have hik' : i ≤ s := by omega
          have h := mem_of_le_consecutiveRunDown S hi0 (by simpa [s] using hik')
          simpa [m] using h
    omega
  have hs_memT : s ∈ T := by
    change s ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inr (by simp))
    · simp
      omega
  have hall_ge_s : ∀ x ∈ T, s ≤ x := by
    intro x hx
    have hx' : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) := by
      simpa [T, beta, s, m] using hx
    have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hx').1
    rcases Finset.mem_union.mp hxU with hxS | hxpair
    · have hb_le_x : base S hne ≤ x := Finset.min'_le S x hxS
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
      rcases hxpair with rfl | rfl
      · omega
      · omega
  have hbaseT : base T hneT = s := by
    apply le_antisymm
    · exact Finset.min'_le T s hs_memT
    · exact hall_ge_s _ (Finset.min'_mem T hneT)
  have hm1_memT : m - 1 ∈ T := by
    by_cases hs1 : s = 1
    · change m - 1 ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · refine Finset.mem_union.mpr (Or.inr ?_)
        simp [hs1]
      · simp
        omega
    · have hs2 : 2 ≤ s := by omega
      have hm1S : m - 1 ∈ S := by
        have h := mem_of_le_consecutiveRunDown S (n := m) (k := 2) (by omega)
          (by simpa [s] using hs2)
        simpa [m] using h
      change m - 1 ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union.mpr (Or.inl hm1S)
      · simp
        omega
  have hmaxT : T.max' hneT = m - 1 := by
    apply le_antisymm
    · apply Finset.max'_le T hneT (m - 1)
      intro x hx
      have hx' : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) := by
        simpa [T, beta, s, m] using hx
      have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hx').1
      rcases Finset.mem_union.mp hxU with hxS | hxpair
      · have hx_ne_m : x ≠ m := by
          exact fun hxeq => (Finset.mem_sdiff.mp hx').2 (by simp [hxeq])
        have hx_le_m : x ≤ m := Finset.le_max' S x hxS
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with rfl | rfl <;> omega
    · exact Finset.le_max' T _ hm1_memT
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (T \ ({s, m - s} : Finset ℕ)) ∪ ({m} : Finset ℕ) := by
      have hm_eq : (m - 1) - s + 1 = m - s := by omega
      have hm_succ : m - 1 + 1 = m := by omega
      simpa [alpha, T, hbaseT, hmaxT, hm_eq, hm_succ] using hx
    rcases Finset.mem_union.mp hx' with hxsdiff | hxsingle
    · have hxT : x ∈ T := (Finset.mem_sdiff.mp hxsdiff).1
      have hxT' : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) := by
        simpa [T, beta, s, m] using hxT
      have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hxT').1
      rcases Finset.mem_union.mp hxU with hxS | hxpair
      · exact hxS
      · have hnot : x ∉ ({s, m - s} : Finset ℕ) := (Finset.mem_sdiff.mp hxsdiff).2
        exfalso
        exact hnot hxpair
    · have hxeq : x = m := by simpa using hxsingle
      exact hxeq ▸ hm_mem
  · intro hxS
    by_cases hxm : x = m
    · have : x ∈ ({m} : Finset ℕ) := by simp [hxm]
      have hxU : x ∈ (T \ ({s, m - s} : Finset ℕ)) ∪ ({m} : Finset ℕ) :=
        Finset.mem_union.mpr (Or.inr this)
      have hm_eq : (m - 1) - s + 1 = m - s := by omega
      have hm_succ : m - 1 + 1 = m := by omega
      simpa [alpha, T, hbaseT, hmaxT, hm_eq, hm_succ] using hxU
    · have hx_not_pair : x ∉ ({s, m - s} : Finset ℕ) := by
        intro hxpair
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with hxs | hxms
        · exact hs_not_mem (hxs ▸ hxS)
        · exact hms_not_mem (hxms ▸ hxS)
      have hxT : x ∈ T := by
        have hxU : x ∈ S ∪ ({s, m - s} : Finset ℕ) := Finset.mem_union.mpr (Or.inl hxS)
        have hxdiff : x ∈ (S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ) :=
          Finset.mem_sdiff.mpr ⟨hxU, by simp [hxm]⟩
        simpa [T, beta, s, m] using hxdiff
      have hxsdiff : x ∈ T \ ({s, m - s} : Finset ℕ) := Finset.mem_sdiff.mpr ⟨hxT, hx_not_pair⟩
      have hxU : x ∈ (T \ ({s, m - s} : Finset ℕ)) ∪ ({m} : Finset ℕ) :=
        Finset.mem_union.mpr (Or.inl hxsdiff)
      have hm_eq : (m - 1) - s + 1 = m - s := by omega
      have hm_succ : m - 1 + 1 = m := by omega
      simpa [alpha, T, hbaseT, hmaxT, hm_eq, hm_succ] using hxU

lemma alpha_card (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hα : alpha_applicable S hne) :
    (alpha S hne).card + 1 = S.card := by
  classical
  set b := base S hne
  set m := S.max' hne
  have hb_mem : b ∈ S := Finset.min'_mem S hne
  have hb_pos : 0 < b := hpos b hb_mem
  have hb_le_m : b ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
  have hb_le_s : b ≤ slope S hne := by
    rcases hα with hα | hα
    · simpa [alpha_applicable, b] using hα.1
    · have hsminus : b ≤ slope S hne - 1 := by
        simpa [alpha_applicable, b] using hα
      omega
  have hmb_mem : m - b + 1 ∈ S := by
    have hrun : m + 1 - b ∈ S := by
      simpa [m] using mem_of_le_consecutiveRunDown S hb_pos hb_le_s
    have hm_eq : m + 1 - b = m - b + 1 := by omega
    simpa [hm_eq] using hrun
  have hdiff : b ≠ m - b + 1 := by
    intro heq
    rcases hα with hα | hα
    · have hb_mem_D : b ∈ slopeSet S hne := by
        simp [slopeSet, b, hb_mem]
        omega
      exact hα.2 (by simpa [alpha_applicable, b] using hb_mem_D)
    · have hsminus : b ≤ slope S hne - 1 := by
        simpa [alpha_applicable, b] using hα
      have hb_lt_s : b + 1 ≤ slope S hne := by omega
      have hlow_mem : m + 1 - (b + 1) ∈ S := by
        simpa [m] using mem_of_le_consecutiveRunDown S (by omega) hb_lt_s
      have hmin_le : b ≤ m + 1 - (b + 1) := Finset.min'_le S _ hlow_mem
      omega
  have hm1_notin_S : m + 1 ∉ S := by
    intro hm1
    have hle : m + 1 ≤ m := Finset.le_max' S (m + 1) hm1
    omega
  have hsubset : ({b, m - b + 1} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hb_mem
    · exact hmb_mem
  have hdisj : Disjoint (S \ ({b, m - b + 1} : Finset ℕ)) ({m + 1} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    intro hx
    exact hm1_notin_S (Finset.mem_sdiff.mp hx).1
  calc
    (alpha S hne).card + 1
        = ((S \ ({b, m - b + 1} : Finset ℕ)).card + ({m + 1} : Finset ℕ).card) + 1 := by
            rw [alpha, Finset.card_union_of_disjoint hdisj]
    _ = (S \ ({b, m - b + 1} : Finset ℕ)).card + 2 := by simp
    _ = (S.card - ({b, m - b + 1} : Finset ℕ).card) + 2 := by
          rw [Finset.card_sdiff_of_subset hsubset]
    _ = (S.card - 2) + 2 := by rw [Finset.card_pair hdiff]
    _ = S.card := by
          have hpair_le : ({b, m - b + 1} : Finset ℕ).card ≤ S.card :=
            Finset.card_le_card hsubset
          rw [Finset.card_pair hdiff] at hpair_le
          omega

lemma beta_card (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hβ : beta_applicable S hne) :
    S.card + 1 = (beta S hne).card := by
  classical
  set s := slope S hne
  set m := S.max' hne
  have hm_mem : m ∈ S := Finset.max'_mem S hne
  have hs_pos : 0 < s := by
    simpa [s] using slope_pos_of_pos S hne hpos
  have hs_lt_b : s < base S hne := by
    rcases hβ with hβ | hβ
    · simpa [beta_applicable, s] using hβ.1
    · omega
  have hs_lt_m : s < m := by
    exact lt_of_lt_of_le hs_lt_b (Finset.min'_le S m hm_mem)
  have hb_mem : base S hne ∈ S := Finset.min'_mem S hne
  have hb_le_runstart : base S hne ≤ m - s + 1 := by
    have hrunstart_mem : m - s + 1 ∈ S := by
      have hs_le : s ≤ slope S hne := by simp [s]
      have h := mem_of_le_consecutiveRunDown S hs_pos hs_le
      have hm_eq : m + 1 - s = m - s + 1 := by omega
      simpa [m, s, hm_eq] using h
    exact Finset.min'_le S _ hrunstart_mem
  have hs_lt_hms : s < m - s := by
    rcases hβ with hβ | hβ
    · have hb_not_D := hβ.2
      have hb_cut : base S hne < m + 1 - s := by
        by_contra hge
        have hb_mem_D : base S hne ∈ slopeSet S hne := by
          simp [slopeSet, hb_mem]
          omega
        exact hb_not_D hb_mem_D
      omega
    · have hs2b : s + 2 ≤ base S hne := by
        simpa [beta_applicable, s] using hβ
      have hs2_hms1 : s + 2 ≤ m - s + 1 := le_trans hs2b hb_le_runstart
      omega
  have hs_ne_hms : s ≠ m - s := ne_of_lt hs_lt_hms
  have hs_not_mem : s ∉ S := by
    intro hs_mem
    exact (not_lt_of_ge (Finset.min'_le S s hs_mem)) hs_lt_b
  have hms_not_mem : m - s ∉ S := by
    intro hms_mem
    have hs1_le : s + 1 ≤ slope S hne := by
      apply le_consecutiveRunDown_of_mem S (n := m) (k := s + 1)
      · omega
      · intro i hi0 hik
        by_cases his : i = s + 1
        · subst his
          simpa [m] using hms_mem
        · have hik' : i ≤ s := by omega
          have h := mem_of_le_consecutiveRunDown S hi0 (by simpa [s] using hik')
          simpa [m] using h
    omega
  have hdisj : Disjoint S ({s, m - s} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro x hxS hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl
    · exact hs_not_mem hxS
    · exact hms_not_mem hxS
  have hm_mem_union : m ∈ S ∪ ({s, m - s} : Finset ℕ) := Finset.mem_union.mpr (Or.inl hm_mem)
  have hsingle_subset : ({m} : Finset ℕ) ⊆ S ∪ ({s, m - s} : Finset ℕ) := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    exact hm_mem_union
  calc
    S.card + 1 = S.card + ({s, m - s} : Finset ℕ).card - ({m} : Finset ℕ).card := by
      rw [Finset.card_pair hs_ne_hms]
      simp
    _ = (S ∪ ({s, m - s} : Finset ℕ)).card - ({m} : Finset ℕ).card := by
      rw [Finset.card_union_of_disjoint hdisj]
    _ = ((S ∪ ({s, m - s} : Finset ℕ)) \ ({m} : Finset ℕ)).card := by
      rw [Finset.card_sdiff_of_subset hsingle_subset]
    _ = (beta S hne).card := by rw [beta]

lemma alpha_card_parity_flip (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hα : alpha_applicable S hne) :
    (alpha S hne).card % 2 ≠ S.card % 2 := by
  have hcard := alpha_card S hne hpos hα
  intro hpar
  omega

lemma beta_card_parity_flip (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x)
    (hβ : beta_applicable S hne) :
    (beta S hne).card % 2 ≠ S.card % 2 := by
  have hcard := beta_card S hne hpos hβ
  intro hpar
  omega

noncomputable def odd_alpha_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 1) (alpha_partitions n)

noncomputable def even_alpha_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 0) (alpha_partitions n)

noncomputable def odd_beta_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 1) (beta_partitions n)

noncomputable def even_beta_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 0) (beta_partitions n)

theorem alpha_maps_odd_to_even_beta (n : ℕ) (S : Finset ℕ)
    (hSα : S ∈ alpha_partitions n) (hodd : S.card % 2 = 1) :
    alpha S (nonempty_of_alpha_mem n S hSα) ∈ even_beta_partitions n := by
  have hne : S.Nonempty := nonempty_of_alpha_mem n S hSα
  have hα : alpha_applicable S hne := alpha_applicable_of_mem n S hSα
  have hmemS : S ∈ all_distinct_partitions n := by
    have htmp : S ∈ all_distinct_partitions n ∧ alpha_applicable S hne := by
      simpa [alpha_partitions, hne] using hSα
    exact htmp.1
  have hpos : ∀ x ∈ S, 0 < x := by
    simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
    exact hmemS.2.2
  have hmemβ : alpha S hne ∈ beta_partitions n := alpha_maps_to_beta n S hSα
  have hpar : (alpha S hne).card % 2 = 0 := by
    have hcard := alpha_card S hne hpos hα
    omega
  simpa [even_beta_partitions, hne] using And.intro hmemβ hpar

theorem alpha_maps_even_to_odd_beta (n : ℕ) (S : Finset ℕ)
    (hSα : S ∈ alpha_partitions n) (heven : S.card % 2 = 0) :
    alpha S (nonempty_of_alpha_mem n S hSα) ∈ odd_beta_partitions n := by
  have hne : S.Nonempty := nonempty_of_alpha_mem n S hSα
  have hα : alpha_applicable S hne := alpha_applicable_of_mem n S hSα
  have hmemS : S ∈ all_distinct_partitions n := by
    have htmp : S ∈ all_distinct_partitions n ∧ alpha_applicable S hne := by
      simpa [alpha_partitions, hne] using hSα
    exact htmp.1
  have hpos : ∀ x ∈ S, 0 < x := by
    simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
    exact hmemS.2.2
  have hmemβ : alpha S hne ∈ beta_partitions n := alpha_maps_to_beta n S hSα
  have hpar : (alpha S hne).card % 2 = 1 := by
    have hcard := alpha_card S hne hpos hα
    omega
  simpa [odd_beta_partitions, hne] using And.intro hmemβ hpar

theorem beta_maps_odd_to_even_alpha (n : ℕ) (S : Finset ℕ)
    (hSβ : S ∈ beta_partitions n) (hodd : S.card % 2 = 1) :
    beta S (nonempty_of_beta_mem n S hSβ) ∈ even_alpha_partitions n := by
  have hne : S.Nonempty := nonempty_of_beta_mem n S hSβ
  have hβ : beta_applicable S hne := beta_applicable_of_mem n S hSβ
  have hmemS : S ∈ all_distinct_partitions n := by
    have htmp : S ∈ all_distinct_partitions n ∧ beta_applicable S hne := by
      simpa [beta_partitions, hne] using hSβ
    exact htmp.1
  have hpos : ∀ x ∈ S, 0 < x := by
    simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
    exact hmemS.2.2
  have hmemα : beta S hne ∈ alpha_partitions n := beta_maps_to_alpha n S hSβ
  have hpar : (beta S hne).card % 2 = 0 := by
    have hcard := beta_card S hne hpos hβ
    omega
  simpa [even_alpha_partitions, hne] using And.intro hmemα hpar

theorem beta_maps_even_to_odd_alpha (n : ℕ) (S : Finset ℕ)
    (hSβ : S ∈ beta_partitions n) (heven : S.card % 2 = 0) :
    beta S (nonempty_of_beta_mem n S hSβ) ∈ odd_alpha_partitions n := by
  have hne : S.Nonempty := nonempty_of_beta_mem n S hSβ
  have hβ : beta_applicable S hne := beta_applicable_of_mem n S hSβ
  have hmemS : S ∈ all_distinct_partitions n := by
    have htmp : S ∈ all_distinct_partitions n ∧ beta_applicable S hne := by
      simpa [beta_partitions, hne] using hSβ
    exact htmp.1
  have hpos : ∀ x ∈ S, 0 < x := by
    simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
    exact hmemS.2.2
  have hmemα : beta S hne ∈ alpha_partitions n := beta_maps_to_alpha n S hSβ
  have hpar : (beta S hne).card % 2 = 1 := by
    have hcard := beta_card S hne hpos hβ
    omega
  simpa [odd_alpha_partitions, hne] using And.intro hmemα hpar

def minusExceptional (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => k + i)

def plusExceptional (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => k + 1 + i)

lemma minusExceptional_nonempty {k : ℕ} (hk : 0 < k) : (minusExceptional k).Nonempty := by
  refine ⟨k, ?_⟩
  refine Finset.mem_image.mpr ⟨0, by simp [hk], by simp⟩

lemma plusExceptional_nonempty {k : ℕ} (hk : 0 < k) : (plusExceptional k).Nonempty := by
  refine ⟨k + 1, ?_⟩
  refine Finset.mem_image.mpr ⟨0, by simp [hk], by simp⟩

lemma minusExceptional_sum (k : ℕ) :
    (minusExceptional k).sum id = k * (3 * k - 1) / 2 := by
  rw [minusExceptional, Finset.sum_image]
  · simp_rw [id_eq]
    rw [Finset.sum_add_distrib, sum_range_id']
    simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm]
    have hdiv : (k * (k - 1) / 2) * 2 = k * (k - 1) := by
      rw [← sum_range_id' k]
      exact sum_range_id_mul_two' k
    have hdiv' : 2 * (k * (k - 1) / 2) = k * (k - 1) := by
      simpa [Nat.mul_comm] using hdiv
    have hcalc : 2 * (k * k + k * (k - 1) / 2) = k * (k * 3 - 1) := by
      calc
        2 * (k * k + k * (k - 1) / 2) = 2 * (k * k) + 2 * (k * (k - 1) / 2) := by
          rw [Nat.left_distrib]
        _ = 2 * (k * k) + k * (k - 1) := by rw [hdiv']
        _ = k * (2 * k) + k * (k - 1) := by
          simp [Nat.mul_assoc, Nat.mul_comm]
        _ = k * (2 * k + (k - 1)) := by rw [← Nat.mul_add]
        _ = k * (k * 3 - 1) := by
          have hinner : 2 * k + (k - 1) = 3 * k - 1 := by omega
          rw [hinner, Nat.mul_comm k 3]
    exact Nat.eq_div_of_mul_eq_right (by decide : 2 ≠ 0) hcalc
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

lemma plusExceptional_sum (k : ℕ) :
    (plusExceptional k).sum id = k * (3 * k + 1) / 2 := by
  rw [plusExceptional, Finset.sum_image]
  · simp_rw [id_eq]
    rw [Finset.sum_add_distrib, sum_range_id']
    simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm]
    have hdiv : (k * (k - 1) / 2) * 2 = k * (k - 1) := by
      rw [← sum_range_id' k]
      exact sum_range_id_mul_two' k
    have hdiv' : 2 * (k * (k - 1) / 2) = k * (k - 1) := by
      simpa [Nat.mul_comm] using hdiv
    have hcalc : 2 * ((k + 1) * k + k * (k - 1) / 2) = k * (k * 3 + 1) := by
      calc
        2 * ((k + 1) * k + k * (k - 1) / 2)
            = 2 * ((k + 1) * k) + 2 * (k * (k - 1) / 2) := by
              rw [Nat.left_distrib]
        _ = 2 * ((k + 1) * k) + k * (k - 1) := by rw [hdiv']
        _ = k * (2 * (k + 1)) + k * (k - 1) := by
              ac_rfl
        _ = k * (2 * (k + 1) + (k - 1)) := by rw [← Nat.mul_add]
        _ = k * (k * 3 + 1) := by
              cases k with
              | zero => simp
              | succ k =>
                  have hinner : 2 * (Nat.succ k + 1) + (Nat.succ k - 1) = 3 * Nat.succ k + 1 := by
                    omega
                  rw [hinner, Nat.mul_comm (Nat.succ k) 3]
    have hcalc' : 2 * (k * (k + 1) + k * (k - 1) / 2) = k * (k * 3 + 1) := by
      simpa [Nat.mul_comm] using hcalc
    exact Nat.eq_div_of_mul_eq_right (by decide : 2 ≠ 0) hcalc'
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

lemma minusExceptional_mem_all_distinct (n k : ℕ) (hk : 0 < k)
    (hn : n = k * (3 * k - 1) / 2) :
    minusExceptional k ∈ all_distinct_partitions n := by
  rw [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    simp only [Finset.mem_range] at hi
    rw [hn]
    simp [Finset.mem_range]
    have hxle : k + i ≤ (minusExceptional k).sum id := by
      exact Finset.single_le_sum (fun y _ => Nat.zero_le y) (by
        exact Finset.mem_image.mpr ⟨i, by simpa [Finset.mem_range] using hi, rfl⟩)
    rw [minusExceptional_sum] at hxle
    omega
  · simpa [hn] using minusExceptional_sum k
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    simp only [Finset.mem_range] at hi
    omega

lemma plusExceptional_mem_all_distinct (n k : ℕ) (hk : 0 < k)
    (hn : n = k * (3 * k + 1) / 2) :
    plusExceptional k ∈ all_distinct_partitions n := by
  rw [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    simp only [Finset.mem_range] at hi
    rw [hn]
    simp [Finset.mem_range]
    have hxle : k + 1 + i ≤ (plusExceptional k).sum id := by
      exact Finset.single_le_sum (fun y _ => Nat.zero_le y) (by
        exact Finset.mem_image.mpr ⟨i, by simpa [Finset.mem_range] using hi, rfl⟩)
    rw [plusExceptional_sum] at hxle
    omega
  · simpa [hn] using plusExceptional_sum k
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    simp only [Finset.mem_range] at hi
    omega

lemma max'_minusExceptional {k : ℕ} (hk : 0 < k) :
    (minusExceptional k).max' (minusExceptional_nonempty hk) = 2 * k - 1 := by
  apply le_antisymm
  · apply Finset.max'_le (minusExceptional k) (minusExceptional_nonempty hk) (2 * k - 1)
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    simp only [Finset.mem_range] at hi
    omega
  · have htop : 2 * k - 1 ∈ minusExceptional k := by
      refine Finset.mem_image.mpr ⟨k - 1, ?_, ?_⟩
      · simpa [Finset.mem_range] using Nat.pred_lt hk.ne'
      · omega
    exact Finset.le_max' (minusExceptional k) _ htop

lemma base_minusExceptional {k : ℕ} (hk : 0 < k) :
    base (minusExceptional k) (minusExceptional_nonempty hk) = k := by
  apply le_antisymm
  · have hk_mem : k ∈ minusExceptional k := by
      refine Finset.mem_image.mpr ⟨0, by simpa [Finset.mem_range] using hk, by omega⟩
    exact Finset.min'_le (minusExceptional k) _ hk_mem
  · have hmin_mem : base (minusExceptional k) (minusExceptional_nonempty hk) ∈ minusExceptional k :=
      Finset.min'_mem (minusExceptional k) (minusExceptional_nonempty hk)
    rcases Finset.mem_image.mp hmin_mem with ⟨i, hi, hEq⟩
    simp only [Finset.mem_range] at hi
    omega

lemma slope_minusExceptional {k : ℕ} (hk : 0 < k) :
    slope (minusExceptional k) (minusExceptional_nonempty hk) = k := by
  let S := minusExceptional k
  let hne := minusExceptional_nonempty hk
  have hmax : S.max' hne = 2 * k - 1 := by simpa [S, hne] using max'_minusExceptional hk
  have hlow : k ≤ slope S hne := by
    rw [slope, hmax]
    apply le_consecutiveRunDown_of_mem S
    · omega
    · intro i hi0 hik
      refine Finset.mem_image.mpr ⟨k - i, ?_, ?_⟩
      · simp [Finset.mem_range]
        omega
      · omega
  have hupp : slope S hne ≤ k := by
    by_contra hgt
    have hk1 : k + 1 ≤ slope S hne := by omega
    have hbad : 2 * k - 1 + 1 - (k + 1) ∈ S := by
      exact mem_of_le_consecutiveRunDown S (by omega) (by
        rw [slope, hmax] at hk1
        exact hk1)
    have hkbad : k - 1 ∈ S := by
      have hEq : 2 * k - 1 + 1 - (k + 1) = k - 1 := by omega
      simpa [hEq] using hbad
    rcases Finset.mem_image.mp hkbad with ⟨i, hi, hEq⟩
    simp only [Finset.mem_range] at hi
    omega
  exact Nat.le_antisymm hupp hlow

lemma max'_plusExceptional {k : ℕ} (hk : 0 < k) :
    (plusExceptional k).max' (plusExceptional_nonempty hk) = 2 * k := by
  apply le_antisymm
  · apply Finset.max'_le (plusExceptional k) (plusExceptional_nonempty hk) (2 * k)
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    simp only [Finset.mem_range] at hi
    omega
  · have htop : 2 * k ∈ plusExceptional k := by
      refine Finset.mem_image.mpr ⟨k - 1, ?_, ?_⟩
      · simpa [Finset.mem_range] using Nat.pred_lt hk.ne'
      · omega
    exact Finset.le_max' (plusExceptional k) _ htop

lemma base_plusExceptional {k : ℕ} (hk : 0 < k) :
    base (plusExceptional k) (plusExceptional_nonempty hk) = k + 1 := by
  apply le_antisymm
  · have hk_mem : k + 1 ∈ plusExceptional k := by
      refine Finset.mem_image.mpr ⟨0, by simpa [Finset.mem_range] using hk, by omega⟩
    exact Finset.min'_le (plusExceptional k) _ hk_mem
  · have hmin_mem : base (plusExceptional k) (plusExceptional_nonempty hk) ∈ plusExceptional k :=
      Finset.min'_mem (plusExceptional k) (plusExceptional_nonempty hk)
    rcases Finset.mem_image.mp hmin_mem with ⟨i, hi, hEq⟩
    simp only [Finset.mem_range] at hi
    omega

lemma slope_plusExceptional {k : ℕ} (hk : 0 < k) :
    slope (plusExceptional k) (plusExceptional_nonempty hk) = k := by
  let S := plusExceptional k
  let hne := plusExceptional_nonempty hk
  have hmax : S.max' hne = 2 * k := by simpa [S, hne] using max'_plusExceptional hk
  have hlow : k ≤ slope S hne := by
    rw [slope, hmax]
    apply le_consecutiveRunDown_of_mem S
    · omega
    · intro i hi0 hik
      refine Finset.mem_image.mpr ⟨k - i, ?_, ?_⟩
      · simp [Finset.mem_range]
        omega
      · omega
  have hupp : slope S hne ≤ k := by
    by_contra hgt
    have hk1 : k + 1 ≤ slope S hne := by omega
    have hbad : 2 * k + 1 - (k + 1) ∈ S := by
      exact mem_of_le_consecutiveRunDown S (by omega) (by
        rw [slope, hmax] at hk1
        exact hk1)
    have hkbad : k ∈ S := by
      have hEq : 2 * k + 1 - (k + 1) = k := by omega
      simpa [hEq] using hbad
    rcases Finset.mem_image.mp hkbad with ⟨i, hi, hEq⟩
    simp only [Finset.mem_range] at hi
    omega
  exact Nat.le_antisymm hupp hlow

lemma eq_minusExceptional_of_slope_eq_base
    (n : ℕ) (S : Finset ℕ) (hmem : S ∈ all_distinct_partitions n)
    (hne : S.Nonempty)
    (hD : base S hne ∈ slopeSet S hne)
    (hsb : slope S hne = base S hne) :
    S = minusExceptional (base S hne) := by
  classical
  set b := base S hne
  set m := S.max' hne
  simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
  obtain ⟨_, _, hpos⟩ := hmem
  have hb_mem : b ∈ S := Finset.min'_mem S hne
  have hb_pos : 0 < b := hpos b hb_mem
  have hb_le_m : b ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
  have hm_le : m ≤ 2 * b - 1 := by
    have hD' := hD
    simp [slopeSet, b, hsb, hb_mem] at hD'
    omega
  have hrun_bottom : m - b + 1 ∈ S := by
    have hrun : m + 1 - b ∈ S := by
      have hs_le : b ≤ slope S hne := by simp [b, hsb]
      simpa [m, b] using mem_of_le_consecutiveRunDown S hb_pos hs_le
    simpa [Nat.succ_eq_add_one, Nat.succ_sub hb_le_m, Nat.add_comm] using hrun
  have hm_ge : 2 * b - 1 ≤ m := by
    have hmin_le : b ≤ m - b + 1 := Finset.min'_le S _ hrun_bottom
    have hpred : b - 1 ≤ m - b := by omega
    have hsum : (b - 1) + b ≤ (m - b) + b := Nat.add_le_add_right hpred b
    omega
  have hm_eq : m = 2 * b - 1 := by omega
  ext x
  constructor
  · intro hx
    have hb_le_x : b ≤ x := Finset.min'_le S x hx
    have hx_le_m : x ≤ m := Finset.le_max' S x hx
    have hx_lt : x < 2 * b := by rw [hm_eq] at hx_le_m; omega
    have hi_lt : x - b < b := by omega
    refine Finset.mem_image.mpr ⟨x - b, ?_, ?_⟩
    · simpa [Finset.mem_range] using hi_lt
    · omega
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi_lt : i < b := by simpa [Finset.mem_range] using hi
    have hi_pos : 0 < m + 1 - (b + i) := by
      rw [hm_eq]
      omega
    have hi_le : m + 1 - (b + i) ≤ slope S hne := by
      rw [hm_eq]
      omega
    have hrun : m + 1 - (m + 1 - (b + i)) ∈ S := by
      exact mem_of_le_consecutiveRunDown S hi_pos hi_le
    have hx_eq : m + 1 - (m + 1 - (b + i)) = b + i := by
      rw [hm_eq]
      omega
    simpa [m, hx_eq] using hrun

lemma eq_plusExceptional_of_slope_eq_base_sub_one
    (n : ℕ) (S : Finset ℕ) (hmem : S ∈ all_distinct_partitions n)
    (hne : S.Nonempty)
    (hD : base S hne ∈ slopeSet S hne)
    (hsb : slope S hne = base S hne - 1) :
    S = plusExceptional (base S hne - 1) := by
  classical
  set b := base S hne
  set s := slope S hne
  set m := S.max' hne
  simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
  obtain ⟨_, _, hpos⟩ := hmem
  have hb_mem : b ∈ S := Finset.min'_mem S hne
  have hb_pos : 0 < b := hpos b hb_mem
  have hb_le_m : b ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
  have hs_eq : s = b - 1 := by simpa [s, b] using hsb
  have hm_le : m ≤ 2 * b - 2 := by
    have hD' := hD
    simp [slopeSet, b, s, hs_eq, hb_mem] at hD'
    omega
  have hrun_bottom : m - (b - 1) + 1 ∈ S := by
    have hs_pos : 0 < b - 1 := by
      rw [← hs_eq]
      exact slope_pos_nonempty S hne
    have hrun : m + 1 - (b - 1) ∈ S := by
      have hs_le : b - 1 ≤ slope S hne := by simp [s, hs_eq]
      simpa [m, s, hs_eq] using mem_of_le_consecutiveRunDown S hs_pos hs_le
    have hle : b - 1 ≤ m := by omega
    simpa [Nat.succ_eq_add_one, Nat.succ_sub hle, Nat.add_comm] using hrun
  have hm_ge : 2 * b - 2 ≤ m := by
    have hmin_le : b ≤ m - (b - 1) + 1 := Finset.min'_le S _ hrun_bottom
    have hpred : b - 1 ≤ m - (b - 1) := by omega
    have hsum : (b - 1) + (b - 1) ≤ (m - (b - 1)) + (b - 1) := Nat.add_le_add_right hpred (b - 1)
    omega
  have hm_eq : m = 2 * b - 2 := by omega
  ext x
  constructor
  · intro hx
    have hb_le_x : b ≤ x := Finset.min'_le S x hx
    have hx_le_m : x ≤ m := Finset.le_max' S x hx
    have hx_lt : x < 2 * b - 1 := by rw [hm_eq] at hx_le_m; omega
    have hi_lt : x - b < b - 1 := by omega
    refine Finset.mem_image.mpr ⟨x - b, ?_, ?_⟩
    · simpa [Finset.mem_range] using hi_lt
    · omega
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi_lt : i < b - 1 := by simpa [Finset.mem_range] using hi
    have hi_pos : 0 < m + 1 - (b + i) := by
      rw [hm_eq]
      omega
    have hi_le : m + 1 - (b + i) ≤ slope S hne := by
      rw [hm_eq]
      omega
    have hrun : m + 1 - (m + 1 - (b + i)) ∈ S := by
      exact mem_of_le_consecutiveRunDown S hi_pos hi_le
    have hrun' : m + 1 - (m + 1 - (b - 1 + (1 + i))) ∈ S := by
      convert hrun using 1 <;> omega
    have hx_final : m + 1 - (m + 1 - (b - 1 + (1 + i))) = b - 1 + (1 + i) := by
      rw [hm_eq]
      omega
    simpa [hx_final, Nat.add_assoc] using hrun'

theorem n_eq_generalized_pentagonal_of_neither_applicable
    (n : ℕ) (S : Finset ℕ) (hmem : S ∈ all_distinct_partitions n)
    (hne : S.Nonempty)
    (h : ¬ alpha_applicable S hne ∧ ¬ beta_applicable S hne) :
    (∃ k : ℕ, n = k * (3 * k - 1) / 2) ∨
      (∃ k : ℕ, n = k * (3 * k + 1) / 2) := by
  have hsum : S.sum id = n := by
    simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
    exact hmem.2.1
  rcases (neither_alpha_nor_beta_applicable_iff S hne).mp h with ⟨hD, hs⟩
  rcases hs with hsb | hsb
  · left
    set b := base S hne
    refine ⟨b, ?_⟩
    have hshape : S = minusExceptional b := by
      simpa [b] using eq_minusExceptional_of_slope_eq_base n S hmem hne hD hsb.symm
    calc
      n = S.sum id := by simpa using hsum.symm
      _ = (minusExceptional b).sum id := by rw [hshape]
      _ = b * (3 * b - 1) / 2 := by
            rw [minusExceptional_sum]
  · right
    set b := base S hne - 1
    refine ⟨b, ?_⟩
    have hshape : S = plusExceptional b := by
      have : base S hne - 1 = b := by rfl
      simpa [b] using eq_plusExceptional_of_slope_eq_base_sub_one n S hmem hne hD (by omega)
    calc
      n = S.sum id := by simpa using hsum.symm
      _ = (plusExceptional b).sum id := by rw [hshape]
      _ = b * (3 * b + 1) / 2 := by
            rw [plusExceptional_sum]

def IsGeneralizedPentagonal (n : ℕ) : Prop :=
  (∃ k : ℕ, n = k * (3 * k - 1) / 2) ∨
    (∃ k : ℕ, n = k * (3 * k + 1) / 2)

noncomputable def pentagonalCoeff (n : ℕ) : ℤ :=
  by
    classical
    exact if h₁ : ∃ k : ℕ, n = k * (3 * k - 1) / 2 then
      (-1 : ℤ) ^ Classical.choose h₁
    else if h₂ : ∃ k : ℕ, n = k * (3 * k + 1) / 2 then
      (-1 : ℤ) ^ Classical.choose h₂
    else
      0

noncomputable def regular_partitions (n : ℕ) : Finset (Finset ℕ) :=
  alpha_partitions n ∪ beta_partitions n

noncomputable def exceptional_partitions (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact Finset.filter
    (fun S => if hne : S.Nonempty then ¬ alpha_applicable S hne ∧ ¬ beta_applicable S hne else False)
    (all_distinct_partitions n)

noncomputable def regular_even_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 0) (regular_partitions n)

noncomputable def regular_odd_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 1) (regular_partitions n)

noncomputable def exceptional_even_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 0) (exceptional_partitions n)

noncomputable def exceptional_odd_partitions (n : ℕ) : Finset (Finset ℕ) :=
  Finset.filter (fun S => S.card % 2 = 1) (exceptional_partitions n)

/- Proof roadmap for Euler's pentagonal number theorem:
1. For `n > 0`, every partition in `all_distinct_partitions n` is either regular
   (`alpha` or `beta` applies) or exceptional (neither applies).
2. The regular partitions cancel in pairs because `alpha` and `beta` map between
   even and odd partitions and act as inverses on the regular locus.
3. The remaining contribution therefore comes only from the exceptional partitions.
4. Exceptional partitions exist exactly at generalized pentagonal numbers, and
   when they exist there is exactly one such partition whose parity gives the sign.
5. The `n = 0` case is handled separately inside the exceptional contribution theorem.
-/

lemma nonempty_of_mem_all_distinct_of_pos
    (n : ℕ) (hn : 0 < n) (S : Finset ℕ)
    (hS : S ∈ all_distinct_partitions n) : S.Nonempty := by
  simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨_, hsum, _⟩ := hS
  by_contra hempty
  have : S.sum id = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
  rw [hsum] at this
  omega

lemma mem_exceptional_partitions_iff
    (n : ℕ) (S : Finset ℕ) :
    S ∈ exceptional_partitions n ↔
      S ∈ all_distinct_partitions n ∧
      ∃ hne : S.Nonempty, ¬ alpha_applicable S hne ∧ ¬ beta_applicable S hne := by
  classical
  simp only [exceptional_partitions, Finset.mem_filter]
  constructor
  · intro hS
    obtain ⟨hmem, hcond⟩ := hS
    by_cases hne : S.Nonempty
    · simp only [dif_pos hne] at hcond
      exact ⟨hmem, ⟨hne, hcond⟩⟩
    · simp only [dif_neg hne] at hcond
  · rintro ⟨hmem, hne, hα, hβ⟩
    refine ⟨hmem, ?_⟩
    simp [hne, hα, hβ]

lemma minusExceptional_mem_exceptional (n k : ℕ) (hk : 0 < k)
    (hn : n = k * (3 * k - 1) / 2) :
    minusExceptional k ∈ exceptional_partitions n := by
  have hmem : minusExceptional k ∈ all_distinct_partitions n :=
    minusExceptional_mem_all_distinct n k hk hn
  have hne : (minusExceptional k).Nonempty := minusExceptional_nonempty hk
  have hbase : base (minusExceptional k) hne = k := base_minusExceptional hk
  have hslope : slope (minusExceptional k) hne = k := slope_minusExceptional hk
  have hbaseD : base (minusExceptional k) hne ∈ slopeSet (minusExceptional k) hne := by
    have hk_mem : k ∈ minusExceptional k := by
      refine Finset.mem_image.mpr ⟨0, by simpa [Finset.mem_range] using hk, by omega⟩
    simp [slopeSet, hbase, hslope, max'_minusExceptional hk, hk_mem]
    omega
  have hneither :
      ¬ alpha_applicable (minusExceptional k) hne ∧
      ¬ beta_applicable (minusExceptional k) hne := by
    exact (neither_alpha_nor_beta_applicable_iff (minusExceptional k) hne).mpr
      ⟨hbaseD, by simp [hbase, hslope]⟩
  rw [mem_exceptional_partitions_iff]
  exact ⟨hmem, hne, hneither.1, hneither.2⟩

lemma plusExceptional_mem_exceptional (n k : ℕ) (hk : 0 < k)
    (hn : n = k * (3 * k + 1) / 2) :
    plusExceptional k ∈ exceptional_partitions n := by
  have hmem : plusExceptional k ∈ all_distinct_partitions n :=
    plusExceptional_mem_all_distinct n k hk hn
  have hne : (plusExceptional k).Nonempty := plusExceptional_nonempty hk
  have hbase : base (plusExceptional k) hne = k + 1 := base_plusExceptional hk
  have hslope : slope (plusExceptional k) hne = k := slope_plusExceptional hk
  have hbaseD : base (plusExceptional k) hne ∈ slopeSet (plusExceptional k) hne := by
    have hk_mem : k + 1 ∈ plusExceptional k := by
      refine Finset.mem_image.mpr ⟨0, by simpa [Finset.mem_range] using hk, by omega⟩
    simp [slopeSet, hbase, hslope, max'_plusExceptional hk, hk_mem]
    omega
  have hneither :
      ¬ alpha_applicable (plusExceptional k) hne ∧
      ¬ beta_applicable (plusExceptional k) hne := by
    exact (neither_alpha_nor_beta_applicable_iff (plusExceptional k) hne).mpr
      ⟨hbaseD, by simp [hbase, hslope]⟩
  rw [mem_exceptional_partitions_iff]
  exact ⟨hmem, hne, hneither.1, hneither.2⟩

lemma sum_eq_of_mem_all_distinct {n : ℕ} {S : Finset ℕ}
    (hS : S ∈ all_distinct_partitions n) : S.sum id = n := by
  simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hS
  exact hS.2.1

lemma exceptional_eq_minus_or_plus
    (n : ℕ) (S : Finset ℕ) (hS : S ∈ exceptional_partitions n) :
    ∃ k : ℕ, 0 < k ∧ (S = minusExceptional k ∨ S = plusExceptional k) := by
  rw [mem_exceptional_partitions_iff] at hS
  rcases hS with ⟨hmem, hne, hα, hβ⟩
  rcases (neither_alpha_nor_beta_applicable_iff S hne).mp ⟨hα, hβ⟩ with ⟨hD, hs⟩
  rcases hs with hsb | hsb
  · refine ⟨base S hne, ?_, Or.inl ?_⟩
    · have hb_mem : base S hne ∈ S := Finset.min'_mem S hne
      have hpos : ∀ x ∈ S, 0 < x := by
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
        exact hmem.2.2
      exact hpos _ hb_mem
    · exact eq_minusExceptional_of_slope_eq_base n S hmem hne hD hsb.symm
  · refine ⟨base S hne - 1, ?_, Or.inr ?_⟩
    · have hs_pos : 0 < slope S hne := slope_pos_nonempty S hne
      omega
    · exact eq_plusExceptional_of_slope_eq_base_sub_one n S hmem hne hD (by omega)

lemma minusExceptional_card (k : ℕ) :
    (minusExceptional k).card = k := by
  rw [minusExceptional, Finset.card_image_of_injective]
  simp
  intro i j hij
  exact Nat.add_left_cancel hij

lemma plusExceptional_card (k : ℕ) :
    (plusExceptional k).card = k := by
  rw [plusExceptional, Finset.card_image_of_injective]
  simp
  intro i j hij
  exact Nat.add_left_cancel hij

lemma plusExceptional_eq_image_succ (k : ℕ) :
    plusExceptional k = (minusExceptional k).image Nat.succ := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    refine Finset.mem_image.mpr ⟨k + i, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hxy

lemma plusExceptional_sum_eq_minusExceptional_sum_add (k : ℕ) :
    (plusExceptional k).sum id = (minusExceptional k).sum id + k := by
  rw [plusExceptional_eq_image_succ, Finset.sum_image]
  · simp_rw [Nat.succ_eq_add_one, id_eq]
    rw [Finset.sum_add_distrib]
    have hone : ∑ x ∈ minusExceptional k, 1 = k := by
      rw [← Finset.card_eq_sum_ones, minusExceptional_card]
    rw [hone]
  · intro a _ b _ hab
    exact Nat.succ.inj hab

lemma minusExceptional_succ_eq_insert (k : ℕ) :
    minusExceptional (k + 1) = insert (2 * k + 1) (plusExceptional k) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, hxeq⟩
    have hi_lt : i < k + 1 := by simpa [Finset.mem_range] using hi
    by_cases hlast : i = k
    · subst hlast
      simp at hxeq ⊢
      omega
    · have hi_lt_k : i < k := by omega
      simp only [Finset.mem_insert]
      right
      refine Finset.mem_image.mpr ⟨i, by simpa [Finset.mem_range] using hi_lt_k, ?_⟩
      omega
  · intro hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · refine Finset.mem_image.mpr ⟨k, ?_, ?_⟩
      · simp [Finset.mem_range]
      · omega
    · rcases Finset.mem_image.mp hx with ⟨i, hi, hxi⟩
      refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
      · simp [Finset.mem_range] at hi ⊢
        omega
      · omega

lemma minusExceptional_sum_succ (k : ℕ) :
    (minusExceptional (k + 1)).sum id = (minusExceptional k).sum id + (3 * k + 1) := by
  rw [minusExceptional_succ_eq_insert, Finset.sum_insert]
  · rw [plusExceptional_sum_eq_minusExceptional_sum_add]
    simp [id_eq]
    omega
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, hxi⟩
    simp only [Finset.mem_range] at hi
    omega

lemma plusExceptional_sum_succ (k : ℕ) :
    (plusExceptional (k + 1)).sum id = (plusExceptional k).sum id + (3 * k + 2) := by
  rw [plusExceptional_sum_eq_minusExceptional_sum_add, minusExceptional_sum_succ,
    plusExceptional_sum_eq_minusExceptional_sum_add]
  omega

lemma minusExceptional_sum_strictMono :
    StrictMono (fun k => (minusExceptional k).sum id) := by
  exact strictMono_nat_of_lt_succ (fun k => by
    rw [minusExceptional_sum_succ]
    omega)

lemma plusExceptional_sum_strictMono :
    StrictMono (fun k => (plusExceptional k).sum id) := by
  exact strictMono_nat_of_lt_succ (fun k => by
    rw [plusExceptional_sum_succ]
    omega)

lemma minusExceptional_sum_lt_plusExceptional_sum {k : ℕ} (hk : 0 < k) :
    (minusExceptional k).sum id < (plusExceptional k).sum id := by
  rw [plusExceptional_sum_eq_minusExceptional_sum_add]
  omega

lemma plusExceptional_sum_lt_minusExceptional_sum_succ (k : ℕ) :
    (plusExceptional k).sum id < (minusExceptional (k + 1)).sum id := by
  rw [minusExceptional_sum_succ, plusExceptional_sum_eq_minusExceptional_sum_add]
  omega


lemma mem_regular_or_exceptional_of_mem_all_distinct
    (n : ℕ) (hn : 0 < n) (S : Finset ℕ)
    (hS : S ∈ all_distinct_partitions n) :
    S ∈ regular_partitions n ∨ S ∈ exceptional_partitions n := by
  classical
  have hne : S.Nonempty := nonempty_of_mem_all_distinct_of_pos n hn S hS
  by_cases hα : alpha_applicable S hne
  · left
    rw [regular_partitions, Finset.mem_union]
    left
    exact mem_alpha_partitions_of_mem_all_distinct_of_applicable n S hne hS hα
  · by_cases hβ : beta_applicable S hne
    · left
      rw [regular_partitions, Finset.mem_union]
      right
      exact mem_beta_partitions_of_mem_all_distinct_of_applicable n S hne hS hβ
    · right
      rw [mem_exceptional_partitions_iff]
      exact ⟨hS, ⟨hne, hα, hβ⟩⟩

lemma regular_exceptional_disjoint (n : ℕ) :
    Disjoint (regular_partitions n) (exceptional_partitions n) := by
  classical
  rw [Finset.disjoint_left]
  intro S hreg hexc
  rw [regular_partitions, Finset.mem_union] at hreg
  rw [mem_exceptional_partitions_iff] at hexc
  rcases hexc with ⟨_, hne, hα, hβ⟩
  rcases hreg with hαmem | hβmem
  · exact hα (alpha_applicable_of_mem n S hαmem)
  · exact hβ (beta_applicable_of_mem n S hβmem)

lemma regular_even_card_eq_regular_odd_card (n : ℕ) (hn : 0 < n) :
    (regular_even_partitions n).card = (regular_odd_partitions n).card := by
  classical
  have hreg_even :
      regular_even_partitions n = (even_alpha_partitions n) ∪ (even_beta_partitions n) := by
    ext S
    constructor
    · intro hS
      have hmem := Finset.mem_filter.mp hS
      rcases Finset.mem_union.mp hmem.1 with hα | hβ
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨hα, hmem.2⟩
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hβ, hmem.2⟩
    · intro hS
      rcases Finset.mem_union.mp hS with hα | hβ
      · exact Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hα).1),
          (Finset.mem_filter.mp hα).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mp hβ).1),
          (Finset.mem_filter.mp hβ).2⟩
  have hreg_odd :
      regular_odd_partitions n = (odd_alpha_partitions n) ∪ (odd_beta_partitions n) := by
    ext S
    constructor
    · intro hS
      have hmem := Finset.mem_filter.mp hS
      rcases Finset.mem_union.mp hmem.1 with hα | hβ
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨hα, hmem.2⟩
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hβ, hmem.2⟩
    · intro hS
      rcases Finset.mem_union.mp hS with hα | hβ
      · exact Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hα).1),
          (Finset.mem_filter.mp hα).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mp hβ).1),
          (Finset.mem_filter.mp hβ).2⟩
  have hdisj_even : Disjoint (even_alpha_partitions n) (even_beta_partitions n) := by
    rw [Finset.disjoint_left]
    intro S hα hβ
    exact (Finset.disjoint_left.mp (alpha_beta_disjoint n))
      ((Finset.mem_filter.mp hα).1) ((Finset.mem_filter.mp hβ).1)
  have hdisj_odd : Disjoint (odd_alpha_partitions n) (odd_beta_partitions n) := by
    rw [Finset.disjoint_left]
    intro S hα hβ
    exact (Finset.disjoint_left.mp (alpha_beta_disjoint n))
      ((Finset.mem_filter.mp hα).1) ((Finset.mem_filter.mp hβ).1)
  have hcard_evenα_oddβ :
      (even_alpha_partitions n).card = (odd_beta_partitions n).card := by
    refine Finset.card_bij'
      (fun S hS => alpha S (nonempty_of_alpha_mem n S ((Finset.mem_filter.mp hS).1)))
      (fun S hS => beta S (nonempty_of_beta_mem n S ((Finset.mem_filter.mp hS).1)))
      ?_ ?_ ?_ ?_
    · intro S hS
      exact alpha_maps_even_to_odd_beta n S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
    · intro S hS
      exact beta_maps_odd_to_even_alpha n S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
    · intro S hS
      have hSα : S ∈ alpha_partitions n := (Finset.mem_filter.mp hS).1
      have hne : S.Nonempty := nonempty_of_alpha_mem n S hSα
      have hα : alpha_applicable S hne := alpha_applicable_of_mem n S hSα
      have hmemS : S ∈ all_distinct_partitions n := by
        have htmp : S ∈ all_distinct_partitions n ∧ alpha_applicable S hne := by
          simpa [alpha_partitions, hne] using hSα
        exact htmp.1
      have hpos : ∀ x ∈ S, 0 < x := by
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
        exact hmemS.2.2
      simpa using beta_alpha_eq_self S hne hpos hα
    · intro S hS
      have hSβ : S ∈ beta_partitions n := (Finset.mem_filter.mp hS).1
      have hne : S.Nonempty := nonempty_of_beta_mem n S hSβ
      have hβ : beta_applicable S hne := beta_applicable_of_mem n S hSβ
      have hmemS : S ∈ all_distinct_partitions n := by
        have htmp : S ∈ all_distinct_partitions n ∧ beta_applicable S hne := by
          simpa [beta_partitions, hne] using hSβ
        exact htmp.1
      have hpos : ∀ x ∈ S, 0 < x := by
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
        exact hmemS.2.2
      simpa using alpha_beta_eq_self S hne hpos hβ
  have hcard_oddα_evenβ :
      (odd_alpha_partitions n).card = (even_beta_partitions n).card := by
    refine Finset.card_bij'
      (fun S hS => alpha S (nonempty_of_alpha_mem n S ((Finset.mem_filter.mp hS).1)))
      (fun S hS => beta S (nonempty_of_beta_mem n S ((Finset.mem_filter.mp hS).1)))
      ?_ ?_ ?_ ?_
    · intro S hS
      exact alpha_maps_odd_to_even_beta n S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
    · intro S hS
      exact beta_maps_even_to_odd_alpha n S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
    · intro S hS
      have hSα : S ∈ alpha_partitions n := (Finset.mem_filter.mp hS).1
      have hne : S.Nonempty := nonempty_of_alpha_mem n S hSα
      have hα : alpha_applicable S hne := alpha_applicable_of_mem n S hSα
      have hmemS : S ∈ all_distinct_partitions n := by
        have htmp : S ∈ all_distinct_partitions n ∧ alpha_applicable S hne := by
          simpa [alpha_partitions, hne] using hSα
        exact htmp.1
      have hpos : ∀ x ∈ S, 0 < x := by
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
        exact hmemS.2.2
      simpa using beta_alpha_eq_self S hne hpos hα
    · intro S hS
      have hSβ : S ∈ beta_partitions n := (Finset.mem_filter.mp hS).1
      have hne : S.Nonempty := nonempty_of_beta_mem n S hSβ
      have hβ : beta_applicable S hne := beta_applicable_of_mem n S hSβ
      have hmemS : S ∈ all_distinct_partitions n := by
        have htmp : S ∈ all_distinct_partitions n ∧ beta_applicable S hne := by
          simpa [beta_partitions, hne] using hSβ
        exact htmp.1
      have hpos : ∀ x ∈ S, 0 < x := by
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmemS
        exact hmemS.2.2
      simpa using alpha_beta_eq_self S hne hpos hβ
  rw [hreg_even, hreg_odd, Finset.card_union_of_disjoint hdisj_even,
    Finset.card_union_of_disjoint hdisj_odd]
  rw [hcard_evenα_oddβ, hcard_oddα_evenβ]
  omega

lemma partition_counts_split_even (n : ℕ) (hn : 0 < n) :
    p_e n = (regular_even_partitions n).card + (exceptional_even_partitions n).card := by
  classical
  have hdisj : Disjoint (regular_even_partitions n) (exceptional_even_partitions n) := by
    rw [Finset.disjoint_left]
    intro S hreg hexc
    exact (Finset.disjoint_left.mp (regular_exceptional_disjoint n))
      ((Finset.mem_filter.mp hreg).1) ((Finset.mem_filter.mp hexc).1)
  have hunion :
      even_distinct_partitions n = (regular_even_partitions n) ∪ (exceptional_even_partitions n) := by
    ext S
    constructor
    · intro hS
      simp only [even_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨hpow, hsum, hpos, hpar⟩ := hS
      have hmem : S ∈ all_distinct_partitions n := by
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hpow, hsum, hpos⟩
      rcases mem_regular_or_exceptional_of_mem_all_distinct n hn S hmem with hreg | hexc
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hreg, hpar⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hexc, hpar⟩))
    · intro hS
      rcases Finset.mem_union.mp hS with hreg | hexc
      · obtain ⟨hreg, hpar⟩ := Finset.mem_filter.mp hreg
        rcases Finset.mem_union.mp hreg with hα | hβ
        · have hmem : S ∈ all_distinct_partitions n := by
            have htmp : S ∈ all_distinct_partitions n ∧
                alpha_applicable S (nonempty_of_alpha_mem n S hα) := by
              simpa [alpha_partitions, nonempty_of_alpha_mem n S hα] using hα
            exact htmp.1
          simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
          rcases hmem with ⟨hpow, hsum, hpos⟩
          simp only [even_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hpow, hsum, hpos, hpar⟩
        · have hmem : S ∈ all_distinct_partitions n := by
            have htmp : S ∈ all_distinct_partitions n ∧
                beta_applicable S (nonempty_of_beta_mem n S hβ) := by
              simpa [beta_partitions, nonempty_of_beta_mem n S hβ] using hβ
            exact htmp.1
          simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
          rcases hmem with ⟨hpow, hsum, hpos⟩
          simp only [even_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hpow, hsum, hpos, hpar⟩
      · obtain ⟨hexc, hpar⟩ := Finset.mem_filter.mp hexc
        have hmem : S ∈ all_distinct_partitions n := (mem_exceptional_partitions_iff n S).mp hexc |>.1
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
        rcases hmem with ⟨hpow, hsum, hpos⟩
        simp only [even_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hpow, hsum, hpos, hpar⟩
  rw [show p_e n = (even_distinct_partitions n).card by rfl, hunion, Finset.card_union_of_disjoint hdisj]

lemma partition_counts_split_odd (n : ℕ) (hn : 0 < n) :
    p_o n = (regular_odd_partitions n).card + (exceptional_odd_partitions n).card := by
  classical
  have hdisj : Disjoint (regular_odd_partitions n) (exceptional_odd_partitions n) := by
    rw [Finset.disjoint_left]
    intro S hreg hexc
    exact (Finset.disjoint_left.mp (regular_exceptional_disjoint n))
      ((Finset.mem_filter.mp hreg).1) ((Finset.mem_filter.mp hexc).1)
  have hunion :
      odd_distinct_partitions n = (regular_odd_partitions n) ∪ (exceptional_odd_partitions n) := by
    ext S
    constructor
    · intro hS
      simp only [odd_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨hpow, hsum, hpos, hpar⟩ := hS
      have hmem : S ∈ all_distinct_partitions n := by
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hpow, hsum, hpos⟩
      rcases mem_regular_or_exceptional_of_mem_all_distinct n hn S hmem with hreg | hexc
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hreg, hpar⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hexc, hpar⟩))
    · intro hS
      rcases Finset.mem_union.mp hS with hreg | hexc
      · obtain ⟨hreg, hpar⟩ := Finset.mem_filter.mp hreg
        rcases Finset.mem_union.mp hreg with hα | hβ
        · have hmem : S ∈ all_distinct_partitions n := by
            have htmp : S ∈ all_distinct_partitions n ∧
                alpha_applicable S (nonempty_of_alpha_mem n S hα) := by
              simpa [alpha_partitions, nonempty_of_alpha_mem n S hα] using hα
            exact htmp.1
          simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
          rcases hmem with ⟨hpow, hsum, hpos⟩
          simp only [odd_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hpow, hsum, hpos, hpar⟩
        · have hmem : S ∈ all_distinct_partitions n := by
            have htmp : S ∈ all_distinct_partitions n ∧
                beta_applicable S (nonempty_of_beta_mem n S hβ) := by
              simpa [beta_partitions, nonempty_of_beta_mem n S hβ] using hβ
            exact htmp.1
          simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
          rcases hmem with ⟨hpow, hsum, hpos⟩
          simp only [odd_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hpow, hsum, hpos, hpar⟩
      · obtain ⟨hexc, hpar⟩ := Finset.mem_filter.mp hexc
        have hmem : S ∈ all_distinct_partitions n := (mem_exceptional_partitions_iff n S).mp hexc |>.1
        simp only [all_distinct_partitions, Finset.mem_filter, Finset.mem_powerset] at hmem
        rcases hmem with ⟨hpow, hsum, hpos⟩
        simp only [odd_distinct_partitions, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hpow, hsum, hpos, hpar⟩
  rw [show p_o n = (odd_distinct_partitions n).card by rfl, hunion, Finset.card_union_of_disjoint hdisj]

lemma count_difference_eq_exceptional_difference (n : ℕ) (hn : 0 < n) :
    (p_e n : ℤ) - (p_o n : ℤ) =
      ((exceptional_even_partitions n).card : ℤ) -
      ((exceptional_odd_partitions n).card : ℤ) := by
  rw [partition_counts_split_even n hn, partition_counts_split_odd n hn]
  have hreg : ((regular_even_partitions n).card : ℤ) = ((regular_odd_partitions n).card : ℤ) := by
    exact_mod_cast regular_even_card_eq_regular_odd_card n hn
  omega

lemma exceptional_partition_implies_generalized_pentagonal
    (n : ℕ) (S : Finset ℕ) (hS : S ∈ exceptional_partitions n) :
    IsGeneralizedPentagonal n := by
  rw [mem_exceptional_partitions_iff] at hS
  rcases hS with ⟨hmem, hne, hα, hβ⟩
  exact n_eq_generalized_pentagonal_of_neither_applicable n S hmem hne ⟨hα, hβ⟩

lemma generalized_pentagonal_has_exceptional_partition
    (n : ℕ) (hn : 0 < n) (h : IsGeneralizedPentagonal n) :
    ∃ S, S ∈ exceptional_partitions n := by
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      subst hk0
      simpa using hn
    exact ⟨minusExceptional k, minusExceptional_mem_exceptional _ _ hk rfl⟩
  · have hk : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      subst hk0
      simpa using hn
    exact ⟨plusExceptional k, plusExceptional_mem_exceptional _ _ hk rfl⟩

lemma exceptional_partitions_card_le_one (n : ℕ) :
    (exceptional_partitions n).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro A B hA hB
  have hsumA : A.sum id = n := by
    exact sum_eq_of_mem_all_distinct ((mem_exceptional_partitions_iff n A).mp hA).1
  have hsumB : B.sum id = n := by
    exact sum_eq_of_mem_all_distinct ((mem_exceptional_partitions_iff n B).mp hB).1
  rcases exceptional_eq_minus_or_plus n A hA with ⟨k, hk, rfl | rfl⟩
  · rcases exceptional_eq_minus_or_plus n B hB with ⟨l, hl, rfl | rfl⟩
    · have hsum_eq :
          (minusExceptional k).sum id = (minusExceptional l).sum id := by
        rw [hsumA, hsumB]
      have hkl : k = l := minusExceptional_sum_strictMono.injective hsum_eq
      simp [hkl]
    · have hsum_eq :
          (minusExceptional k).sum id = (plusExceptional l).sum id := by
        rw [hsumA, hsumB]
      rcases lt_trichotomy k l with hkl | rfl | hlk
      · have hle : (minusExceptional l).sum id ≤ (plusExceptional l).sum id := by
          rw [plusExceptional_sum_eq_minusExceptional_sum_add]
          omega
        have hlt : (minusExceptional k).sum id < (plusExceptional l).sum id :=
          lt_of_lt_of_le (minusExceptional_sum_strictMono hkl) hle
        exfalso
        exact (ne_of_lt hlt) hsum_eq
      · exfalso
        exact (ne_of_lt (minusExceptional_sum_lt_plusExceptional_sum hl)) hsum_eq
      · have hlt : (plusExceptional l).sum id < (minusExceptional k).sum id := by
          have hlt' := plusExceptional_sum_lt_minusExceptional_sum_succ l
          have hle :
              (minusExceptional (l + 1)).sum id ≤ (minusExceptional k).sum id := by
            exact minusExceptional_sum_strictMono.monotone (by omega)
          exact lt_of_lt_of_le hlt' hle
        exfalso
        exact (ne_of_gt hlt) hsum_eq
  · rcases exceptional_eq_minus_or_plus n B hB with ⟨l, hl, rfl | rfl⟩
    · have hsum_eq :
          (plusExceptional k).sum id = (minusExceptional l).sum id := by
        rw [hsumA, hsumB]
      rcases lt_trichotomy k l with hkl | rfl | hlk
      · have hlt : (plusExceptional k).sum id < (minusExceptional l).sum id := by
          have hlt' := plusExceptional_sum_lt_minusExceptional_sum_succ k
          have hle :
              (minusExceptional (k + 1)).sum id ≤ (minusExceptional l).sum id := by
            exact minusExceptional_sum_strictMono.monotone (by omega)
          exact lt_of_lt_of_le hlt' hle
        exfalso
        exact (ne_of_lt hlt) hsum_eq
      · exfalso
        exact (ne_of_gt (minusExceptional_sum_lt_plusExceptional_sum hk)) hsum_eq
      · have hlt : (minusExceptional l).sum id < (plusExceptional k).sum id := by
          have hle : (minusExceptional l).sum id ≤ (plusExceptional l).sum id := by
            rw [plusExceptional_sum_eq_minusExceptional_sum_add]
            omega
          exact lt_of_le_of_lt hle (plusExceptional_sum_strictMono hlk)
        exfalso
        exact (ne_of_gt hlt) hsum_eq
    · have hsum_eq :
          (plusExceptional k).sum id = (plusExceptional l).sum id := by
        rw [hsumA, hsumB]
      have hkl : k = l := plusExceptional_sum_strictMono.injective hsum_eq
      simp [hkl]

lemma neg_one_pow_nat_even (k : ℕ) (hk : k % 2 = 0) : (-1 : ℤ) ^ k = 1 := by
  rw [show k = 2 * (k / 2) by omega, pow_mul]
  simp

lemma neg_one_pow_nat_odd (k : ℕ) (hk : k % 2 = 1) : (-1 : ℤ) ^ k = -1 := by
  rw [show k = 2 * (k / 2) + 1 by omega, pow_add, pow_mul]
  simp

lemma exceptional_contribution_eq_pentagonalCoeff (n : ℕ) (hn : 0 < n) :
    ((exceptional_even_partitions n).card : ℤ) -
      ((exceptional_odd_partitions n).card : ℤ) = pentagonalCoeff n := by
  classical
  by_cases h₁ : ∃ k : ℕ, n = k * (3 * k - 1) / 2
  · set k := Classical.choose h₁
    have hk_spec : n = k * (3 * k - 1) / 2 := by
      simpa [k] using Classical.choose_spec h₁
    have hk_pos : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      rw [hk0] at hk_spec
      simp at hk_spec
      omega
    have hExc : minusExceptional k ∈ exceptional_partitions n := by
      simpa [k] using minusExceptional_mem_exceptional n k hk_pos hk_spec
    have huniq : exceptional_partitions n = {minusExceptional k} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hExc, ?_⟩
      intro T hT
      exact (Finset.card_le_one_iff.mp (exceptional_partitions_card_le_one n)) hT hExc
    by_cases hk_even : k % 2 = 0
    · have hEven : exceptional_even_partitions n = {minusExceptional k} := by
        rw [exceptional_even_partitions, huniq]
        simp [minusExceptional_card, hk_even]
      have hOdd : exceptional_odd_partitions n = ∅ := by
        rw [exceptional_odd_partitions, huniq]
        simp [minusExceptional_card, hk_even]
      calc
        ((exceptional_even_partitions n).card : ℤ) - ((exceptional_odd_partitions n).card : ℤ)
            = 1 := by rw [hEven, hOdd]; simp
        _ = (-1 : ℤ) ^ k := by symm; exact neg_one_pow_nat_even k hk_even
        _ = pentagonalCoeff n := by simp [pentagonalCoeff, h₁, k]
    · have hk_odd : k % 2 = 1 := by omega
      have hEven : exceptional_even_partitions n = ∅ := by
        rw [exceptional_even_partitions, huniq]
        simp [minusExceptional_card, hk_odd]
      have hOdd : exceptional_odd_partitions n = {minusExceptional k} := by
        rw [exceptional_odd_partitions, huniq]
        simp [minusExceptional_card, hk_odd]
      calc
        ((exceptional_even_partitions n).card : ℤ) - ((exceptional_odd_partitions n).card : ℤ)
            = -1 := by rw [hEven, hOdd]; simp
        _ = (-1 : ℤ) ^ k := by symm; exact neg_one_pow_nat_odd k hk_odd
        _ = pentagonalCoeff n := by simp [pentagonalCoeff, h₁, k]
  · by_cases h₂ : ∃ k : ℕ, n = k * (3 * k + 1) / 2
    · set k := Classical.choose h₂
      have hk_spec : n = k * (3 * k + 1) / 2 := by
        simpa [k] using Classical.choose_spec h₂
      have hk_pos : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        rw [hk0] at hk_spec
        simp at hk_spec
        omega
      have hExc : plusExceptional k ∈ exceptional_partitions n := by
        simpa [k] using plusExceptional_mem_exceptional n k hk_pos hk_spec
      have huniq : exceptional_partitions n = {plusExceptional k} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hExc, ?_⟩
        intro T hT
        exact (Finset.card_le_one_iff.mp (exceptional_partitions_card_le_one n)) hT hExc
      by_cases hk_even : k % 2 = 0
      · have hEven : exceptional_even_partitions n = {plusExceptional k} := by
          rw [exceptional_even_partitions, huniq]
          simp [plusExceptional_card, hk_even]
        have hOdd : exceptional_odd_partitions n = ∅ := by
          rw [exceptional_odd_partitions, huniq]
          simp [plusExceptional_card, hk_even]
        calc
          ((exceptional_even_partitions n).card : ℤ) - ((exceptional_odd_partitions n).card : ℤ)
              = 1 := by rw [hEven, hOdd]; simp
          _ = (-1 : ℤ) ^ k := by symm; exact neg_one_pow_nat_even k hk_even
          _ = pentagonalCoeff n := by simp [pentagonalCoeff, h₁, h₂, k]
      · have hk_odd : k % 2 = 1 := by omega
        have hEven : exceptional_even_partitions n = ∅ := by
          rw [exceptional_even_partitions, huniq]
          simp [plusExceptional_card, hk_odd]
        have hOdd : exceptional_odd_partitions n = {plusExceptional k} := by
          rw [exceptional_odd_partitions, huniq]
          simp [plusExceptional_card, hk_odd]
        calc
          ((exceptional_even_partitions n).card : ℤ) - ((exceptional_odd_partitions n).card : ℤ)
              = -1 := by rw [hEven, hOdd]; simp
          _ = (-1 : ℤ) ^ k := by symm; exact neg_one_pow_nat_odd k hk_odd
          _ = pentagonalCoeff n := by simp [pentagonalCoeff, h₁, h₂, k]
    · have hExcEmpty : exceptional_partitions n = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro S hS
        have hgp : IsGeneralizedPentagonal n := exceptional_partition_implies_generalized_pentagonal n S hS
        rcases hgp with hgp | hgp
        · exact h₁ hgp
        · exact h₂ hgp
      rw [exceptional_even_partitions, hExcEmpty, exceptional_odd_partitions, hExcEmpty]
      simp [pentagonalCoeff, h₁, h₂]

/-- Euler’s pentagonal number theorem. -/
theorem euler_pentagonal_number_theorem (n : ℕ) :
  (p_e n : ℤ) - (p_o n : ℤ) = pentagonalCoeff n := by
  by_cases hn : n = 0
  · subst n
    have h0 : ∃ k : ℕ, 0 = k * (3 * k - 1) / 2 := ⟨0, by simp⟩
    have hchoose : Classical.choose h0 = 0 := by
      rcases hchoosek : Classical.choose h0 with _ | k
      · simp
      · have hspec : 0 = Nat.succ k * (3 * Nat.succ k - 1) / 2 := by
          simpa [hchoosek] using Classical.choose_spec h0
        have hpos : 0 < Nat.succ k * (3 * Nat.succ k - 1) / 2 := by
          apply Nat.div_pos
          · have hfac : 2 ≤ 3 * Nat.succ k - 1 := by omega
            calc
              2 ≤ 3 * Nat.succ k - 1 := hfac
              _ ≤ 1 * (3 * Nat.succ k - 1) := by simp
              _ ≤ Nat.succ k * (3 * Nat.succ k - 1) := by
                simpa using Nat.mul_le_mul_right (3 * Nat.succ k - 1) (by simp : 1 ≤ Nat.succ k)
          · omega
        rw [← hspec] at hpos
        exact (Nat.lt_irrefl 0 hpos).elim
    have hcount : (p_e 0 : ℤ) - (p_o 0 : ℤ) = 1 := by
      decide
    simpa [pentagonalCoeff, h0, hchoose] using hcount
  · have hn' : 0 < n := by omega
    calc
      (p_e n : ℤ) - (p_o n : ℤ) =
          ((exceptional_even_partitions n).card : ℤ) -
            ((exceptional_odd_partitions n).card : ℤ) :=
        count_difference_eq_exceptional_difference n hn'
      _ = pentagonalCoeff n := exceptional_contribution_eq_pentagonalCoeff n hn'
