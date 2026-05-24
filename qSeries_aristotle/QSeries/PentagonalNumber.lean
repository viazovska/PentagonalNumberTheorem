import QSeries.JacobiTripleProduct

/-!
# Euler's pentagonal number theorem

**Euler's pentagonal number theorem** states that for $\|q\| < 1$:
$$\prod_{n=1}^{\infty} (1 - q^n) = \sum_{k \in \mathbb{Z}} (-1)^k q^{k(3k-1)/2}$$

This follows from the Jacobi triple product by the substitution
$q \to q^3$, $z \to q$, using the index partition
$\{3n\} \cup \{3n-2\} \cup \{3n-1\} = \mathbb{Z}_{\geq 1}$.

## Main definitions

* `qSeries.pentagonal` — the generalized pentagonal number $\omega(k) = k(3k-1)/2$.

## Main results

* `qSeries.eulerPentagonalNumber` — the pentagonal number theorem.
-/

open Finset Filter
open scoped Topology

namespace qSeries

noncomputable section

/-- The $k$-th generalized pentagonal number $\omega(k) = k(3k-1)/2$,
well-defined for $k \in \mathbb{Z}$ (the product $k(3k-1)$ is always even). -/
def pentagonal (k : ℤ) : ℕ :=
  (k * (3 * k - 1) / 2).toNat

/-
**Euler's pentagonal number theorem** (bilateral form).

For $\|q\| < 1$:
$$(q;q)_\infty = \sum_{k=0}^{\infty} (-1)^k q^{\omega(k)}
  + \sum_{k=0}^{\infty} (-1)^{k+1} q^{\omega(-(k+1))}$$
where $\omega(k) = k(3k-1)/2$ is the generalized pentagonal number.

In expanded form:
$(q;q)_\infty = 1 - q - q^2 + q^5 + q^7 - q^{12} - q^{15} + \cdots$
-/
theorem eulerPentagonalNumber {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf q q =
      (∑' k : ℕ, (-1 : ℂ) ^ k * q ^ pentagonal k)
      + ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) * q ^ pentagonal (-(↑k + 1)) := by
  by_cases hq0 : q = 0;
  · rw [ tsum_eq_single 0, tsum_eq_single 0 ] <;> simp_all +decide [ pentagonal ];
    · grind;
    · exact fun n hn => Int.le_ediv_of_mul_le ( by norm_num ) ( by nlinarith [ show ( n : ℤ ) > 0 from Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hn ) ] );
  · -- Use the full Jacobi triple product (valid on the whole punctured disc);
    -- with `z = -q` we only need `‖-q‖ < 1` and `-q ≠ 0`, not the annulus bound.
    have hJTP := jacobiTripleProduct (q := q ^ 3) (z := -q)
        ( show ‖q ^ 3‖ < 1 from by simpa using pow_lt_one₀ ( norm_nonneg q ) hq ( by norm_num ) )
        ( by simpa using hq ) ( neg_ne_zero.mpr hq0 )
    unfold jacobiProd jacobiBilateral jacobiBilateralPos jacobiBilateralNeg at hJTP
    convert hJTP using 1
    · norm_num [ pow_succ, mul_assoc, hq0 ];
      -- By definition of $qPochhammerInf$, we can write
      have h_def : qPochhammerInf q q = ∏' k : ℕ, (1 - q ^ (k + 1)) := by
        exact tprod_congr fun k => by ring;
      -- We can split the product into three separate products, one for each residue class modulo 3.
      have h_split : ∏' k : ℕ, (1 - q ^ (k + 1)) = (∏' k : ℕ, (1 - q ^ (3 * k + 1))) * (∏' k : ℕ, (1 - q ^ (3 * k + 2))) * (∏' k : ℕ, (1 - q ^ (3 * k + 3))) := by
        have h_split : ∀ {f : ℕ → ℂ}, Summable (fun k => ‖f k‖) → (∏' k : ℕ, (1 + f k)) = (∏' k : ℕ, (1 + f (3 * k))) * (∏' k : ℕ, (1 + f (3 * k + 1))) * (∏' k : ℕ, (1 + f (3 * k + 2))) := by
          intros f hf_summable
          have h_split : ∏' k : ℕ, (1 + f k) = (∏' k : ℕ, (1 + f (3 * k))) * (∏' k : ℕ, (1 + f (3 * k + 1))) * (∏' k : ℕ, (1 + f (3 * k + 2))) := by
            have h_split : ∀ {g : ℕ → ℂ}, Summable (fun k => ‖g k‖) → (∏' k : ℕ, (1 + g k)) = (∏' k : ℕ, (1 + g (3 * k))) * (∏' k : ℕ, (1 + g (3 * k + 1))) * (∏' k : ℕ, (1 + g (3 * k + 2))) := by
              intros g hg_summable
              have h_split : ∀ n : ℕ, ∏ k ∈ Finset.range (3 * n), (1 + g k) = (∏ k ∈ Finset.range n, (1 + g (3 * k))) * (∏ k ∈ Finset.range n, (1 + g (3 * k + 1))) * (∏ k ∈ Finset.range n, (1 + g (3 * k + 2))) := by
                intro n; induction n <;> simp_all +decide [ Nat.mul_succ, Finset.prod_range_succ ] ; ring;
              have h_split : Filter.Tendsto (fun n => ∏ k ∈ Finset.range (3 * n), (1 + g k)) Filter.atTop (nhds (∏' k : ℕ, (1 + g k))) := by
                have h_split : Multipliable (fun k => 1 + g k) := by
                  refine' multipliable_one_add_of_summable _;
                  exact hg_summable;
                convert h_split.hasProd.tendsto_prod_nat.comp ( Filter.tendsto_id.nsmul_atTop three_pos ) using 1;
              have h_split : Filter.Tendsto (fun n => (∏ k ∈ Finset.range n, (1 + g (3 * k))) * (∏ k ∈ Finset.range n, (1 + g (3 * k + 1))) * (∏ k ∈ Finset.range n, (1 + g (3 * k + 2)))) Filter.atTop (nhds ((∏' k : ℕ, (1 + g (3 * k))) * (∏' k : ℕ, (1 + g (3 * k + 1))) * (∏' k : ℕ, (1 + g (3 * k + 2)))) ) := by
                have h_split : ∀ {h : ℕ → ℂ}, Summable (fun k => ‖h k‖) → Filter.Tendsto (fun n => ∏ k ∈ Finset.range n, (1 + h k)) Filter.atTop (nhds (∏' k : ℕ, (1 + h k))) := by
                  intro h hh_summable;
                  have h_split : Multipliable (fun k => 1 + h k) := by
                    refine' multipliable_one_add_of_summable _;
                    exact hh_summable;
                  convert h_split.hasProd.tendsto_prod_nat using 1;
                exact Filter.Tendsto.mul ( Filter.Tendsto.mul ( h_split <| hg_summable.comp_injective <| by intros a b; aesop ) ( h_split <| hg_summable.comp_injective <| by intros a b; aesop ) ) ( h_split <| hg_summable.comp_injective <| by intros a b; aesop );
              exact tendsto_nhds_unique ‹_› ( by simp only [*] )
            exact h_split hf_summable;
          exact h_split;
        convert h_split _ using 1;
        rotate_left;
        rotate_left;
        use fun k => -q ^ ( k + 1 );
        · simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one ( by positivity ) hq;
        · exact tprod_congr fun _ => by ring;
        · norm_cast;
      rw [ h_def, h_split ];
      unfold qPochhammerInf; ring;
    · congr! 1;
      · refine' tsum_congr fun k => _;
        unfold pentagonal; ring;
        rw [ show ( -k + k ^ 2 * 3 : ℤ ) / 2 = k + k.choose 2 * 3 by
              rw [ Int.ediv_eq_of_eq_mul_left ] <;> norm_num;
              exact Nat.recOn k ( by norm_num ) fun n ih => by norm_num [ Nat.choose ] at * ; linarith; ] ; norm_cast ; ring;
      · refine' tsum_congr fun m => _;
        rw [ show pentagonal ( - ( m + 1 ) : ℤ ) = ( m + 2 ).choose 2 * 3 - ( m + 1 ) by
              unfold pentagonal;
              rw [ Nat.choose_two_right ];
              ring;
              norm_cast;
              exact eq_tsub_of_add_eq ( by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ 2 + m ), Nat.div_mul_cancel ( show 2 ∣ 4 + m * 7 + m ^ 2 * 3 from even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ), Nat.div_mul_cancel ( show 2 ∣ m * ( 2 + m - 1 ) + ( 2 + m - 1 ) * 2 from even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) ) ] ) ];
        rw [ show ( m + 2 ).choose 2 * 3 - ( m + 1 ) = ( m + 2 ).choose 2 * 3 - ( m + 1 ) from rfl, pow_sub₀ ] <;> norm_num ; ring;
        · assumption;
        · grind +suggestions;

end

end qSeries