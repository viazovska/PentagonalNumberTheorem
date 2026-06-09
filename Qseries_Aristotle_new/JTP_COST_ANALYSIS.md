# Cost Analysis: Completing the Jacobi Triple Product Identity

## Current State

| Component | Status |
|-----------|--------|
| `qPochhammer`, `qBinom`, finite q-binomial theorem | ✅ Fully proved |
| `qPochhammerInf`, convergence, non-vanishing, telescoping | ✅ Fully proved |
| Cauchy identity (infinite q-binomial theorem) | ✅ Fully proved |
| Euler 1st identity: `1/(z;q)_∞ = Σ zⁿ/(q;q)_n` | ✅ Fully proved |
| Euler 2nd identity: `(-z;q)_∞ = Σ q^C(n,2) zⁿ/(q;q)_n` | ✅ Fully proved |
| Functional equation for product: `f(qz) = f(z)/z` | ✅ Fully proved |
| Functional equation for bilateral series: `g(qz) = g(z)/z` | ✅ Fully proved |
| Bilateral series summability | ✅ Fully proved |
| **Jacobi triple product: `f(z) = g(z)`** | ❌ `sorry` |
| **Pentagonal number theorem (analytic)** | ❌ `sorry` (depends on JTP) |
| PNT in FPS/combinatorial form (Franklin's involution) | ✅ Fully proved in `Lemmas.lean` + `FormalPowerSeries.lean` |

---

## Route A: Current Sketch (Complex Analysis / Liouville)

**Strategy:** Both sides of JTP satisfy the same functional equation `F(qz) = F(z)/z`. Show their ratio is a bounded, q-periodic holomorphic function on ℂ*, hence constant by a Liouville-type argument. Determine the constant is 1.

### What's Missing

1. **Holomorphicity of infinite products** (~300–500 lines)
   - Need to show `∏(1 + aₖ(z))` is holomorphic when `∑ aₖ` converges locally uniformly.
   - Mathlib has `TendstoLocallyUniformlyOn.differentiableOn` (locally uniform limits of holomorphic functions are holomorphic), but connecting this to infinite products requires building the bridge: partial products are polynomials (hence holomorphic), and they converge locally uniformly, so the infinite product is holomorphic.
   - Must handle `(-z;q)_∞` and `(-q/z;q)_∞` separately (the latter has a pole at z = 0).

2. **Laurent expansion of the product** (~200–300 lines)
   - Show `(-z;q)_∞·(-q/z;q)_∞` has a convergent Laurent expansion on the annulus `|q| < |z| < 1`.
   - Alternatively, show `f(z) = (q;q)_∞·(-z;q)_∞·(-q/z;q)_∞` is holomorphic on ℂ\{0} and has a Laurent expansion.
   - The Cauchy product of the two Euler-2 expansions gives the Laurent coefficients, but convergence of the Cauchy product on the annulus needs justification.

3. **Zero analysis** (~100–200 lines)
   - Show `f(z) = 0 iff z = -qⁿ` for some `n ∈ ℤ`.
   - Show `g(z)` has the same zeros (this requires showing the bilateral series vanishes at those points, which follows from the Euler identity but needs formal argument).
   - Show `g/f` extends to a holomorphic function (removable singularities at the zeros).

4. **Boundedness / Liouville argument** (~200–400 lines)
   - Show the ratio `g/f` is bounded on a fundamental annulus `{|q| ≤ |z| ≤ 1}`.
   - Use q-periodicity to extend boundedness to all of ℂ*.
   - Apply a Liouville-type theorem. Mathlib has `Differentiable.apply_eq_apply_of_bounded` for bounded entire functions, but we need a variant for ℂ* (or map to ℂ via logarithm, making it doubly periodic).
   - This likely requires developing a small theory of q-periodic meromorphic functions.

5. **Normalization** (~50–100 lines)
   - Once `f = C·g`, determine `C = 1` by evaluating at a specific point or comparing coefficients. Could use Euler's 2nd identity at z → 0.

### Estimated Cost: ~900–1500 new lines

### Difficulty Assessment
- The holomorphicity of infinite products and the Liouville argument are genuinely deep infrastructure that doesn't exist in Mathlib.
- Every step is individually doable but involves significant complex analysis glue.
- Risk: the Liouville argument for q-periodic functions on ℂ* may require more infrastructure than anticipated (e.g., if the existing `Liouville` theorem doesn't easily adapt).

---

## Route B: Via Euler's Pentagonal Number Theorem

**Strategy:** Use the already-formalized PNT (Franklin's involution, combinatorial proof in FPS) to derive JTP. This is the approach in Prodinger's paper.

### Step 1: Bridge FPS ↔ Analytic (~200–350 lines)

The PNT is currently proved in the formal power series world (`ℤ⟦X⟧`):

```
coeff_prod_pentagonal_*: [Xⁿ] ∏_{k=1}^n (1 - Xᵏ) = pentagonal coefficient
```

We need the analytic statement: for `‖q‖ < 1`,

```
(q;q)_∞ = Σₖ (-1)ᵏ q^{ω(k)}
```

The bridge argument:
1. The partial product `P_N(q) = ∏_{k=1}^N (1-qᵏ)` is a polynomial whose coefficient at `qⁿ` equals the pentagonal coefficient `cₙ` for all `n ≤ N`. This follows from the FPS result.
2. The series `Σ cₙ qⁿ` converges absolutely for `‖q‖ < 1` since `|cₙ| ≤ 1`.
3. `|P_N(q) - Σ_{n=0}^N cₙ qⁿ| ≤ ‖q‖^{N+1} · M` where `M = ∏(1+‖q‖ᵏ)` is bounded. (The difference only has terms of degree ≥ N+1, and the sum of absolute values of all polynomial coefficients is bounded by `∏(1+‖q‖ᵏ)`.)
4. `P_N(q) → (q;q)_∞` (from `tendsto_qPochhammer`, already proved).
5. By uniqueness of limits: `(q;q)_∞ = Σ cₙ qⁿ`.

This is moderately involved but self-contained — no complex analysis needed, just estimates on polynomial coefficients and limits.

### Step 2: The Laurent Series / Functional Equation Argument (~300–500 lines)

Once we have PNT in analytic form, derive JTP. The cleanest approach (which I believe is essentially Prodinger's):

1. **Laurent expansion:** Using Euler's 2nd identity (already proved), we have:
   - `(-z;q)_∞ = Σ_{n≥0} q^{C(n,2)} zⁿ/(q;q)_n` for `‖z‖ < 1`
   - `(-q/z;q)_∞ = Σ_{m≥0} q^{C(m+1,2)} z^{-m}/(q;q)_m` for `‖q/z‖ < 1`

   On the annulus `‖q‖ < ‖z‖ < 1`, the product has a convergent Laurent expansion:
   `(-z;q)_∞·(-q/z;q)_∞ = Σ_k c_k z^k`

2. **Functional equation determines coefficients:** The functional equation `f(qz) = f(z)/z` (already proved) forces:
   `c_{k+1} = c_k · qᵏ`, hence `c_k = c₀ · q^{k(k-1)/2}`

   This step is purely algebraic — the functional equation on Laurent series uniquely determines the ratio of consecutive coefficients. (~100 lines to formalize, working with `tsum` and coefficient extraction.)

3. **Normalization via PNT:** We need `(q;q)_∞ · c₀ = 1`. Setting `z = 0` in the product (or rather, comparing the `z⁰` coefficient):

   Actually, there's a cleaner normalization. Consider the specialization `z = q^{1/2}` or evaluate the identity at a specific point. The most elegant route:
   
   - From `f = (q;q)_∞ · c₀ · g`, evaluate at `q → q³, z → q` to get PNT on both sides, and use the already-proved PNT to conclude `(q;q)_∞ · c₀ = 1`.

   Alternatively, compare the constant term directly: `c₀ = Σ_m q^{m²}/((q;q)_m)²`, and show `(q;q)_∞ · Σ_m q^{m²}/((q;q)_m)² = 1`. This itself is a q-series identity that needs proof (~100–200 lines).

### Step 3: Convergence Details (~200–300 lines)

- Absolute convergence of the Cauchy product of two one-sided series on the annulus.
- Justification that the functional equation acts coefficient-wise on the Laurent expansion.
- Summability of the bilateral series (partly done).

### Estimated Cost: ~700–1200 new lines

### Difficulty Assessment
- The FPS-to-analytic bridge (Step 1) is the most novel piece, but conceptually straightforward.
- The Laurent series functional equation argument (Step 2) avoids all the hard complex analysis of Route A.
- The normalization (determining the constant is 1) is the trickiest step. Using PNT for this is elegant but requires showing the specialization `q → q³, z → q` is valid — which is essentially the same index-partitioning argument as PNT-from-JTP, but in reverse.
- Lower risk than Route A: no holomorphicity of infinite products, no Liouville theorem, no removable singularity arguments.

---

## Side-by-Side Comparison

| Aspect | Route A (Complex Analysis) | Route B (Via PNT) |
|--------|---------------------------|-------------------|
| **New lines estimate** | 900–1500 | 700–1200 |
| **Hardest single step** | Liouville for q-periodic functions on ℂ* | Normalization (constant = 1) |
| **Mathlib gaps** | Holomorphicity of infinite products, Liouville on ℂ* | Cauchy product of Laurent series, FPS↔analytic bridge |
| **Complex analysis needed** | Heavy | None (purely algebraic + real analysis) |
| **Risk of unexpected obstacles** | High (complex analysis infrastructure is deep) | Moderate (normalization may need a separate identity) |
| **Reusability** | Infrastructure useful for theta functions, modular forms | Infrastructure useful for other q-identities |
| **What we already have** | Functional equations for both sides | PNT (combinatorial), Euler identities, functional equations |

---

## Recommendation

**Route B is cheaper and lower-risk.** The key advantages:

1. **Avoids complex analysis entirely.** Route A requires holomorphicity of infinite products, a Liouville-type theorem for q-periodic functions, and removable singularity arguments — none of which exist in Mathlib. Route B works with convergent series and algebraic manipulations.

2. **Leverages existing infrastructure.** The combinatorial PNT (`Lemmas.lean`) and the Euler identities (`EulerIdentities.lean`) are both fully proved. Route B uses them directly; Route A doesn't use PNT at all.

3. **Smaller scope.** Route B needs ~700–1200 lines vs ~900–1500 for Route A.

4. **The main technical gap (FPS ↔ analytic bridge) is reusable.** Having a general theorem that transfers formal power series identities to analytic identities for `‖q‖ < 1` would benefit the entire q-series library.

**The main risk with Route B** is the normalization step (showing the constant is 1). The cleanest approach would be:
- Show the coefficient of `z⁰` in `(q;q)_∞(-z;q)_∞(-q/z;q)_∞` is 1, OR
- Use a specialization argument with PNT to fix the constant.

If the normalization proves difficult, it can be approached via the Cauchy identity (which we already have) by a careful algebraic argument.

---

## Concrete Plan for Route B

If you want to proceed with Route B, here is a concrete decomposition into files/lemmas:

### File: `QSeries/FPSBridge.lean` (~200 lines)
- `pentagonal_coeff_bounded`: `|cₙ| ≤ 1` for pentagonal coefficients.
- `pentagonal_series_summable`: `Σ |cₙ| ‖q‖ⁿ < ∞`.
- `polynomial_coeff_bound`: `Σ |[qⁿ] P_N(q)| ≤ ∏(1+‖q‖ᵏ)`.
- `polynomial_tail_vanishes`: `|P_N(q) - Σ_{n≤N} cₙ qⁿ| → 0`.
- `analyticPNT`: `(q;q)_∞ = Σ (-1)ᵏ q^{ω(k)}` for `‖q‖ < 1`.

### File: `QSeries/LaurentProduct.lean` (~300 lines)
- `cauchy_product_summable`: Absolute convergence of the Cauchy product of two Euler-2 series on `‖q‖ < ‖z‖ < 1`.
- `product_laurent_expansion`: `(-z;q)_∞(-q/z;q)_∞ = Σ cₖ zᵏ` on the annulus.
- `functional_eq_determines_coeffs`: If `Σ aₖ zᵏ` satisfies `F(qz) = F(z)/z`, then `aₖ = a₀ q^{k(k-1)/2}`.
- `triple_product_eq_const_times_bilateral`: `f(z) = C · g(z)` for some `C`.

### Modified: `QSeries/JacobiTripleProduct.lean` (~200 lines added)
- `normalization_constant_is_one`: `C = 1` (the hardest step).
- `jacobiTripleProduct`: Main theorem, combining the above.

### Modified: `QSeries/PentagonalNumber.lean` (~60 lines added)
- `eulerPentagonalNumber`: Follows from JTP by substitution `q → q³, z → q`.
