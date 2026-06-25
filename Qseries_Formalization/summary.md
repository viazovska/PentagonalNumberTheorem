# Qseries_Formalization — Summary

Lean 4 / Mathlib formalization of the **Jacobi Triple Product identity** and
**Euler's Pentagonal Number Theorem** via q-series. Two parallel proof routes are
developed: an **algebraic/FPS route** working over any commutative ring, and an
**analytic route** working over ℂ. All files build with zero sorries.

14 source files, 3489 lines (excluding the root import file).

---

## Proof routes

### Algebraic / FPS route

Proves `jacobiTripleProduct_fps : jtpProd = jtpSeries` in `A⟦X⟧` where
`A = ℂ[z, z⁻¹]` (Laurent polynomials). Works over any commutative ring with the
discrete topology. Strategy: coefficient stabilization via the finite q-binomial
theorem → Euler second identity as FPS → key identity `S_k = (q;q)_∞⁻¹` →
Cauchy product diagonal decomposition.

### Analytic route

Proves `jacobiTripleProduct_analytic` for all `‖q‖ < 1`, `z ≠ 0` over ℂ.
Strategy: Euler second identity → functional equation `g(qz) = g(z)/z` →
iteration to reduce to the unit disk → locally uniform convergence on `{z ≠ 0}`.
The pentagonal number theorem follows as a corollary at `z = -1`.

---

## Files

### `Defs.lean` (163 lines)

Definitions shared by both routes:

| Name | Description |
|---|---|
| `qPochhammer a q n` | Finite q-Pochhammer symbol `(a; q)_n = ∏_{i<n}(1 − a·qⁱ)` over any `CommRing` |
| `qBinom n k q` | Gaussian binomial coefficient `[n choose k]_q` over any `CommRing` |
| `qBinom_succ_succ` | Pascal recurrence for `qBinom` |
| `qBinom_mul_qPochhammer_mul_qPochhammer` | `[n choose k]_q · (q;q)_k · (q;q)_{n-k} = (q;q)_n` |

### `FiniteBinomial.lean` (87 lines)

| Name | Description |
|---|---|
| `qBinom_finite_thm` | Finite q-binomial theorem: `∏_{i<n}(1 + z·qⁱ) = ∑_{k≤n} [n choose k]_q · z^k` over any `CommRing` |

### `InfPochhammer.lean` (142 lines)

Analytic infinite q-Pochhammer over ℂ:

| Name | Description |
|---|---|
| `qPochhammerInf a q` | Infinite product `∏_{k≥0}(1 − a·qᵏ)` over ℂ |
| `multipliable_one_sub_smul_qpow` | Multipliability for `‖q‖ < 1` |
| `qPochhammerInf_ne_zero_of_factors` | Non-vanishing when all factors are non-zero |
| `tendsto_qPochhammer` | `(a;q)_n → (a;q)_∞` as `n → ∞` |
| `qPochhammerInf_recursion` | `(z;q)_∞ = (1−z)·(qz;q)_∞` |

### `EulerIdentities.lean` (156 lines)

| Name | Description |
|---|---|
| `euler_first_identity` | `(z;q)_∞ · ∑_{n≥0} zⁿ/(q;q)_n = 1` for `‖q‖,‖z‖ < 1` |
| `euler_second_identity` | `(-z;q)_∞ = ∑_{n≥0} q^{C(n,2)} zⁿ/(q;q)_n` for `‖q‖,‖z‖ < 1` |

### `CauchyIdentity.lean` (401 lines)

Proves Cauchy's q-binomial theorem analytically over ℂ via the functional equation approach:

| Name | Description |
|---|---|
| `cauchyCoeff a q n` | Coefficient in Cauchy's series |
| `cauchy_functional_eq_G`, `cauchy_functional_eq_F` | Functional equations relating `G(a,z)` and `F(a,z)` |
| `qBinom_infinite_thm` | Cauchy's theorem: `∑_{k≥0} [∞ choose k]_q z^k = 1/(z;q)_∞` for `‖z‖,‖q‖ < 1` |

### `FPS.lean` (229 lines)

FPS q-Pochhammer infrastructure over any commutative ring `R`:

| Name | Description |
|---|---|
| `qPoch a n` | Finite q-Pochhammer in `R⟦X⟧`: `∏_{i<n}(1 − a·Xⁱ·a)` |
| `coeff_qPoch_stable` | Coefficient `d < n` stabilizes: `coeff d (qPoch a n) = coeff d (qPoch a (n+1))` |
| `multipliable_qPoch` | The sequence `qPoch a n` is multipliable in `R⟦X⟧` |
| `qPochInf a` | Infinite q-Pochhammer `(a;X)_∞` in `R⟦X⟧` |
| `qPochInf_recursion` | `(a;X)_∞ = (1−a)·(aX;X)_∞` |
| `isUnit_qPochInf` | `(a;X)_∞` is a unit when `1 − coeff 0 a` is a unit |
| `z`, `zinv` | `PS(T(1))` and `PS(T(-1))` in `A⟦X⟧` (images of Laurent monomials) |
| `jtpProd` | `(X;X)_∞ · (-z;X)_∞ · (-X·z⁻¹;X)_∞` in `A⟦X⟧` |
| `jtpSeries` | `∑_{k∈ℤ} z^k · X^{k(k-1)/2}` in `A⟦X⟧` |

### `FPS_Euler.lean` (65 lines)

Helper lemmas connecting `qPoch X n` to `qPochInf`:

| Name | Description |
|---|---|
| `isUnit_qPoch_X` | `qPoch X n` is a unit in `R⟦X⟧` |
| `qPochInf_eq_qPoch_mul` | `(a;X)_∞ = qPoch a n · (aXⁿ;X)_∞` |
| `qqInf_eq_qPoch_mul` | `(X;X)_∞ = qPoch X n · (Xⁿ⁺¹;X)_∞` |

### `FPS_Algebra.lean` (870 lines)

The algebraic heart of the FPS proof:

| Name | Description |
|---|---|
| `qPochInv k` | Inverse of `qPoch X k` in `R⟦X⟧` (via `invOfUnit`) |
| `qqInv` | Inverse of `qPochInf X` in `R⟦X⟧` |
| `qqInf_mul_qPochInv n` | Telescoping: `(X;X)_∞ · qPochInv n = (Xⁿ⁺¹;X)_∞` |
| `coeff_qBinom_eq_qPochInv` | `qBinom(n,k,X)` agrees with `qPochInv k` at coefficients `j` with `j+k ≤ n` |
| `fps_euler_second` | Euler's second identity as FPS over any `CommRing`: `(−a;X)_∞ = ∑_k X^{C(k,2)} aᵏ (qPochInv k)` |
| `S_fps k` | The key sum `∑_m X^{C(m,2)} · (qPochInv k)` shifted by `k` |
| `S_fps_recurrence` | `S_k − S_{k+1} = X^{k+1}(S_{k+2} − S_{k+1})` |
| `fps_key_identity` | `S_fps k = qqInv` for all `k` (coefficient stabilization) |
| `cauchy_coeff_nonneg`, `cauchy_coeff_neg` | Cauchy product diagonal coefficients |
| `jacobiTripleProduct_fps` | **Main result**: `jtpProd = jtpSeries` in `A⟦X⟧` |

### `JTP_Core.lean` (165 lines)

Analytic setup for the JTP proof:

| Name | Description |
|---|---|
| `qPochhammerInf_prod_hasSum` | `(q;q)_∞ · (-z;q)_∞ = ∑_n q^{C(n,2)} zⁿ (q^{n+1};q)_∞` for `‖z‖ < 1` |
| `jacobiTripleProduct_zero` | JTP at `‖z‖ < 1`, `z ≠ 0` (initial case) |
| `euler_second_at_qoz` | Euler second at `q/z` for `‖q‖ < ‖z‖` |
| `jacobiTripleProduct_annulus` | JTP for `‖q‖ < ‖z‖ < 1` |

### `JTP_KeyIdentity.lean` (325 lines)

Analytic analogue of `fps_key_identity`:

| Name | Description |
|---|---|
| `S_sum q k` | The analytic key sum `∑_m q^{C(m,2)} z^m / (q;q)_m` (at `z = q^k`) |
| `S_sum_recurrence` | Recurrence for `S_sum` |
| `S_sum_eq` | `S_sum q k = 1/(q;q)_∞` for all `k` |
| `cauchy_coeff_nonneg`, `cauchy_coeff_neg` | Cauchy product diagonal coefficients over ℂ |

### `JTP_Helpers.lean` (52 lines)

| Name | Description |
|---|---|
| `fe_propagates_forward` | Functional equation propagates: `f(qⁿz) = f(z)/zⁿ · q^{-C(n,2)}` |
| `jtp_annulus_to_disk` | Extends JTP from annulus to disk by continuity |

### `JacobiTripleProduct.lean` (281 lines)

| Name | Description |
|---|---|
| `jacobiProd q z` | Product side `(q;q)_∞ · (-z;q)_∞ · (-q/z;q)_∞` |
| `jacobiBilateral q z` | Series side `∑_{k∈ℤ} z^k q^{k(k-1)/2}` |
| `jacobiProd_fe` | Functional equation for the product side |
| `jacobiBilateral_fe` | Functional equation for the series side |
| `euler_second_identity_all` | Euler second identity for all `z` (not just `‖z‖ < 1`) |
| `jacobiTripleProduct` | JTP for `‖q‖ < 1`, `‖z‖ < 1`, `z ≠ 0` |

### `JTP_Analytic.lean` (423 lines)

Extension to the full domain and locally uniform convergence:

| Name | Description |
|---|---|
| `summable_jacobi_nonneg_all` | Bilateral series converges for all `z` when `‖q‖ < 1` |
| `jacobiBilateral_tendstoLocallyUniformlyOn` | Series side converges locally uniformly on `{z ≠ 0}` |
| `jacobiProd_tendstoLocallyUniformlyOn` | Product side converges locally uniformly on `{z ≠ 0}` |
| `jacobiProd_iterate`, `jacobiBilateral_iterate` | Functional equation iterated `N` times |
| `jacobiTripleProduct_analytic` | **Main result**: JTP for all `‖q‖ < 1`, `z ≠ 0` |

### `PentagonalNumber.lean` (116 lines)

| Name | Description |
|---|---|
| `pentagonal k` | Generalized pentagonal number `k(3k−1)/2` for `k : ℤ` |
| `eulerPentagonalNumber` | **Main result**: `∏_{k≥1}(1−q^k) = ∑_{k∈ℤ} (−1)^k q^{pentagonal k}` for `‖q‖ < 1` |
