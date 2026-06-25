# Review brief — Euler's Pentagonal Number Theorem (Lean 4)

*Prepared 2026-06-17 for a senior expert in q-series and combinatorics. Self-contained: no repository access required.*

---

## 1. Goal

We aim to produce a complete, sorry-free Lean 4 formalization of **Euler's Pentagonal Number Theorem**:
$$
\prod_{n=1}^{\infty}(1 - q^n) \;=\; \sum_{k \in \mathbb{Z}} (-1)^k \, q^{k(3k-1)/2}.
$$

The project pursues this via **two independent routes** that are now both fully proved:
- **Route I** (Franklin): a purely combinatorial/bijective proof via Franklin's involution.
- **Route II** (JTP): a q-series proof via the Jacobi Triple Product identity.

The project also includes a third purely algebraic version — a formal power series (FPS) proof of the Jacobi Triple Product over the ring of Laurent polynomials, without any analytic hypotheses.

---

## 2. Background and references

### 2.1 Setting

Throughout, $q$ is a formal variable or a complex number with $|q| < 1$ depending on context. All formal power series live in $\mathbb{Z}\llbracket X \rrbracket$ or $\mathbb{C}\llbracket X \rrbracket$ (power series with the $X$-adic topology), and analytic results are in $\mathbb{C}$. The generalized pentagonal numbers are
$$
\omega(k) := \frac{k(3k-1)}{2}, \quad k \in \mathbb{Z},
$$
taking values $0, 1, 2, 5, 7, 12, 15, 22, 26, \ldots$ for $k = 0, 1, -1, 2, -2, 3, -3, \ldots$ The theorem says the infinite product $\prod_{n\geq 1}(1-q^n)$ has coefficients $0, \pm 1$ depending on whether the index is a generalized pentagonal number.

We work with **partitions of $n$ into distinct positive parts**, represented as subsets $S \subseteq \{1, \ldots, n\}$ with $\sum_{s \in S} s = n$. A partition $S$ is *even* if $|S| \equiv 0 \pmod 2$ and *odd* otherwise. The counts are $p_e(n) := |\mathcal{P}_{\mathrm{even}}(n)|$ and $p_o(n) := |\mathcal{P}_{\mathrm{odd}}(n)|$.

### 2.2 References

[Andrews 1998] George E. Andrews. *The Theory of Partitions*. Cambridge University Press, 1998.

[Hardy–Wright 2008] G. H. Hardy and E. M. Wright. *An Introduction to the Theory of Numbers*, 6th ed. Oxford University Press, 2008.

[JC–PM–MV 2026] Jonathan Conrad, Paula Mürmann, Maryna Viazovska. "Pentagonal Number Theorem" (internal manuscript, 2026). Primary source for the Franklin involution formalization.

[Gasper–Rahman 2004] George Gasper and Mizan Rahman. *Basic Hypergeometric Series*, 2nd ed. Cambridge University Press, 2004.

### 2.3 State of the art

Euler's pentagonal number theorem is classical (1748). Franklin's bijective proof dates to 1881 (F. Franklin, *Amer. J. Math.* 1881, pp. 390–392). The Jacobi Triple Product route is classical q-series. No Lean 4 formalization of either proof was previously in Mathlib.

---

## 3. Strategy

**Route I (Franklin involution).** We decompose $\mathcal{P}(n)$ into three disjoint classes $\mathcal{P}_\alpha(n)$, $\mathcal{P}_\beta(n)$, and $\mathcal{P}_\mathrm{special}(n)$. A pair of operations $\alpha : \mathcal{P}_\alpha \to \mathcal{P}_\beta$ and $\beta : \mathcal{P}_\beta \to \mathcal{P}_\alpha$ (Franklin's involution) forms a bijection that flips parity (changes the number of parts by exactly 1). Since the $\alpha$- and $\beta$-parts cancel in $p_e(n) - p_o(n)$, the net contribution is $|\mathcal{P}_\mathrm{special}(n)|_{\pm}$, the signed count of special partitions. The special partitions are characterized: they are empty unless $n$ is a generalized pentagonal number, in which case there is exactly one. By connecting coefficients of the finite product $\prod_{k=1}^n (1-X^k)$ to the signed partition count, we recover the full coefficient pattern of Euler's PNT.

**Route II (JTP).** We build up a q-series library: the infinite q-Pochhammer symbol $(a;q)_\infty$, the Cauchy identity (infinite q-binomial theorem), and Euler's first and second identities. From these we prove the Jacobi Triple Product
$$
(q;q)_\infty (-z;q)_\infty (-q/z;q)_\infty = \sum_{k \in \mathbb{Z}} z^k q^{k(k-1)/2}
$$
and deduce Euler's PNT by the substitution $q \mapsto q^3$, $z \mapsto -q$.

**FPS variant.** Route II is also implemented algebraically as an equality of formal power series in $A\llbracket X \rrbracket$ where $A = \mathbb{C}[z, z^{-1}]$ and $X$ plays the role of $q$. This version requires no convergence hypotheses.

---

## 4. Definitions

**Definition 4.1** (Distinct partitions). Let $n \in \mathbb{N}$. The set of *partitions of $n$ into distinct positive parts* is
$$
\mathcal{P}(n) := \bigl\{ S \subseteq \{1, \ldots, n\} \;\big|\; {\textstyle\sum_{s \in S}} s = n \bigr\}.
$$
Subsets $\mathcal{P}_\mathrm{even}(n)$ and $\mathcal{P}_\mathrm{odd}(n)$ are those with $|S|$ even (resp. odd), and $p_e(n) := |\mathcal{P}_\mathrm{even}(n)|$, $p_o(n) := |\mathcal{P}_\mathrm{odd}(n)|$.

**Definition 4.2** (Partition invariants). For a nonempty $S \in \mathcal{P}(n)$, let:
- $b(S) := \min(S)$ — the *base*,
- $m(S) := \max(S)$ — the *maximum*,
- $s(S) :=$ the length of the longest consecutive run $\{m(S)-s+1, \ldots, m(S)\} \subseteq S$ — the *slope*,
- $D(S) := \{m(S) - s(S) + 1, \ldots, m(S)\}$ — the *slope set*.

**Definition 4.3** (Franklin's three classes). For $n \geq 1$ and $S \in \mathcal{P}(n)$ nonempty:
$$
S \in \mathcal{P}_\alpha(n) \iff b(S) \leq s(S) \text{ and } b(S) \notin D(S), \text{ or } b(S)+1 \leq s(S).
$$
$$
S \in \mathcal{P}_\beta(n) \iff s(S) < b(S) \text{ and } b(S) \notin D(S), \text{ or } s(S)+2 \leq b(S).
$$
$$
S \in \mathcal{P}_\mathrm{special}(n) \iff S = \emptyset, \text{ or } b(S) \in D(S) \text{ and } b(S) \in \{s(S), s(S)+1\}.
$$
These are disjoint and cover $\mathcal{P}(n)$.

**Definition 4.4** (Franklin's operations). For $S \in \mathcal{P}_\alpha(n)$ with base $b$, max $m$:
$$\alpha(S) := (S \setminus \{b,\, m-b+1\}) \cup \{m+1\}.$$
For $S \in \mathcal{P}_\beta(n)$ with slope $s$, max $m$:
$$\beta(S) := (S \cup \{s,\, m-s\}) \setminus \{m\}.$$

**Definition 4.5** (Pentagonal partitions). For $k \geq 1$:
- $S_{-k} := \{k, k+1, \ldots, 2k-1\}$ — a partition of $\omega(-k) = (3k^2-k)/2$ into $k$ parts.
- $S_k := \{k+1, k+2, \ldots, 2k\}$ — a partition of $\omega(k) = (3k^2+k)/2$ into $k$ parts.

**Definition 4.6** (Finite q-Pochhammer symbol). For a commutative ring $R$ and elements $a, q \in R$:
$$(a;q)_n := \prod_{k=0}^{n-1}(1 - aq^k), \quad (a;q)_0 = 1.$$

**Definition 4.7** (Infinite q-Pochhammer symbol). For $|q| < 1$ in $\mathbb{C}$:
$$(a;q)_\infty := \prod_{k=0}^{\infty}(1 - aq^k).$$

**Definition 4.8** (Gaussian binomial coefficient). Defined by the $q$-Pascal recurrence:
$$\binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}\binom{n}{k}_q,$$
with $\binom{n}{0}_q = 1$, $\binom{0}{k+1}_q = 0$.

---

## 5. Established results

### 5.1 Franklin Route

**Theorem 5.1** (Disjoint union decomposition). *For every $n \geq 0$,*
$$\mathcal{P}(n) = \mathcal{P}_\alpha(n) \sqcup \mathcal{P}_\beta(n) \sqcup \mathcal{P}_\mathrm{special}(n).$$
*Sketch.* Direct case analysis on the relationship between $b(S)$, $s(S)$, and $D(S)$. ∎

**Theorem 5.2** (Special partition characterization). *For $n \geq 1$:*
- *If $2n \neq 3k^2 \pm k$ for all $k \geq 1$, then $\mathcal{P}_\mathrm{special}(n) = \emptyset$.*
- *If $2n = 3k^2 - k$ for some $k \geq 1$, then $\mathcal{P}_\mathrm{special}(n) = \{S_{-k}\}$.*
- *If $2n = 3k^2 + k$ for some $k \geq 1$, then $\mathcal{P}_\mathrm{special}(n) = \{S_k\}$.*

*Sketch.* For the non-pentagonal case, the conditions $b(S) \in D(S)$ and $b(S) = s(S)$ or $b(S) = s(S)+1$ force $S = \{b, b+1, \ldots, m\}$ to be a consecutive interval, and a sum formula for arithmetic progressions shows such an interval can only sum to $n$ if $n$ is pentagonal. In the pentagonal cases, the unique interval summing to $n$ in the required shape is $S_{\pm k}$. ∎

**Theorem 5.3** (Franklin's map is a bijection). *$\alpha : \mathcal{P}_\alpha(n) \to \mathcal{P}_\beta(n)$ is a bijection with inverse $\beta$.*

*Sketch.* (a) $\alpha$ maps into $\mathcal{P}_\beta$: the new max is $m+1$, the new slope is $b$, the new base is $\geq b+1$ (since the smallest element $b$ was removed), and the class criterion is verified. (b) $\beta \circ \alpha = \mathrm{id}$ and $\alpha \circ \beta = \mathrm{id}$: direct unfolding of the definitions, using the fact that $b \neq m-b+1$ (from $m \geq 2b$, a prerequisite for $\alpha$-membership) and $s \neq m-s$ (from $m \geq 2s+1$, a prerequisite for $\beta$-membership). ∎

**Theorem 5.4** (Parity flip). *For $S \in \mathcal{P}_\alpha(n)$: $|\alpha(S)| = |S| - 1$. For $S \in \mathcal{P}_\beta(n)$: $|\beta(S)| = |S| + 1$.*

*Sketch.* $\alpha$ removes two elements ($b$ and $m-b+1$) and inserts one ($m+1$); $\beta$ inserts two elements ($s$ and $m-s$) and removes one ($m$). Distinctness and non-membership conditions ensure no cancellation. ∎

**Theorem 5.5** (Parity-restricted bijections). *The restriction of $\alpha$ to odd-cardinality $\alpha$-partitions gives a bijection with even-cardinality $\beta$-partitions, and vice versa.*

*Sketch.* Follows from Theorems 5.3 and 5.4. ∎

**Theorem 5.6** (Main combinatorial result). *For all $n \geq 0$:*
$$
(p_e(n) : \mathbb{Z}) - p_o(n) = \begin{cases} (-1)^k & \text{if } 2n = 3k^2 - k \text{ for some } k \geq 1, \\ (-1)^k & \text{if } 2n = 3k^2 + k \text{ for some } k \geq 1, \\ 1 & \text{if } n = 0, \\ 0 & \text{otherwise.} \end{cases}
$$
*Sketch.* From Theorems 5.1, 5.2, and 5.5, the $\alpha$- and $\beta$-contributions cancel, leaving only the special partitions. $S_{-k}$ and $S_k$ each have $k$ parts, contributing $(-1)^k$. ∎

**Theorem 5.7** (Coefficient form of PNT). *For every $n \geq 0$:*
$$[X^n] \prod_{k=1}^n (1 - X^k) = p_e(n) - p_o(n).$$
*Sketch.* Expand via the identity $\prod_{k=1}^n (1+a_k) = \sum_{T \subseteq \{1,\ldots,n\}} \prod_{k \in T} a_k$, with $a_k = -X^k$. Each subset $T$ with $\sum_{k \in T} k = n$ is exactly a partition in $\mathcal{P}(n)$, contributing $(-1)^{|T|}$. ∎

**Theorem 5.8** (Unified PNT, combinatorial form). *For every $n \in \mathbb{N}$, either there exists $k \in \mathbb{Z}$ with $n = k(3k-1)/2$, in which case $p_e(n) - p_o(n) = (-1)^{|k|}$, or no such $k$ exists, in which case $p_e(n) - p_o(n) = 0$.*

Theorems 5.7 and 5.8 together say: $[X^n]\prod_{k=1}^n(1-X^k)$ equals the $n$-th coefficient of the pentagonal series $\sum_{k\in\mathbb{Z}}(-1)^k X^{\omega(k)}$.

---

### 5.2 q-Series / JTP Route

**Theorem 5.9** (Finite q-binomial theorem). *For $n \geq 0$:*
$$\prod_{k=0}^{n-1}(1 + zq^k) = \sum_{k=0}^n q^{\binom{k}{2}} \binom{n}{k}_q z^k.$$
*Sketch.* Induction on $n$ using the $q$-Pascal recurrence. ∎

**Theorem 5.10** (Cauchy identity). *For $|q|, |z| < 1$:*
$$\sum_{n=0}^{\infty} \frac{(a;q)_n}{(q;q)_n} z^n = \frac{(az;q)_\infty}{(z;q)_\infty}.$$
*Sketch.* Let $F(z) := \sum_n c_n z^n$ where $c_n = (a;q)_n/(q;q)_n$. The sequence $(c_n)$ satisfies the recurrence $c_{n+1}(1 - q^{n+1}) = c_n(1 - aq^n)$, which gives $(1-z)F(z) = (1-az)F(qz)$. The right-hand side $G(z) := (az;q)_\infty/(z;q)_\infty$ satisfies the same functional equation. Both sides satisfy $H(q^n z) \to 1$ as $n \to \infty$ (Tannery's theorem), so uniqueness of power series gives $F \equiv G$. ∎

**Theorem 5.11** (Euler's second identity). *For $|q| < 1$ and all $z \in \mathbb{C}$:*
$$\sum_{n=0}^{\infty} \frac{q^{\binom{n}{2}}}{(q;q)_n} z^n = (-z;q)_\infty.$$
*Sketch.* The series $E(z)$ satisfies $E(z) = (1+z)E(qz)$ (term-by-term algebra). For large $N$, $|zq^N| < 1$; bootstrapping back using $E(z) = \prod_{k=0}^{N-1}(1+zq^k) \cdot E(zq^N)$ and the telescoping of $(-z;q)_\infty$ gives the result for all $z$. ∎

**Theorem 5.12** (Key identity). *For $|q| < 1$:*
$$S_k := \sum_{m=0}^{\infty} \frac{q^{m(m+k)}}{(q;q)_m (q;q)_{m+k}} = \frac{1}{(q;q)_\infty}.$$
*Sketch.* The differences $D_k := S_k - S_{k+1}$ satisfy $D_k = q^{k+1} D_{k+1}$, so $|D_k| \leq |D_0| \cdot |q|^{k(k+1)/2} \to 0$. Hence $D_k = 0$ for all $k$, and all $S_k$ are equal. Computing at $k = 0$ via the Cauchy identity gives $S_0 = 1/(q;q)_\infty$. ∎

**Theorem 5.13** (Jacobi Triple Product, analytic). *For $|q| < 1$ and $z \neq 0$:*
$$(q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty = \sum_{k \in \mathbb{Z}} z^k q^{k(k-1)/2}.$$
*Sketch.* Expand $(q;q)_\infty(-z;q)_\infty$ via Euler's second identity: $(q;q)_\infty(-z;q)_\infty = \sum_{n \geq 0} q^{\binom{n}{2}} z^n (q^{n+1};q)_\infty$. Multiply by the Euler second expansion of $(-q/z;q)_\infty$. Rearrange the double sum by diagonals; each diagonal sum evaluates to a single theta series term using Theorem 5.12. The result is proved first for $|z| < 1$, then extended to all $z \neq 0$ using the functional equation $f(qz) = f(z)/z$ satisfied by both sides. ∎

**Theorem 5.14** (Euler's Pentagonal Number Theorem, analytic). *For $|q| < 1$:*
$$(q;q)_\infty = \sum_{k=0}^{\infty} (-1)^k q^{\omega(k)} + \sum_{k=0}^{\infty} (-1)^{k+1} q^{\omega(-(k+1))},$$
where $\omega(k) = k(3k-1)/2$.
*Sketch.* Substitute $q \mapsto q^3$, $z \mapsto -q$ in Theorem 5.13. The right-hand side becomes $\sum_{k\in\mathbb{Z}}(-q)^k q^{3k(k-1)/2} = \sum_{k\in\mathbb{Z}} (-1)^k q^{\omega(k)}$. The left-hand side becomes $(q^3;q^3)_\infty(q;q^3)_\infty(q^2;q^3)_\infty$, which equals $(q;q)_\infty$ by the factorization $\{3n+1\}_{n\geq 0} \cup \{3n+2\}_{n\geq 0} \cup \{3n+3\}_{n\geq 0} = \{n+1\}_{n\geq 0}$. ∎

**Theorem 5.15** (FPS Jacobi Triple Product). *In the formal power series ring $A\llbracket X \rrbracket$ where $A = \mathbb{C}[z, z^{-1}]$ and $X$ is the formal variable (playing the role of $q$):*
$$\mathrm{jtpProd} = \mathrm{jtpSeries},$$
*where $\mathrm{jtpProd} = (X;X)_\infty(-z;X)_\infty(-X/z;X)_\infty$ and $\mathrm{jtpSeries} = \sum_{k\in\mathbb{Z}} z^k X^{k(k-1)/2}$.*

*Sketch.* Via a Cauchy product diagonal decomposition: $\mathrm{jtpProd}$ is expanded as a double sum over $\mathbb{N} \times \mathbb{N}$, then rearranged by a bijection splitting pairs $(n,m)$ into those with $n \geq m$ and those with $n < m$. Each diagonal sum evaluates to a single term of $\mathrm{jtpSeries}$ using FPS Cauchy coefficient identities proved via coefficient stabilization of formal inverses. ∎

---

## 6. In progress

Both main routes (Franklin and q-series/JTP) are complete with no outstanding proofs. The FPS algebraic variant is also complete. The remaining items are structural and presentational.

**Bridge between routes.** There is no explicit formal theorem connecting the Franklin route result (Theorem 5.8, about $p_e(n) - p_o(n)$) to the analytic result (Theorem 5.14, about $(q;q)_\infty$). Mathematically, the connection rests on two steps:
1. The coefficient of $X^n$ in $\prod_{k=1}^\infty (1-X^k)$ (as a formal power series) equals the coefficient of $X^n$ in $\prod_{k=1}^n (1-X^k)$, since factors $1-X^k$ with $k > n$ do not affect degree $\leq n$ terms.
2. When $X = q \in \mathbb{C}$ with $|q| < 1$, the formal power series identity specializes to the analytic identity coefficient-by-coefficient via partial product convergence.

Neither step is currently formalized; both are noted in docstrings only.

**Legacy files.** An older, partially written proof in a different formulation still has two open `sorry`s. This code is superseded by the current formalization and is not part of any submission.

---

## 7. Targets (not yet attempted)

**Formal bridge.** A single theorem connecting the combinatorial form ($[X^n]\prod_{k=1}^\infty(1-X^k) = $ pentagonal coefficient) to the analytic form ($(q;q)_\infty = \sum_k (-1)^k q^{\omega(k)}$) via the FPS route.

**Mathlib integration.** Determining which results are suitable for a Mathlib PR. Candidates include: the q-Pochhammer infrastructure, the Cauchy identity, the Euler identities, the JTP, and the PNT itself.

**Integrality.** The JTP proof works over $\mathbb{C}$; the FPS proof works over $A = \mathbb{C}[z,z^{-1}]$. A version over $\mathbb{Z}[z,z^{-1}]$ would be more fundamental for combinatorial applications, since the identity is an identity of formal Laurent series with integer coefficients.

---

## 8. Where we're stuck

**Stuck point 8.1.** *Connecting the finite and infinite product (Franklin side).*

The Franklin route's central result (Theorem 5.7) is about the finite product $\prod_{k=1}^n(1-X^k)$, not the infinite product $\prod_{k=1}^\infty(1-X^k)$. In formal power series, the $n$-th coefficient of the infinite product is identical to the $n$-th coefficient of the finite product (because multiplying by $1-X^k$ for $k > n$ does not change the degree-$n$ term). This is mathematically trivial but has not been formally stated. The needed lemma is:
$$[X^n] \prod_{k=1}^\infty (1-X^k) = [X^n] \prod_{k=1}^n (1-X^k).$$
We are unsure whether this "coefficient stability" follows cleanly from Mathlib's pi-topology tprod infrastructure, or requires a short bespoke argument.

**Stuck point 8.2.** *Connection between the FPS identity and the analytic identity.*

The FPS JTP (Theorem 5.15) is an equality in $\mathbb{C}[z,z^{-1}]\llbracket X \rrbracket$. The analytic JTP (Theorem 5.13) is an equality in $\mathbb{C}$ for each $(q,z)$ with $|q| < 1$, $z \neq 0$. These are logically independent results with independent proofs. Connecting them requires a "specialization" theorem: evaluating the FPS identity at $X = q$ (via the evaluation ring homomorphism from the pi-topology power series ring to $\mathbb{C}$) recovers the analytic identity. Mathlib has tools for this, but it is not done.

**Stuck point 8.3.** *Integrality of the FPS JTP.*

The FPS algebraic proof works over $A = \mathbb{C}[z,z^{-1}]$. It is unclear whether the existing proof can be promoted to $\mathbb{Z}[z,z^{-1}]$. The main step that uses $\mathbb{C}$ is the Cauchy diagonal decomposition (which uses convergence of complex-valued tprod). A clean algebraic proof over $\mathbb{Z}$ would be more fundamental and potentially more Mathlib-ready.

---

## 9. Open mathematical questions for the reviewer

**Q1.** Theorems 5.7 (Franklin route) and 5.14 (analytic route) are two independent formalizations of the same theorem at different levels of generality. What is the *canonical* form for a Mathlib statement of Euler's PNT? (E.g., as a formal power series identity over $\mathbb{Z}$? As an analytic identity for $|q| < 1$ in $\mathbb{C}$? As the combinatorial $p_e(n) - p_o(n)$ form?)

**Q2.** For Stuck point 8.1 (coefficient stability under tprod): is the statement
$$[X^n]\prod_{k\geq 1}(1-X^k) = [X^n]\prod_{k=1}^n(1-X^k)$$
a clean one-liner from standard formal power series theory, or does it require building the "cofinitely-1 products don't affect bounded degrees" framework explicitly?

**Q3.** The key identity $S_k = 1/(q;q)_\infty$ (Theorem 5.12) is proved via the recurrence $D_k = q^{k+1}D_{k+1}$ and $D_k \to 0$. This is a simple and effective argument. Does the reviewer know a reference for this specific approach? Standard presentations (e.g., [Gasper–Rahman]) use the functional equation / Liouville argument on $\mathbb{C}^*$, which is harder to formalize. If this recurrence argument is new (or at least not well-known), that is worth noting for the write-up.

**Q4.** The FPS JTP (Theorem 5.15) works over $A = \mathbb{C}[z,z^{-1}]$. Is there a clean algebraic proof of the JTP over $\mathbb{Z}[z,z^{-1}]$? Working over $\mathbb{Z}$ would make the result significantly more general. Is the reviewer aware of a reference?

**Q5.** Looking at Definitions 4.3–4.4 and comparing to the classical presentation (e.g., [Andrews 1998]): is the formalization of the three partition classes and the involution operations faithful to the standard mathematical definitions? In particular, the condition "$b(S) \notin D(S)$" appearing in the $\mathcal{P}_\alpha$ and $\mathcal{P}_\beta$ class definitions — is this the right encoding, or is there a simpler equivalent condition that would be cleaner for a Mathlib-style statement?

**Q6.** The project has two independent libraries (Franklin combinatorial + q-series/JTP) that both lead to Euler's PNT but speak different mathematical languages. For a Mathlib contribution, would it be better to (a) contribute them separately as independent developments, (b) contribute only one and have it imply the other, or (c) first write the formal bridge (§6) so they form a single coherent development?

---

## 10. Document metadata

- Project name: `my_project` (Lean 4 / Mathlib formalization of Euler's PNT)
- Authors: Jonathan Conrad, Paula Mürmann, Maryna Viazovska
- Brief generated: 2026-06-17
- Build status at time of writing: both main libraries build cleanly with **zero sorry**; legacy files have 2 open sorry (superseded code, not part of submission)
- Recent commit context: repo restructure completed 2026-06-13; blueprint and dependency graph fully deployed; all Lean code sorry-free

---

*This document was prepared by automated extraction from the Lean source. All mathematical claims above correspond to formally verified results.*
