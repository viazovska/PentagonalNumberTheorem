---
usemathjax: true
---

# Pentagonal Number Theorem

A Lean 4 / Mathlib formalization of **Euler's Pentagonal Number Theorem** and the
**Jacobi Triple Product**, together with a written-out, machine-checkable blueprint
of the proof structure.

## The theorem

For $\|q\| < 1$,

$$
\prod_{i=1}^{\infty}(1-q^i)
\;=\;
1+\sum_{k=1}^\infty (-1)^k\,\bigl(q^{(3k^2-k)/2}+q^{(3k^2+k)/2}\bigr)
\;=\;
\sum_{k\in\mathbb{Z}}(-1)^k\,q^{(3k^2-k)/2}.
$$

The exponents $(3k^2-k)/2$ are the *generalized pentagonal numbers*.

## Two independent proof routes

This repository formalizes the result **twice**, by genuinely different arguments.
Neither depends on the other.

### 1. Franklin's involution — combinatorial

A sign-reversing involution on partitions of $n$ into distinct parts, whose fixed
points are exactly the "staircase" partitions occurring at pentagonal $n$. This
yields the coefficient identity

$$
[q^n]\prod_{k=1}^{n}(1-q^k) \;=\; p_e(n)-p_o(n) \;=\;
\begin{cases}(-1)^{|k|} & n = k(3k-1)/2,\\ 0 & \text{otherwise,}\end{cases}
$$

where $p_e$ and $p_o$ count partitions into an even resp. odd number of distinct
parts. Note this route works with the **truncated** product $\prod_{k=1}^{n}$,
which agrees with the infinite product in degree $n$.

Source: [`EulerPentagonalNumberTheorem_Franklin/`](https://github.com/{{ site.repository }}/tree/main/EulerPentagonalNumberTheorem_Franklin)

### 2. q-series and the Jacobi Triple Product — analytic

A self-contained development of q-Pochhammer symbols, Euler's identities and the
Cauchy identity, culminating in the Jacobi Triple Product

$$
\prod_{n=1}^{\infty}(1-q^{n})(1+zq^{n-1})(1+z^{-1}q^{n})
\;=\;\sum_{k\in\mathbb{Z}}z^{k}q^{k(k-1)/2},
$$

from which the pentagonal number theorem follows by specialization. The triple
product is proved in two settings: as a **formal power series** identity over any
commutative ring with discrete topology (no convergence needed), and
**analytically** over $\mathbb{C}$ for $\|q\|<1$, $z\neq 0$.

Source: [`Qseries_Formalization/QSeries/`](https://github.com/{{ site.repository }}/tree/main/Qseries_Formalization/QSeries)

## Where to look

- **[Web blueprint]({{ site.url }}/blueprint/)** — the human-readable proof. Each
  definition / lemma / theorem links back to its Lean formalization and to the
  matching `.lean` source on GitHub.
- **[Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)** — visual
  map of how the lemmas depend on each other.
- **[PDF blueprint]({{ site.url }}/blueprint.pdf)** — same content, printable.
- **[Lean API docs]({{ site.url }}/docs/)** — doc-gen4 output for all declarations.
- **[GitHub repository](https://github.com/{{ site.repository }})** — source, issues,
  and pull requests.

## Status

Both routes are **complete**: the project builds with no `sorry` placeholders, no
additional axioms beyond Lean's standard three (`propext`, `Classical.choice`,
`Quot.sound`), and no linter warnings.

**Franklin route** — all fully proved:

- Core definitions: partitions into distinct parts, base, slope, slope set, the
  $\alpha$ / $\beta$ / special partition classes, and Franklin's operations
- Disjointness and union-decomposition of the three classes
- The staircase-set lemmas (cardinality and sum)
- Franklin's involution: $\alpha$ maps into $\beta$, $\beta$ into $\alpha$, mutually inverse
- The resulting bijection, the parity flip, and the closed form for $p_e(n)-p_o(n)$
- Formal-power-series packaging: the coefficient of $q^n$ in the truncated product
  $\prod_{k=1}^{n}(1-q^k)$, in unified integer-index form

**q-series / JTP route** — all fully proved:

- q-Pochhammer symbols, finite and infinite, in $R[[X]]$ and over $\mathbb{C}$
- Euler's first and second identities; the Cauchy identity
- The key identity $S_k = (q;q)_\infty^{-1}$ and the finite q-binomial theorem
- Jacobi Triple Product as a formal power series identity
- Jacobi Triple Product analytically for $\|q\|<1$, $z\neq0$
- Euler's pentagonal number theorem for the infinite product $(q;q)_\infty$

## Contributing

Open an issue on GitHub for typos or mathematical errors in the blueprint. See the
[repository README](https://github.com/{{ site.repository }}#readme) for build
instructions.

## Use of AI

This project used AI assistance at two stages:

- **Aristotle** helped develop and refine the mathematical argument and the
  structure of the blueprint.
- **Claude** assisted with Lean 4 proof development, blueprint maintenance, and
  CI/deployment infrastructure.

## License

Apache License 2.0 — see [LICENSE](https://github.com/{{ site.repository }}/blob/main/LICENSE).

## Authors

Jonathan Conrad, Paula Muermann, Maryna Viazovska.
