---
usemathjax: true
---

# Pentagonal Number Theorem

A Lean 4 / Mathlib formalization of **Euler's Pentagonal Number Theorem** together
with a written-out, machine-checkable blueprint of the proof structure.

## The theorem

For formal power series over a commutative ring,

$$
\prod_{i=1}^{\infty}(1-x^i)
\;=\;
1+\sum_{k=1}^\infty (-1)^k\,\bigl(x^{(3k^2-k)/2}+x^{(3k^2+k)/2}\bigr)
\;=\;
\sum_{k\in\mathbb{Z}}(-1)^k\,x^{(3k^2-k)/2}.
$$

The exponents $(3k^2-k)/2$ are the *generalized pentagonal numbers*. The classical
proof, attributed to Franklin, exhibits a sign-reversing involution on partitions
of $n$ into distinct parts whose fixed points are exactly the "staircase"
partitions at pentagonal $n$.

## Where to look

- **[Web blueprint]({{ site.url }}/blueprint/)** — the human-readable proof. Each
  definition / lemma / theorem links back to its Lean formalization (where it
  exists) and to the matching `.lean` source on GitHub.
- **[Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)** — visual
  map of how the lemmas depend on each other. Click any node to see its statement
  and follow links to the Lean source.
- **[PDF blueprint]({{ site.url }}/blueprint.pdf)** — same content as the web
  version, printable.
- **[Lean API docs]({{ site.url }}/docs/)** — doc-gen4 output for the project's
  Lean declarations.
- **[GitHub repository](https://github.com/{{ site.repository }})** — source code,
  issues, and pull requests.

## Status

The Lean 4 formalization of the Franklin involution proof is complete — no
`sorry` placeholders remain. The following are all fully proved:

- All core definitions (partitions into distinct parts, base, slope, slope set,
  the α / β / special partition classes, Franklin's operations α and β)
- The disjointness and union-decomposition lemmas for the three classes
- The staircase set lemmas (cardinality and sum of $\{m,m{-}1,\ldots,m{-}k{+}1\}$)
- Franklin's involution: αOp lands in β, βOp lands in α, they are mutual inverses
- The bijection and the parity-flip
- The closed form $p_e(n)-p_o(n) = (-1)^k$ for generalized pentagonal $n$, $0$ otherwise
- The formal-power-series packaging: $\prod_{i\geq 1}(1-x^i)$ equals the pentagonal series

## Contributing

Open an issue on GitHub for typos or mathematical errors in the blueprint.
See the [repository README](https://github.com/{{ site.repository }}#readme) for
build instructions.

## Use of AI

This project used AI assistance at two stages:

- **Aristotle** helped develop and refine the mathematical
  argument and the structure of the blueprint.
- **Claude** assisted with Lean 4 proof development, blueprint
  maintenance, and CI/deployment infrastructure.

## Authors

Jonathan Conrad, Paula M{\"u}rmann, Maryna Viazovska.
