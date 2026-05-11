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

This is a work in progress. The blueprint contains the full mathematical argument;
the Lean formalization is partial. Declarations currently in Lean:

- `all_distinct_partitions`, `even_distinct_partitions`, `odd_distinct_partitions`
- `base` (the smallest part of a partition)
- `euler_pentagonal_number_theorem` (statement only, proof `sorry`)

## Contributing

Open an issue on GitHub for typos / mathematical errors in the blueprint, or
send a pull request with a Lean proof attached to one of the blueprint lemmas.
See the [repository README](https://github.com/{{ site.repository }}#readme) for
build instructions.

## Authors

JC, PM, MV.
