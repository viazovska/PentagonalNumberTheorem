# Expert-review session state

- Generated: 2026-06-17T00:00:00
- Audience: Senior q-series / combinatorics expert
- Goal of brief: Pre-submission read — anything obviously wrong before we finalize/submit
- Scope: Both routes — Franklin involution + q-series / Jacobi Triple Product
- Reply received: false
- Reply integrated: false

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | What is the *canonical* form for a Mathlib statement of Euler's PNT? (Formal power series over ℤ? Analytic for |q|<1 in ℂ? Combinatorial p_e(n)-p_o(n) form?) |
| Q2 | Is the coefficient stability statement [X^n]∏_{k≥1}(1-X^k) = [X^n]∏_{k=1}^n(1-X^k) a clean one-liner from standard formal power series theory, or does it require explicit infrastructure? |
| Q3 | Is there a reference for the key identity S_k=1/(q;q)_∞ via the recurrence D_k=q^{k+1}D_{k+1} and D_k→0? Standard texts use Liouville; this approach is simpler to formalize. |
| Q4 | Is there a clean algebraic proof of the FPS JTP over ℤ[z,z^{-1}] rather than ℂ[z,z^{-1}]? Any reference? |
| Q5 | Is our formalization of the three partition classes (Definition 4.3) faithful to [Andrews 1998]? In particular, is the condition "b(S) ∉ D(S)" the right encoding? |
| Q6 | For Mathlib contribution: contribute the two libraries separately, contribute only one, or first write the formal bridge? |

## Ticket-board snapshot at brief time

No ticket system (no .mathlib-quality/tickets.md). Summary of open mathematical sub-goals:

- Formal bridge between Franklin route (finite product coefficients) and analytic route ((q;q)_∞) — not started
- Coefficient stability under tprod: [X^n]∏_{k≥1}(1-X^k) = [X^n]∏_{k=1}^n(1-X^k) — not started
- FPS JTP over ℤ[z,z^{-1}] — not started
- Mathlib integration scoping — not started

## Stuck points (from §8 of brief)

1. Connecting finite and infinite product on the Franklin side (coefficient stability lemma)
2. Specialization: FPS identity → analytic identity via evaluation ring homomorphism
3. Integrality: FPS JTP currently over ℂ[z,z^{-1}], not ℤ[z,z^{-1}]

## Reference list (from §2.2 of brief)

- [Andrews 1998] George E. Andrews. *The Theory of Partitions*. Cambridge University Press, 1998.
- [Hardy–Wright 2008] Hardy and Wright. *An Introduction to the Theory of Numbers*, 6th ed. Oxford University Press, 2008.
- [JC–PM–MV 2026] Conrad, Massot, Viazovska. "Pentagonal Number Theorem" (internal manuscript, 2026).
- [Gasper–Rahman 2004] George Gasper and Mizan Rahman. *Basic Hypergeometric Series*, 2nd ed. Cambridge University Press, 2004.
