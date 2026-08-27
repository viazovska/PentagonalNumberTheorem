# lean-pool submission materials

Everything needed to submit this repository to
[lean-pool](https://github.com/Vilin97/lean-pool). Prepared on branch `lean-pool/submission`.

```
project-card.yml     ready-to-paste entry for LeanPool/projects.yml (validated)
proposal-issue.md    issue text for the "propose a repo" path  <- recommended
content-pr-guide.md  steps for the heavier "content PR" path
criteria-check.md    evidence against CRITERIA.txt and every hard gate
```

## The key thing to understand

lean-pool **vendors a copy** of the project into `LeanPool/<Project>/` inside its own repository.
It does not track or submodule your repo. So "submitting" is one of:

1. **Propose the repo** — open an issue, a maintainer imports it. Low effort. Use
   `proposal-issue.md`.
2. **Open a content PR** — you vendor the code into their layout yourself. See
   `content-pr-guide.md`.

Either way, **this repository is not modified by the submission**. The only change this branch
makes to the repo itself is the one preparation step below.

## The one repo change on this branch

A lean-pool project card names a single `entry_module`, but this repo had two independent
libraries and no common root. So this branch adds:

- `PentagonalNumberTheorem.lean` — a root module importing both halves, with a module docstring
  explaining that the two routes are independent
- the matching `[[lean_lib]]` in `lakefile.toml`, added to `defaultTargets`

Verified: `lake build --wfail` → **8293 jobs, 0 warnings, exit 0**.

This is worth merging to `main` regardless of the lean-pool outcome — it gives the repository a
single import point, which it lacked.

## Status of the gates

All measured on this branch; details and evidence in `criteria-check.md`.

| | |
|---|---|
| Own Lean LOC | 4582 (minimum is 250) |
| `sorry` | 0 |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| `unsafe` / `partial` | 0 |
| Licence | Apache-2.0 |
| Build | `--wfail` green, Mathlib linter set enforced |
| Headers / docstrings | 19/19 files · 220/220 declarations |
| Largest file | 716 lines |
| Provenance | `mix` (declared honestly — see criteria-check.md) |

Every published gate is already met. Nothing in the Lean code needs to change for lean-pool.
