# Content PR path (alternative to proposing the repo)

Only take this path if a maintainer asks for it, or you would rather control the vendored copy
yourself. It is more work: lean-pool **vendors a copy** of the project into its own repository, so
this is a PR against `Vilin97/lean-pool`, not against this repo.

## Rules that bite

From `CONTRIBUTING.md`:

- **Don't mix content and non-content changes.** A content PR may touch **only** `LeanPool.lean`,
  `LeanPool/**/*.lean`, and `LeanPool/projects.yml` (plus the `Challenge`/`Solution` trees, which
  do not apply here). No CI, tooling, or doc changes in the same PR.
- **Never change the checks or gates.** Do not edit workflows, `quality.py`, lint settings, or add
  any waiver (`nolints-style.txt` entry, `set_option linter.X false`, `size-limit-ok`). "If a
  check fails, fix the code, not the check" — stated to apply especially to AI agents.
- **Branch naming:** `yourname/description`, e.g. `conrad/pentagonal-number-theorem`.

## Steps

```bash
git clone https://github.com/Vilin97/lean-pool && cd lean-pool
git checkout -b conrad/pentagonal-number-theorem
lake exe cache get                       # Mathlib oleans; do NOT run `make setup` (~1.5h)
```

1. **Vendor the sources** into `LeanPool/PentagonalNumberTheorem/`, renaming modules from
   `QSeries.*` / `EulerPentagonalNumberTheorem_Franklin.*` to
   `LeanPool.PentagonalNumberTheorem.*`. This is the bulk of the work: every `import` and every
   fully-qualified reference has to move with it.

2. **Add the project card.** Paste `project-card.yml` (next to this file) into
   `LeanPool/projects.yml` under `projects:`, keeping the list ordering convention of the file.

3. **Regenerate the index:**
   ```bash
   lake exe mk_all
   ```

4. **Build just this project** — you do not need the whole pool:
   ```bash
   lake build LeanPool.PentagonalNumberTheorem     # or: make build-project P=PentagonalNumberTheorem
   ```

5. **Open the PR.** CI runs the build, `lake exe runLinter`, `lake exe lint-style`, and the
   quality checker across the pool; then an LLM review of fit and significance
   (`.github/REVIEW_RULES.md`), plus an advisory Greptile review. A `/profile` comment reports
   compile cost — informational, not a gate, but a 4582-line project will show up in it.

## Note on the entry module

The card names `entry_module: LeanPool.PentagonalNumberTheorem`. This branch adds a root
`PentagonalNumberTheorem.lean` importing both halves, which is the module that becomes that entry
point after renaming.
