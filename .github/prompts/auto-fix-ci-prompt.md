The Lean CI build failed. Your task is to fix the build errors.

Instructions:

0. Use your judgment on whether Mathlib scouting is needed for this fix. For proof-level
   failures (`sorry`, tactic errors, type mismatches in proofs), read PR/issue comments for
   existing **Mathlib Scouting Reports** and use them to inform your fix. For simple failures
   (import errors, syntax issues, naming), skip scouting and fix directly.
1. Read the error logs carefully to identify the failing Lean files and error messages.
2. Common Lean build failures and how to fix them:

   - `sorry` left in proof: fully close the lemma/theorem — replace `sorry` with a complete proof. Do NOT leave `sorry` behind or add TODO comments as a workaround.
   - Type mismatch: check expected vs actual types and fix the proof term.
   - Unknown identifier / import error: add the correct `import` statement.
   - Tactic failure: try alternative tactics (`simp`, `exact`, `apply`, `omega`, etc.).
   - Timeout: simplify the proof or break it into helper lemmas.
3. Your goal is to fully close every incomplete lemma/theorem, not just silence errors. Do not use `sorry`, `admit`, or other shortcuts.
4. Run `lake build` to verify your fix compiles with zero errors and zero `sorry`s.
5. Make minimal, targeted fixes. Do not refactor unrelated code.
6. Commit and push your fix to the current branch. Prefix commit messages with `[claude-auto-fix]`.
7. After pushing, use the GitHub MCP tools to post a comment on the PR summarizing what was fixed.

Quality bar (same rubric as Claude Code Review — your fix MUST satisfy ALL of these before committing):

- Proof integrity (BLOCKER): no `sorry`, `admit`, `native_decide` on non-trivial goals, `unsafeCast`, or new axioms. See `docs/PROOF_INTEGRITY.md`.
- Proof correctness (BLOCKER): structured proofs, not brute-force `simp`/`omega`/`ring` chains. If a result looks wrong, too strong, or suspiciously general, scout `Papers/` and `Notes/` for the original theorems, compare hypotheses/conclusions, cite the specific paper section.
- Mathlib style: camelCase definitions, snake_case lemmas, minimal imports, no unnecessary `open`, prefer `exact` over `apply` + `rfl`.
- Type safety (BLOCKER): no universe issues, missing `[DecidableEq]`/`[Fintype]` instances, or coercion-chain unification failures.
- Performance: avoid `decide` on large types, unbounded `simp` sets, deep `rw` chains, `norm_num` on symbolic expressions. Prefer `omega`, `positivity`, explicit `calc`.
- Modularity: keep new lemmas general; do not duplicate existing Mathlib results.
- Documentation: new definitions and key theorems get docstrings that explain mathematical meaning, not Lean syntax.
- Blueprint sync: when adding or completing (removing `sorry` from) theorems/lemmas/defs, update the corresponding `blueprint/src/chapter/` entry — add `\lean{DeclarationName}` and `\leanok` tags for new results, or add `\leanok` to `\begin{proof}` for newly proven results.

If you cannot satisfy a BLOCKER category, STOP and post a PR comment explaining the obstacle instead of pushing a half-fix.
