The automated code review found issues in this PR. Your task is to fix them.

Instructions:

1. First, use the GitHub MCP tools to read the full PR diff and all review threads yourself. Treat the thread summaries from this workflow as seeds only.
2. Use your judgment on whether Mathlib scouting is needed for this fix. For review comments about proofs (`sorry` removal, tactic suggestions, proof restructuring), read PR/issue comments for existing **Mathlib Scouting Reports** and use them to inform your fix. For cosmetic comments (naming, docstrings, style), skip scouting and fix directly.
3. Read each review thread conversation and understand the issue being raised, including follow-up replies that may refine the original comment.
4. Fix each issue in the relevant file at the indicated line.
5. If the review state is `"APPROVED"` with no comments requiring changes, do nothing.
6. Common fixes:

   - Remove `sorry` and fully close the lemma/theorem with a complete proof. Do NOT leave `sorry` behind or replace it with another shortcut.
   - Fix naming to match Mathlib conventions.
   - Add missing docstrings where requested.
   - Fix type mismatches or tactic failures.
   - Improve proof structure as suggested.
   - Revise paper-gap notes so that they satisfy `docs/paper-gaps/policy.tex`.
7. If you edit a paper-gap note, preserve it as a self-contained mathematical document:

   - introduce the notation,
   - state the cited assertion,
   - isolate the mathematical obstruction,
   - compare with the blueprint and Lean statement when relevant,
   - give a precise verdict.
   Compile or verify the edited LaTeX document when practical; otherwise explain why that check was not run.
8. Your goal is to fully close every incomplete lemma/theorem, not just address minor comments. Do not use `sorry`, `admit`, `native_decide` on non-trivial goals, or other shortcuts.
9. Run `lake build` to verify your fixes compile with zero errors and zero `sorry`s.
10. When your fixes add or complete (remove `sorry` from) theorems, lemmas, or definitions, update the corresponding blueprint entry in `blueprint/src/chapter/` — add `\lean{DeclarationName}` and `\leanok` tags for new results, or add `\leanok` to `\begin{proof}` for newly proven results.
11. Make minimal, targeted fixes. Do not refactor unrelated code.
12. Commit and push your fix to the current branch. Prefix commit messages with `[claude-review-fix]`.
13. After pushing, use the GitHub MCP tools to post a comment on the PR with:

   - a summary of which review items were addressed,
   - for paper-gap note changes, the revised mathematical verdict and cited source passage,
   - if you used or discovered Mathlib lemmas during the fix, include a **Mathlib Audit** section (name, module path, and how it was used).
   Skip this section for trivial fixes that did not involve Mathlib.

Quality bar (same rubric as Claude Code Review — your fix MUST satisfy ALL of these before committing):

- Proof integrity (BLOCKER): no `sorry`, `admit`, `native_decide` on non-trivial goals, `unsafeCast`, or new axioms. See docs/PROOF_INTEGRITY.md.
- Proof correctness (BLOCKER): structured proofs, not brute-force `simp`/`omega`/`ring` chains. If a result looks wrong, too strong, or suspiciously general, scout Papers/Notes for the original theorems, compare hypotheses/conclusions, cite the specific paper/section.
- Mathlib style: camelCase definitions, snake_case lemmas, minimal imports, no unnecessary `open`, prefer `exact` over `apply` + `rfl`.
- Type safety (BLOCKER): no universe issues, missing `[DecidableEq]`/`[Fintype]` instances, or coercion-chain unification failures.
- Performance: avoid `decide` on large types, unbounded `simp` sets, deep `rw` chains, `norm_num` on symbolic expressions. Prefer `omega`, `positivity`, explicit `calc`.
- Modularity: keep new lemmas general; do not duplicate existing Mathlib results.
- Documentation: new definitions and key theorems get docstrings that explain mathematical meaning, not Lean syntax.
- Blueprint sync: when adding or completing (removing `sorry` from) theorems/lemmas/defs, update the corresponding `blueprint/src/chapter/` entry — add `\lean{DeclarationName}` and `\leanok` tags for new results, or add `\leanok` to `\begin{proof}` for newly proven results.
- Paper-gap notes: changed notes under `docs/paper-gaps/` must follow `docs/paper-gaps/policy.tex` by introducing notation, stating the cited assertion, isolating the mathematical obstruction, comparing with blueprint and Lean statements when relevant, and giving a precise verdict for third-party mathematical readers.

If you cannot satisfy a BLOCKER category, STOP and post a PR comment explaining the obstacle instead of pushing a half-fix.
