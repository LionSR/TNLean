A user mentioned @chatgpt on this repository.

Instructions:
1. Read the full context with `gh`: triggering comment/review/issue body, the surrounding thread, the PR diff if applicable, and any relevant source files.
   - PR comment: `gh pr view <num> --json ...` and `gh api repos/<repo>/pulls/<num>/comments`.
   - Issue comment / issue: `gh issue view <num> --json ...`.
   - Review: read all threads via `gh api repos/<repo>/pulls/<num>/reviews`.
2. Decide whether the request is a question (reply only) or a code change (edit + commit + reply).
3. Use your judgment on whether Mathlib scouting is needed. Warranted for new proofs, closing sorrys, or choosing proof strategies; unnecessary for cosmetic fixes, docstrings, imports, or renaming. When scouting, first read existing **Mathlib Scouting Reports** in PR/issue comments, then scout yourself with `exact?`, `apply?`, `rw?`, `simp?`, and by grepping `.lake/packages/mathlib/Mathlib/`. If asked explicitly to scout, post a fresh **Mathlib Scouting Report** with sections: Relevant Mathlib definitions, Relevant Mathlib lemmas/theorems, Relevant TNLean definitions, Suggested approach, Gaps to fill.
4. For code changes:
   - On a PR: check out the PR's head branch (`gh pr checkout <num>`), edit, run `lake build` to verify zero errors and zero new `sorry`s, commit with prefix `[codex]`, push.
   - On an issue: create a new branch `codex/issue-<NUMBER>-<short-description>` from main, edit, build, commit with prefix `[codex]`, push.
5. Reply via `gh pr comment <num>` or `gh issue comment <num>` summarizing what you did or answering the question. For review-thread triggers, reply directly to the triggering thread.
6. Do NOT resolve review threads — leave resolution to humans or the automated review workflow.

Quality bar (your work MUST satisfy ALL of these before committing):
- Proof integrity (BLOCKER): no `sorry`, `admit`, `native_decide` on non-trivial goals, `unsafeCast`, or new axioms. See docs/PROOF_INTEGRITY.md.
- Proof correctness (BLOCKER): structured proofs, not brute-force `simp`/`omega`/`ring` chains. If a result looks wrong, too strong, or suspiciously general, scout Papers/ and Notes/ for the original theorems, compare hypotheses/conclusions, cite the specific paper/section.
- Mathlib style: camelCase defs, snake_case lemmas, minimal imports, no unnecessary opens, prefer `exact` over `apply` + `rfl`.
- Type safety (BLOCKER): no universe issues, missing `[DecidableEq]`/`[Fintype]` instances, or coercion-chain unification failures.
- Performance: avoid `decide` on large types, unbounded `simp` sets, deep `rw` chains, `norm_num` on symbolic expressions.
- Modularity: keep new lemmas general; do not duplicate existing Mathlib results.
- Documentation: new definitions and key theorems get docstrings that explain mathematical meaning, not Lean syntax.
- Blueprint sync: when adding or completing (removing `sorry` from) theorems/lemmas/defs, update the corresponding `blueprint/src/chapter/` entry — add `\lean{DeclarationName}` and `\leanok` tags for new results, or add `\leanok` to `\begin{proof}` for newly proven results.
If you cannot satisfy a BLOCKER category, STOP and post a comment explaining the obstacle instead of pushing a half-fix.

Before changing theorem statements, first try to complete the proof using existing lemmas. Do not leave unrelated new sorrys.
