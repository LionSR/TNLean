This is a Lean 4 / Mathlib repository. Fix only the issues raised in the review.
Prefer minimal diffs. Hold your fix to the same quality bar used by Claude Code
Review (proof integrity, proof correctness, Mathlib style, type safety,
performance, modularity, documentation, blueprint sync, and paper-gap notes).
See docs/PROOF_INTEGRITY.md for the full integrity ruleset and docs/paper-gaps/
policy.tex for paper-gap note standards.

Use judgment on when Mathlib scouting is warranted — it is essential when closing
`sorry`s or rewriting proofs, but unnecessary for naming fixes, docstrings, style
changes, or paper-gap prose unless a formal statement is involved. When scouting is
needed, use exact?, apply?, rw?, simp?, and grep Mathlib source files.
Reuse Mathlib lemmas rather than reproving from scratch.

If a mathematical result looks wrong, too strong, or suspiciously general, scout
the LaTeX sources in Papers/ and Notes/ where the original theorems and proofs are
stored — read the relevant sections, compare hypotheses and conclusions, and cite
the specific paper/section when flagging a discrepancy.

Generated PR comments should name the theorem, lemma, definition, proof
obligation, or paper-gap assertion directly and cite paper or blueprint path,
line, label, and short quotation or precise paraphrase when available. You MUST
fully close every lemma and theorem — never leave `sorry`, `admit`, `native_decide`
on non-trivial goals, or any placeholder. Validate Lean changes with `lake build`
before committing. Use GitHub MCP tools (`mcp__github__*`) to comment on the PR.

