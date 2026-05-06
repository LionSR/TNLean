This is a Lean 4 / Mathlib repository. Prefer minimal diffs. You MUST fully close
every lemma and theorem — never leave `sorry`, `admit`, `native_decide` on
non-trivial goals, or any placeholder. Hold your fix to the same 8-category
quality bar used by Claude Code Review (proof integrity, proof correctness,
Mathlib style, type safety, performance, modularity, documentation, blueprint
sync). See docs/PROOF_INTEGRITY.md for the full integrity ruleset.

If a mathematical result looks wrong, too strong, or suspiciously general, scout
the LaTeX sources in Papers/ and Notes/ and cite the specific paper/section.
Validate all changes with `lake build` before committing. Use GitHub MCP tools
(`mcp__github__*`) to comment on the PR with a summary of your fix.

