Use `gh pr diff ${{ github.event.pull_request.number }}` to see the changes.

Focus your review on the categories below. Each category has a severity level
that determines whether the PR can be approved with outstanding issues.

**Severity levels:**
- 🔴 **Blocker** — must be fixed before merge. Request changes if any are found.
- 🟡 **Requires changes** — must be addressed before approval. These are NOT nits.
  Do NOT approve the PR while issues in this category remain unresolved.
- ℹ️ **Advisory** — flag for awareness, acceptable with justification.

---

1. 🔴 **Proof integrity**: Read `docs/PROOF_INTEGRITY.md` for the complete list of proof
   integrity rules. Flag **blockers** as must-fix issues that should block merge. Flag
   **warnings** as advisory — note them but acknowledge they may be acceptable with justification.
   For each finding, explain WHY it is problematic and suggest the correct alternative.
2. 🔴 **Proof correctness**: Are proof terms well-structured? Do tactic proofs follow a logical
   strategy, or are they brute-forced with `simp` / `omega` / `ring` chains? Are `calc` blocks
   and `conv` rewrites correctly chained? Are hypotheses used or dangling?
   If a mathematical result looks wrong, too strong, or suspiciously general, **scout** the
   LaTeX sources in `Papers/` and `Notes/` where the original theorems and proofs are
   stored. Read the relevant sections, compare hypotheses and conclusions, and cite the
   specific paper/section when flagging a discrepancy.
3. 🟡 **Mathlib style**: Does the code follow Mathlib conventions? Check naming (`camelCase` for
   defs, `snake_case` for lemmas), tactic style (prefer `exact` over `apply` + `rfl` when
   equivalent), import hygiene (no unnecessary `open`s, minimal imports), and lemma placement.
   Style violations are NOT nits — they must be fixed before approval.
4. 🔴 **Type safety**: Any type mismatches, universe issues, or coercion problems? Check for
   universe polymorphism issues, missing `[DecidableEq]` or `[Fintype]` instances, and
   coercion chains that may cause unification failures.
5. 🟡 **Performance**: Will any proofs cause timeouts? Watch for `decide` on large types,
   `simp` with unbounded lemma sets, deep `rw` chains, and `norm_num` on symbolic expressions.
   Suggest alternatives like `omega`, `positivity`, or explicit `calc` steps.
   Performance issues that will likely cause timeouts must be fixed before approval.
6. 🟡 **Modularity & duplication**: Are new lemmas general enough? Could any be upstreamed to
   Mathlib? Are there lemmas that are overly specialized to the local context but could be
   stated more generally? Is the file structure consistent with the existing module hierarchy?
   Flag duplicated logic or lemmas that restate existing Mathlib results.
   Modularity and duplication issues must be fixed before approval.
7. 🟡 **Documentation**: Do new definitions and key theorems have docstrings? Are module-level
   doc comments present for new files? Do docstrings explain mathematical meaning, not just
   Lean syntax? Missing documentation must be added before approval.
8. 🟡 **Paper-gap notes**: When the PR changes files under `docs/paper-gaps/`, read
   `docs/paper-gaps/policy.tex` before reviewing the changed note. Check that the note is a
   self-contained mathematical account: it introduces its notation, states the cited assertion,
   isolates the calculation or logical obstruction, compares the cited source with the
   blueprint and Lean statement when relevant, and gives a precise verdict. If the note cites
   a paper, blueprint, or project source file, inspect the cited passage and flag unsupported,
   overstated, or ambiguous claims. Paper-gap notes must be written for third-party
   mathematical readers, not as issue logs or implementation diaries.

**Out of scope** (handled by the dedicated `Blueprint Sync & Prose Review` workflow — do
NOT comment on these here, to avoid duplicate review threads):
- Blueprint ↔ Lean sync (`\lean{...}` / `\leanok` / `\uses{...}` tags, `\leanok` on proofs).
- Prose quality / banned AI-software language in blueprint `.tex` and Lean docstrings.
  This exclusion does not apply to paper-gap notes, which are reviewed here against
  `docs/paper-gaps/policy.tex`.

---

**Review verdict rules:**
- If ANY 🔴 or 🟡 issues are found, submit the review as **REQUEST_CHANGES**.
  Do NOT approve while these issues remain unresolved.
- Only **APPROVE** when all 🔴 and 🟡 issues have been addressed.
- ℹ️ advisory items alone do not block approval.
- Do NOT label issues as "Nit" or "non-blocking" if they fall under a 🟡 or 🔴 category.
  Use clear language: "This must be fixed before merge" or "Requires changes".

For each issue found, post an inline comment on the relevant line using the GitHub CLI.
At the end, post a summary comment on the PR with your overall assessment.
In that assessment, describe mathematical concerns by naming the theorem, lemma,
definition, proof obligation, or paper-gap assertion. When you flag a paper/blueprint
discrepancy, cite the source path, line number, label, and a short quotation or precise
paraphrase. State the theorem, lemma, definition, or proof obligation directly.

**Reading existing feedback:**
Before posting new comments, read ALL existing feedback on this PR using the GitHub MCP tools:
1. Read **inline review threads** via `get_review_comments` — these are code-level comments from previous review cycles.
2. Read **PR conversation comments** via `get_comments` — bots and humans often post feedback, summaries,
   and discussion directly on the PR thread (not as inline review comments). These are equally important.
This includes threads from previous review cycles and any replies from @claude, other bots, or human reviewers.
Use this context to:
- Avoid re-raising issues that have already been discussed, acknowledged, or fixed in either location.
- Understand any ongoing conversation or decisions made in earlier threads or PR comments.

**Resolving previous review comments:**
When this review is triggered by a `synchronize` event (new push to the PR):
1. First, fetch all review threads **with their GraphQL node IDs** using `gh api graphql`.
   The `get_review_comments` MCP method does not return thread IDs, so you MUST use GraphQL.
2. For each unresolved thread where the author login starts with `claude`, `copilot-pull-request-reviewer`, or `chatgpt-codex-connector`
   (note: GitHub may append `[bot]` to app logins — match the base name as a prefix to handle both forms),
   check whether the new changes address the issue raised in that comment.
   Do NOT resolve threads from `cursor`/Bugbot — that bot manages its own thread resolution.
3. If a previous comment has been addressed by the new commits, resolve it using `mcp__github__resolve_review_thread` with the GraphQL thread `id`.
4. If a previous comment is still relevant (the issue was NOT fixed), leave it unresolved.
5. Only resolve bot threads — never resolve threads authored by human reviewers.
   This prevents stale bot comments from accumulating across review cycles.

**Example: How to fetch thread IDs and resolve them**

Step 1 — Query thread IDs via GraphQL (returns up to 100 threads; see Step 3 for pagination):
```bash
gh api graphql -f query='
{
  repository(owner: "${{ github.repository_owner }}", name: "${{ github.event.repository.name }}") {
    pullRequest(number: ${{ github.event.pull_request.number }}) {
      reviewThreads(first: 100) {
        nodes {
          id
          isResolved
          isOutdated
          comments(first: 1) {
            nodes {
              author { login }
              body
            }
          }
        }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}'
```
This returns thread objects with `id` fields like `"PRRT_kwDON..."`. Use pagination if `hasNextPage` is true.

Step 2 — For each unresolved bot thread whose issue is now fixed, resolve it:
```
mcp__github__resolve_review_thread(threadId: "PRRT_kwDON...")
```

Step 3 — If there are more than 100 threads, paginate:
```bash
gh api graphql -f query='
{
  repository(owner: "${{ github.repository_owner }}", name: "${{ github.event.repository.name }}") {
    pullRequest(number: ${{ github.event.pull_request.number }}) {
      reviewThreads(first: 100, after: "CURSOR_FROM_PREVIOUS_PAGE") {
        nodes { id isResolved isOutdated comments(first: 1) { nodes { author { login } body } } }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}'
```
