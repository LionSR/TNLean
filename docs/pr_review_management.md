---
modifiedBy: custom:leanOrchestrator
executionId: 7dfcb0e16ad2
modifiedAt: 2026-03-24T18:31:28.844Z
pinned: true
---
# PR Review and Merge Lessons — 2026-03-23

## Critical Rules

1. **Never merge a PR without consulting the user.** Merging is the user's decision.
2. **Every review comment must be addressed before merge.** If Bugbot, Claude, Copilot, or Codex flagged something, it must be fixed or explicitly justified — not just acknowledged.
3. **Don't rush through PR triage.** Reading "0 sorry, CI pass" is not enough. Must read every inline comment and PR-level comment in full.
4. **Closing a PR loses its unique code.** Before closing, verify that all definitions/theorems from that PR exist elsewhere (on main or in another open PR). PR #100's `permuteConjBlockMap`/`orbitUnitaryPow` were lost.

## Process for PR Review

1. Check CI status
2. Check sorry count in diff
3. **Read ALL three types of comments** (see API map below)
4. For each comment: is it addressed? If not, note it.
5. If unaddressed comments exist: do NOT merge. Either fix first or flag to user.
6. Present summary to user and let them decide.

## Mathlib-style PR and Documentation Standards (from docs/MATHLIB_pr-review.md and docs/MATHLIB_doc.md)

PRs should follow the mathlib review checklist — review for: **style**, **documentation**, **location**, **improvements**, and **library integration**.

### Documentation (docs/MATHLIB_doc.md)
- Every file needs: copyright header, imports, module docstring with `/-! -/`
- Module docstring sections (in order): Main definitions, Main statements, Notation, Implementation notes, References, Tags
- Every `def` must have a docstring. Theorems encouraged. Use backticks for Lean names, LaTeX for math.
- Sectioning comments `/-! ### Section title -/` for structure within files
- References should use BibTeX entries

### PR and issue title conventions
@codex and @claude generate inconsistent titles. Unify before merging:
- **Title format**: `type(scope): description`, for example
  `feat(Wolf Chapter 6): add conditional expectation (Theorem 6.15)`.
- **Types**: `feat` (new formalization), `fix` (mathematical or proof correction),
  `doc` (documentation only), `style` (formatting, naming, prose, or title
  cleanup), `refactor` (restructure without changing mathematical content),
  `ci` (CI/workflow changes), `chore` (dependencies or linting).
- **Scope**: paper tag or chapter, such as `Wolf Chapter 2`, `Wolf Chapter 6`,
  `1804.04964`, `1708.00029`, `MPS/Chain`, or `PEPS`. No brackets.
- **Description**: lowercase, imperative mood, concise. Reference
  theorem/proposition numbers where applicable.
- **Body**: should have `### Motivation`, `### Description`, and
  `### Testing` sections. Reference the issue number. List files changed.
- **Clean up bot-generated titles** before merging. Codex/Claude often produce
  verbose or inconsistent titles like `[PR #165 follow-up] BlockedChainFT style
  cleanups and term-mode endpoint`. Rename to, for example,
  `style(MPS/Chain): BlockedChainFT term-mode endpoint and naming cleanup`.
- **Issue titles**: do not use PR prefixes. Use plain mathematical titles such
  as `Wolf Chapter 6: fixed-point decomposition for Schwarz maps`,
  `MPS/CanonicalForm: assemble cyclic sectors at a common blocking length`, or
  `Tracking: Wolf Chapter 6 spectral properties`.

### Review checklist (docs/MATHLIB_pr-review.md)
- **Style**: code formatting, naming conventions (`MATHLIB_naming.md`), PR title/description informative
- **Documentation**: docstrings on defs, cross-references, proof sketches in comments for complex proofs, warnings for restricted-use code
- **Location**: declarations in right files, no duplicate results, imports not too heavy, files not too long (>1000 lines → split)
- **Improvements**: split long proofs into lemmas, use better tactics for readability, simplify proof structure
- **Library integration**: sensible API, general enough, fits project design, proper `@[simp]`/`@[ext]` tagging, no instance diamonds
- **Specific checks**: `Type*` not `Type _`, `@[simp]` only where appropriate, new defs come with lemmas

## Inline Comment Status — Use GraphQL, Not REST

The REST API `line` field is unreliable for determining if a comment is addressed:
- `line=null` correlates with outdated but isn't the authoritative field
- `line=<number>` does NOT mean unresolved

**Use GraphQL instead** — it has explicit `isResolved` and `isOutdated` fields:

```bash
REPO_OWNER="LionSR"; REPO_NAME="TNLean"; PR=133
gh api graphql -f query='{
  repository(owner: "'$REPO_OWNER'", name: "'$REPO_NAME'") {
    pullRequest(number: '$PR') {
      reviewThreads(first: 20) {
        nodes {
          isResolved
          isOutdated
          comments(first: 1) {
            nodes { body outdated path line }
          }
        }
      }
    }
  }
}'
```

Interpretation:
- `isResolved=true` → Explicitly marked resolved (by reviewer or author)
- `isOutdated=true` → Code at that position changed by subsequent commit
- **Unresolved + not outdated** = must be addressed before merge
- **Unresolved + outdated** = code changed but thread wasn't formally resolved; usually OK but verify
- `isResolved` and `isOutdated` are on the **thread** level; `outdated` is on individual **comment** level

## GitHub PR Comment API Map

Three SEPARATE places comments live on a PR. Must check ALL three.

### 1. Inline review comments (on specific diff lines)
- **What**: Bugbot (cursor[bot]), Copilot, Codex (chatgpt-codex-connector), and Claude inline findings on specific lines
- **API**: `gh api repos/OWNER/REPO/pulls/N/comments`
- **NOT returned by**: `gh pr view --json comments` or `--json reviews`
- **Key fields**: `path`, `line`, `body`, `user.login`, `in_reply_to_id`

### 2. PR-level comments (conversation thread)
- **What**: Claude review summaries, human comments, @codex/@claude responses
- **API**: `gh api repos/OWNER/REPO/issues/N/comments` OR `gh pr view N --json comments`
- **Key fields**: `body`, `author.login`, `createdAt`
- **Watch for**: Claude sometimes embeds inline-style nits here when it can't post inline

### 3. Review summaries (top-level review verdict)
- **What**: Bugbot "reviewed and found N issues", human Approve/Request Changes
- **API**: `gh api repos/OWNER/REPO/pulls/N/reviews` OR `gh pr view N --json reviews`
- **Sub-comments**: `gh api repos/OWNER/REPO/pulls/N/reviews/REVIEW_ID/comments`
- **Key fields**: `state` (APPROVED/COMMENTED/CHANGES_REQUESTED), `body`, `user.login`

### Quick check script for all comments on a PR:
```bash
REPO="LionSR/TNLean"; PR=198
# 1. Inline (Bugbot line-level findings)
gh api "repos/$REPO/pulls/$PR/comments" --jq '.[] | "INLINE [\(.user.login)] \(.path):\(.line) — \(.body[:120])"'
# 2. PR-level (Claude reviews, human comments)  
gh api "repos/$REPO/issues/$PR/comments" --jq '.[] | "PR-LEVEL [\(.user.login)] \(.body[:120])"'
# 3. Review summaries
gh api "repos/$REPO/pulls/$PR/reviews" --jq '.[] | "REVIEW [\(.user.login)] state=\(.state) \(.body[:120])"'
```

## Process for Closing PRs

1. Check what definitions/theorems the PR introduces
2. Verify they exist on main or in another open PR
3. If unique content would be lost, note it in the close comment and create a tracking issue

## Auto-Fix and Mention Protocol

### Auto-fix labels control review repair

The active review-repair loop is label-gated.  A pull request with
`auto-fix-claude` or `auto-fix-codex` is already assigned to the corresponding
auto-fix workflow.  Do not add `@claude auto fix`, `@chatgpt auto fix`, or
similar trigger comments to a PR that already has one of these labels.
Do not use PR replies as an auto-fix control surface for labeled PRs.

In particular, the phrase `auto fix` in a PR reply is not the label-gated
auto-fix trigger.  It starts the ordinary mention-handler lane, which can
duplicate work or race the labeled auto-fix workflow.

Use the labels this way:

| Situation | Action |
|---|---|
| PR has `auto-fix-claude` or `auto-fix-codex` | Leave the PR to the labeled workflow; monitor checks and review threads. |
| PR needs automated review repair and has no auto-fix label | Add the appropriate PR label, then wait for the workflow. |
| Labeled workflow reaches its iteration cap, fails, or stalls | Remove or keep the label deliberately, then fix locally or open a narrow follow-up issue. |
| PR needs a human mathematical decision | Do not ask auto-fix to decide it; comment with the mathematical obstruction or fix locally. |

The auto-fix labels are PR-only controls.  Adding them to issues does not start
the review-fix loop.  See `docs/ci-automation.md` for the workflow details.

### When to use direct mentions

Direct `@claude` / `@chatgpt` mentions are separate from labeled auto-fix.
Use them only for a new delegated task where a separate branch or explicit
one-off answer is intended.
They are not a repair mechanism for a PR that is already on the auto-fix label
lane.

Putting `@claude` or `@chatgpt` in an issue body is unreliable for activation;
post a comment after issue creation if a mention-handler task is intended.  For
new issue-based work, mention comments create fresh work from `main`, so do not
use them for ordinary nits on an existing PR branch.

### Branch-name caveat for mention handlers

Old bracketed issue titles such as `[Wolf Chapter 6] ...` can put `]` into bot
branch names.  Some mention-handler checkouts reject such branch names.  New
issues should keep titles bracket-free, for example `Wolf Chapter 6: ...`.

### Task-size calibration

Mention-handler agents tend to produce small PRs.  Bundle related source-facing
formula or prose repairs into a single issue comment rather than opening many
tiny tasks.  For substantial formalization work, prefer a local branch or an
explicitly scoped issue whose output is one reviewable PR.

## PR Follow-up Wisdom

### How to do a follow-up pass
1. **Get the full open PR list** — `gh pr list --state open`
2. **For EACH PR**, check all 3 comment types (inline, PR-level, reviews) using the script above
3. **Identify what's unresolved** — don't just count comments, READ them
4. If the PR has an auto-fix label, do not post another mention-trigger request; wait for the labeled workflow or fix locally after it fails/stalls.
5. If the PR has no auto-fix label and the comments are mechanical, add the appropriate auto-fix label.
6. If the comments require mathematical judgment, fix locally or write a precise issue comment explaining the obstruction.
7. **Merge clean PRs immediately** — don't let them sit. If ALL comments from ALL reviewers (Bugbot, Claude, Codex, Copilot, humans) are addressed, CI green, no unresolved inline/PR-level/review comments across all 3 endpoints → merge right away. No reason to batch or delay.

### After any fix commit, wait for CI + re-review
Bugbot and claude-review CI run on every new commit.  After a local or auto-fix
commit, wait for CI to complete and check for new inline comments before
declaring the PR ready.

### Superseded PR chains — don't close prematurely
When a replacement PR exists, the replacement often has its own issues.  Do not
close the original until the replacement is clean, linked, and ready.

### Bugbot feedback loops on complex PRs
Bugbot (Cursor) runs on every new commit. Fixing one round of Bugbot issues can trigger a new round of different issues on the fix commit (seen on PR #163: 4 issues → fix → 3 new issues → fix → 3 more new issues). Budget for multiple rounds, or batch all fixes in one commit.

## Blueprint Sync Process

### Problem
Formalization PRs routinely merge without updating the blueprint. This creates drift — Lean declarations exist on main but have no `\lean{}` or `\leanok` tags in the blueprint.

### Adopted process
1. **After merging formalization PRs**, create blueprint sync issues grouped by chapter
2. **Tag @codex on the issue** to generate a PR that adds `\lean{}` and `\leanok` tags
3. **Issue naming**: "Blueprint sync — ChNN topic: list of additions" (bracket-free)
4. **Include grep commands** in the @codex comment so it can find the actual Lean names
5. **One issue per chapter or small group** — keeps PRs focused and reviewable
6. **Issue #116** tracks the overall process improvement

### Blueprint tag format
```latex
\begin{theorem}[Title]\label{thm:label}
    \lean{LeanDeclarationName}
    \leanok
    % LaTeX statement
\end{theorem}
\begin{proof}\leanok
    % proof sketch or reference
\end{proof}
```

### Quality notes
**Structure is good**: @codex produces proper `\lean{}`, `\leanok`, `\uses{}` cross-refs and proof sketches.

**Style needs correction**: @codex leaks Lean jargon into the mathematical text. The blueprint must read as pure mathematics. Specific rules:
- **NO `\texttt{LeanName}` in theorem statements** — use math notation instead. Write "periodic-chain tensors" not `\texttt{PeriodicMPSTensor}`.
- **NO Lean types** — write "$\{1,\ldots,m\}$" not "$\Fin m$". Write "$M_D(\mathbb{C})$" not "Matrix (Fin D) (Fin D) ℂ".
- **NO implementation language** — don't say "represented by the alias", "bundled", "Equivalence structure", "instance". Say "is an equivalence relation" instead.
- **NO excessive `\textbf{}`** — use `\emph{}` sparingly, following existing style.
- **Model on existing entries**: the existing blueprint reads like a math textbook. Match that tone.
- Include these style rules in every @codex blueprint sync comment.

**Ask for MORE per issue** — @codex finishes fast and produces small PRs. Bundle more declarations into each sync issue to reduce PR overhead.

### Current sync issues (2026-03-24)
- #217 → PR #220: Chapter 04 channels (Kraus converse, trace pairing)
- #218 → PR #222: Chapter 06 spectral (Theorem 6.2 item 3, Theorem 6.8 wrappers, Theorem 6.15)
- #219 → PR #221: Chapter 02 MPS periodic + Chapter 11 assembly Z-gauge

## What Went Wrong — Session 2026-03-23

- Merged 5 PRs (#99, #104, #107, #109, #111) with unaddressed review comments
- Had to create cleanup issue #120 after the fact
- Closed PR #100 without realizing its unique definitions were lost
- Posted @codex tags on merged PRs (does nothing)
- Rushed through 23 PRs trying to "clear the backlog" instead of reviewing carefully

## What Went Wrong — Session 2026-03-24

- Merged PR #162 without catching an in-proof comment nit (lines 109-110) from Claude's PR-level review. The nit was in the Claude review text, NOT in formal inline comments — so checking "0 inline comments" wasn't enough.
- **Lesson**: Claude sometimes posts inline-style feedback as PR-level comments (when it can't post inline due to permissions). Must read the FULL text of every Claude review comment, not just count inline comments.
- Posted 15 `@codex` comments on issues asking it to "review branch X" or "push fixes to branch Y" — ALL will fail because @codex cannot fetch existing PR branches. Wasted effort. Should have either done fixes locally or asked @codex to create fresh replacement PRs from main.
