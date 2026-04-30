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

## Mathlib-style PR and Documentation Standards (from docs/pr-review.md and docs/doc.md)

PRs should follow the mathlib review checklist — review for: **style**, **documentation**, **location**, **improvements**, and **library integration**.

### Documentation (docs/doc.md)
- Every file needs: copyright header, imports, module docstring with `/-! -/`
- Module docstring sections (in order): Main definitions, Main statements, Notation, Implementation notes, References, Tags
- Every `def` must have a docstring. Theorems encouraged. Use backticks for Lean names, LaTeX for math.
- Sectioning comments `/-! ### Section title -/` for structure within files
- References should use BibTeX entries

### PR and issue title conventions
@codex and @claude generate inconsistent titles. Unify before merging:
- **Title format**: `type(scope): description`, for example
  `feat(Wolf Ch6): add conditional expectation (Thm 6.15)`.
- **Types**: `feat` (new formalization), `fix` (mathematical or proof correction),
  `doc` (documentation only), `style` (formatting, naming, prose, or title
  cleanup), `refactor` (restructure without changing mathematical content),
  `ci` (CI/workflow changes), `chore` (dependencies or linting).
- **Scope**: paper tag or chapter, such as `Wolf Ch2`, `Wolf Ch6`,
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
  as `Wolf Ch6: fixed-point decomposition for Schwarz maps`,
  `MPS/CanonicalForm: assemble cyclic sectors at a common blocking length`, or
  `Tracking: Wolf Ch6 spectral properties`.

### Review checklist (docs/pr-review.md)
- **Style**: code formatting, naming conventions (`naming.html`), PR title/description informative
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

## How @codex and @claude Respond

### @codex/@claude only trigger from COMMENTS, not issue/PR body
Putting `@codex` or `@claude` in the body text when creating an issue does nothing. They only trigger from **comments** posted after creation. Must post a separate comment to activate them.

### Issue comments vs PR comments — critical distinction

| Where you post | @codex behavior | @claude behavior |
|---|---|---|
| **Issue comment** | Creates a **new branch from main**, writes code from scratch. Cannot see any existing PR branch. | Creates a **new branch from main**, writes code from scratch. Same as codex. |
| **PR comment** | Runs a cloud task on the PR's diff. **CAN push fix commits** to the branch (confirmed: pushed to #215, #214, #213, #200, #198, #133). Sometimes fails with "Codex couldn't complete this request" (#212, #211, #206, #201, #196, #167, #91). Also posts review comments. Works on `]` branches! | Checks out **that PR's branch**, can push fix commits to it. BUT fails on branches with `]` in the name (all codex branches) due to `claude-code-action` branch name validation. |
| **Merged PR comment** | May trigger but no useful effect. | May trigger but no useful effect. |

### Key implications
1. **@codex on issues = fresh start from main.** It will never see the existing PR's code. Good for: creating replacement PRs. Bad for: reviewing or fixing existing PRs.
2. **@claude on PRs = works on that branch.** Good for: pushing fix commits to an existing PR. Bad for: codex branches (name has `]`).
3. **Neither can rebase.** Must do locally.
4. **@codex cannot fetch other branches.** Sandboxed environment blocks `git fetch` (HTTP 403). Asking it to "review branch X" or "push to branch Y" will always fail.

### Why @claude fails on codex branches — confirmed root cause
Codex auto-generates branch names from the issue title:
`codex/github-mention-{ISSUE_TITLE_SLUG}-{RANDOM}`. Issue titles with brackets,
such as `[Wolf Ch6]` or `[1804.04964]`, can therefore put `]` into the branch
name.

The `anthropics/claude-code-action` **explicitly validates branch names** and rejects any containing git special characters `~^:?*[\]`. The exact error:
```
Action failed with error: Invalid branch name: "codex/github-mention-wolf-ch5]-schwarz-implies-normal/subnormal-r2wysl".
Branch names cannot contain control characters, spaces, or special git characters (~^:?*[\]).
```

This means **every PR created by @codex from a bracket-titled issue → @claude will always fail**.

**The root cause was the old issue naming convention.** Codex strips the `[` but keeps the `]` in the branch slug.

**Solutions:**
- **ADOPTED: Bracket-free issue naming convention.** Use `Wolf Ch6: ...` or
  `1804.04964: ...` instead of `[Wolf Ch6] ...` or `[1804.04964] ...`. This
  prevents `]` from appearing in codex branch names, making them
  @claude-compatible. Apply to all new issues going forward; existing issues
  can be renamed as needed.
- Fix locally (checkout branch, make changes, push) — still needed for existing `]` branches
- Ask @codex on the issue to create a fresh replacement PR from main (new branch, new PR)
- @codex on the PR can still run reviews (reads the diff, doesn't need to checkout the branch)

### @codex on issues always creates NEW PRs — causes PR proliferation
Every @codex trigger on an issue creates a new branch from main → new PR. It CANNOT push to an existing PR's branch. This leads to chains like: PR #162 (original) → Issue #205 (nit) → PR #216 (new PR for a 2-line fix). Or: PR #200 → PR #208, PR #201 → PR #210, PR #165 → PR #215, etc.

**To keep work on the SAME PR branch, use @claude on the PR** (not @codex on an issue). @claude pushes directly to the PR branch. Only falls back to @codex-on-issue when @claude can't work (] branches).

### @codex produces tiny PRs — calibrate task size
Codex tends to produce very small PRs (6-60 lines) even when asked for substantial work. Examples from 2026-03-24: PR #206 was 6 lines, #207 was 18 lines, #213 was 45 lines. This means:
- **Don't split tasks too finely** for @codex — it will produce trivially small PRs that create review overhead disproportionate to their value.
- **Bundle related tasks** into single issue comments (e.g., "fix items 1-5" not 5 separate issues).
- **For substantial formalization work**, do it locally or in a single orchestrated session rather than farming out to @codex on GitHub.

### What ACTUALLY works
| Scenario | Solution |
|---|---|
| **Fix** a PR on **any branch** | **@codex on the PR comment** — CAN push fix commits even to `]` branches. Sometimes fails ("couldn't complete"), retry if needed. |
| **Fix** a PR on a **claude branch** (no `]`) | **@claude on the PR comment** — also pushes directly. Preferred when it works (more reliable than codex). |
| **Review** a PR (any branch) | @codex on PR comment, or Bugbot/claude-review CI (automated), or locally. |
| **Rebase** a conflicting PR | Do it locally — neither @codex nor @claude can rebase |
| **Add new code** related to an issue | @codex or @claude on the issue — both create new branches from main |

### Preferred workflow for fixing review comments
**Always fix on the SAME PR.** No new PRs, no new issues for nits.

1. PR gets review comments → **@codex on that PR** to fix (works on any branch, including `]`)
2. For clean branches (no `]`) → can also use **@claude on that PR** (more reliable)
3. Gets new comments after fix → repeat on the same PR
4. All comments addressed → merge

**Do NOT create issues for nits on existing PRs.** That triggers @codex on the issue which creates a new replacement PR every time, causing proliferation.

If @codex fails ("couldn't complete") → retry once. If still fails → fix locally.

### @codex "committed but not pushed" — don't retry, ask user to click portal
When @codex says it committed (gives a SHA) but the commit isn't on the branch, the fix exists in the Codex cloud sandbox. **Do NOT retry** — that would create duplicate work. Instead, ask the user to click the Codex portal link (the "View task →" URL in the response) to push the commit. Only retry if the portal link doesn't work.

**This applies to ALL @codex triggers** — both issue comments (which create new PRs) and PR comments (which push fix commits). In all cases, the user must click the portal link to finalize. Collect all pending portal links and present them in a batch so the user can click them all at once.

## PR Follow-up Wisdom

### How to do a follow-up pass
1. **Get the full open PR list** — `gh pr list --state open`
2. **For EACH PR**, check all 3 comment types (inline, PR-level, reviews) using the script above
3. **Identify what's unresolved** — don't just count comments, READ them
4. **Post the follow-up ON THE PR itself** — not on a separate issue
5. **Always post an actionable fix REQUEST, not just a status report.** End with "Please fix and push." Don't just restate the issues — ask @codex/@claude to address them.
6. **Use @claude on the PR** for clean branches (pushes fix directly, same branch)
7. **For `]` branches**, post @codex fix request on the PR (it can't push but confirms the issue and keeps it actionable). Also document what needs local fixing.
7. **Don't create issues for nits** — that spawns new PRs via @codex, causing proliferation
8. **Merge clean PRs immediately** — don't let them sit. If ALL comments from ALL reviewers (Bugbot, Claude, Codex, Copilot, humans) are addressed, CI green, no unresolved inline/PR-level/review comments across all 3 endpoints → merge right away. No reason to batch or delay.

### @codex on PR comments: push vs no-push
@codex sometimes describes changes in a "Summary" response but **does not actually push**. Always verify by checking commit count (`gh api repos/OWNER/REPO/pulls/N/commits | jq length`). If commit count didn't increase, the fix was not applied.

**The user may need to manually click "Update branch" in the Codex web portal** to apply the changes. If @codex says it finished but no commits appear on the PR branch, remind the user to check the Codex portal and click to update.

Also: @codex sometimes gives **superficial "no major issues" review responses** (e.g., "Didn't find any major issues. Breezy!"). These are NOT thorough reviews. Don't count them as "reviewed." The automated `claude-review` CI and `Cursor Bugbot` CI are far more reliable.

### After any fix commit, wait for CI + re-review
Bugbot and claude-review CI run on every new commit. After @codex pushes a fix, **wait for CI to complete** and check for NEW inline comments before declaring the PR ready. Don't assume the fix is clean — the fix itself may introduce new issues (seen repeatedly).

### Superseded PR chains — don't close prematurely
When @codex creates a replacement PR (e.g., #200 → #208), the replacement often has its OWN issues. Don't close the original until the replacement is actually clean and ready. Keep both open and track the chain.

### The `]` branch situation
Most existing PRs have `]` in branch names. @claude can't fix them. **But @codex on the PR CAN push fixes** (confirmed working on 6 PRs). @codex sometimes fails ("couldn't complete") — retry in that case. If @codex also fails repeatedly, fix locally.

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
- #217 → PR #220: Ch04 channels (Kraus converse, trace pairing)
- #218 → PR #222: Ch06 spectral (Thm 6.2 item 3, Thm 6.8 wrappers, Thm 6.15)
- #219 → PR #221: Ch02 MPS periodic + Ch11 assembly Z-gauge

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
