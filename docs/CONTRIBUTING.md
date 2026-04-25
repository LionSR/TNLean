# Contributing to MPSLean

This document codifies the conventions for pull requests, issues, code review,
Lean style, and CI automation used in the MPSLean project.

---

## 1. Pull Request Conventions

### Title format

Use **conventional-commit** style:

```
type(scope): short description
```

| Type       | When to use                                      |
|------------|--------------------------------------------------|
| `feat`     | New definition, lemma, theorem, or module         |
| `fix`      | Bug fix (broken proof, wrong identifier, etc.)    |
| `refactor` | Restructuring without changing API surface        |
| `docs`     | Documentation or blueprint changes only           |
| `ci`       | CI/CD workflow changes                            |
| `chore`    | Dependency bumps, linting, toolchain updates      |

**Scope** is a shortened module path: `MPS/Symmetry`, `Channel`, `blueprint+docgen`,
`MPS/Core`, etc. Omit the `TNLean/` prefix.

Examples:
- `feat(MPS/Symmetry): add twistedTensor as MonoidHom`
- `fix(blueprint+docgen): resolve broken labels and malformed docstring table`
- `refactor(MPS): move Correlations.lean from ParentHamiltonian/ to Core/`

### Body template

Every PR body must contain three sections:

```markdown
### Motivation
- Why this change is needed (1--3 bullets).

### Description
- What was changed: files added/modified, definitions introduced, lemmas proved.
- Use bullet points.

### Testing
- What was verified and how.
- Examples: `lake env lean TNLean/Foo/Bar.lean`, `lake build TNLean`,
  `rg -n "sorry|axiom" TNLean/Foo/Bar.lean || true`.

---
Addresses #N
```

Use `Addresses #N` (keeps the issue open) or `Closes #N` (auto-closes on merge)
in the footer to link the relevant issue.

### PR template

A PR template (`.github/pull_request_template.md`) auto-fills the
Motivation / Description / Testing sections. Fill in the placeholders — do not
delete the headings.

### Labels

Apply all relevant labels from the taxonomy in [Section 4](#4-label-taxonomy).

---

## 2. Issue Conventions

### Issue templates

Three issue templates are available in `.github/ISSUE_TEMPLATE/`:

| Template | When to use |
|----------|-------------|
| **Formalization Task** | A specific theorem, definition, or lemma to formalize |
| **Bug Report** | Broken proof, type error, sorry regression, CI failure |
| **Tracking Issue** | Umbrella issue with native sub-issues attached |

### Formalization issues

Use a descriptive title that names the mathematical content:

```
Symmetry/SPT 3/6 Definitions: twisted tensor and on-site symmetry
```

Label with **area** + **arXiv paper** + **topic** as applicable.

### Multi-part work

For work spanning multiple PRs, use the `Area K/N: title` pattern and create
an umbrella **tracking issue**:

```
RFP/MPDO 1/5 Pure-state RFP: definitions, ZCL <=> E^2=E, structural form
RFP/MPDO 2/5 Commuting parent Hamiltonians and decorrelation theorem
...
```

The tracking issue collects its children as **native GitHub sub-issues**, not as
a tasklist block. (GitHub retired the ` ```[tasklist] ` fenced-block syntax on
2025-04-30 — any remaining tasklist blocks now render as raw Markdown.) Native
sub-issues show up in a dedicated panel on the parent issue, automatically
display "Tracked by #N" in the child sidebar, and contribute to the parent's
built-in progress bar.

#### Attaching a sub-issue

From the GitHub UI: open the parent tracking issue and use **Create sub-issue**
or **Add sub-issue** in the sub-issues panel.

From the CLI / API:

```bash
# REST: attach issue #234 as a sub-issue of #232
gh api -X POST repos/lionsr/tnlean/issues/232/sub_issues \
  -f sub_issue_id=$(gh api repos/lionsr/tnlean/issues/234 -q .id)
```

From an MCP-aware agent: call `mcp__github__sub_issue_write` with
`method: "add"`, `issue_number: <parent>`, and `sub_issue_id: <child node id>`.

#### Body convention

The tracking issue body should mirror the attached sub-issues as a plain
markdown bullet list under a `## Native sub-issues` heading, one issue per line,
in the form `- #N — short note`. The bullet list is for human readers; the
parent/child link itself lives in the sub-issue API. Do not use ` ```[tasklist] `
fences and do not paste `- [ ] #N` checkboxes — checkbox state is no longer the
source of truth for completion.

### Tracking issues

Use the **Tracking Issue** template (`.github/ISSUE_TEMPLATE/tracking-issue.yml`).
Label with `tracking`. The `tracking-issue-sync` workflow will automatically:

- Refresh the tracking-issue body's bullet-list mirror when sub-issues close or reopen.
- Post progress comments on linked issues when PRs are merged (what was done, what remains).
- Attach genuine PR follow-ups as new sub-issues of the relevant tracker.
- Add the `all-resolved` label when every sub-issue is closed.

### Pinned issues

The three most active tracking issues are pinned to the top of the Issues tab.
Update pins when priorities shift (`gh issue pin/unpin`). GitHub allows at most
3 pinned issues.

### Milestones

Use milestones to group issues targeting a shared deadline (e.g., a paper
submission or a toolchain bump). Assign a milestone when the issue has a concrete
target date; remove it when the date no longer applies.

### Discussions

GitHub Discussions is enabled for design questions, proof strategy debates, and
topics that don't map to a single actionable issue (e.g., "Should MPDO live
under MPS/?"). Use issues for concrete work items; use discussions for open-ended
conversations.

### Blueprint sync issues

When the LaTeX blueprint is out of sync with Lean code, open an issue with
the `blueprint-sync` label. Describe which chapter, theorem, or definition
needs `\lean{}` / `\leanok` tags.

---

## 3. Commit Messages

- Use **imperative mood** in the subject line ("Add", not "Added").
- Keep the subject under 72 characters.
- When squash-merging a PR, the commit message should match the PR title format.
- Reference issue numbers where applicable (`(#N)` suffix or `Addresses #N` in body).

---

## 4. Label Taxonomy

### Area labels

| Label            | Description                                |
|------------------|--------------------------------------------|
| `formalization`  | Lean 4 formalization task                  |
| `infrastructure` | Definitions and basic lemmas               |
| `documentation`  | Improvements or additions to documentation |
| `ci`             | CI/CD workflow changes                     |
| `cleanup`        | Code cleanup and style fixes               |

### Paper labels

| Label         | Description                                                   |
|---------------|---------------------------------------------------------------|
| `0802.0447`   | arXiv:0802.0447 -- String order and symmetries (PRL 2008)     |
| `1606.00608`  | arXiv:1606.00608 -- MPDO RFP                                  |
| `1708.00029`  | arXiv:1708.00029 -- Periodic FT for MPS (De las Cuevas et al.)|
| `1804.04964`  | arXiv:1804.04964 -- FT for normal tensor networks             |
| `2011.12127`  | arXiv:2011.12127 -- RMP review (Cirac--Perez-Garcia--Schuch--Verstraete) |

### Topic labels

| Label               | Description                                                           |
|----------------------|-----------------------------------------------------------------------|
| `parent-hamiltonian` | Parent Hamiltonian theory for MPS (RMP IV.C)                          |
| `correlation-decay`  | Exponential decay of correlations in MPS                              |
| `symmetry-SPT`       | MPS symmetries, projective representations, and SPT classification    |
| `rfp-mpdo`           | Renormalization fixed points and MPDO theory                          |
| `algebraic-FT`       | Algebraic approach to Fundamental Theorem                             |
| `wolf-ch1`           | Wolf Lecture Notes -- Chapter 1: Deconstructing Quantum               |
| `wolf-ch2`           | Wolf Lecture Notes -- Chapter 2: Representations                      |
| `wolf-ch5`           | Wolf Lecture Notes -- Chapter 5: Schwarz Inequalities                 |
| `wolf-ch6`           | Wolf Lecture Notes -- Chapter 6: Spectral Properties                  |
| `wolf-ch7`           | Wolf Lecture Notes -- Chapter 7: Semigroup Structure                  |

### Workflow labels

| Label            | Description                                    |
|------------------|------------------------------------------------|
| `tracking`       | Tracking issue for a formalization area         |
| `blueprint-sync` | Blueprint out of sync with Lean code            |
| `automation`     | Automated documentation/sync PR                 |

### Standard GitHub labels

`bug`, `enhancement`, `good first issue`, `help wanted`, `question`,
`duplicate`, `invalid`, `wontfix`.

---

## 5. Review Checklist

Every PR touching Lean code should be reviewed against these criteria:

1. **Proof correctness** -- No unexplained `sorry`. No `axiom` unless discussed.
   Run `rg -n "sorry|axiom" <file>` to verify.

2. **Mathlib style** -- Follow the naming conventions in [naming.md](naming.md)
   and documentation standards in [doc.md](doc.md). See [pr-review.md](pr-review.md)
   for the full Mathlib review guide.

3. **Type safety** -- No universe mismatches, coercion problems, or unresolved
   metavariables.

4. **Performance** -- Avoid expensive tactics on large types (e.g., `decide` on
   `Fin 1000`). Watch for timeout-prone proof terms.

5. **Modularity** -- Are new lemmas general enough to be reused? Could any be
   upstreamed to Mathlib?

6. **Documentation** -- Every new `def` and major `theorem` must have a docstring.
   Module files should have a header comment with `## References` citing the
   relevant arXiv paper(s).

7. **Blueprint sync** -- If the PR formalizes a statement from the blueprint,
   add `\lean{LeanDeclName}` and `\leanok` tags to the corresponding
   `blueprint/src/chapter/*.tex` file.

---

## 6. Lean Code Style

This project follows Mathlib conventions with project-specific additions.

### Reference guides

- **Documentation style**: [doc.md](doc.md) -- module headers, docstrings,
  LaTeX in comments, sectioning comments.
- **Naming conventions**: [naming.md](naming.md) -- capitalization rules,
  symbol-to-name dictionary, variable conventions.
- **Review guide**: [pr-review.md](pr-review.md) -- detailed examples of
  style, documentation, location, and improvement considerations.

### Project-specific conventions

**Module header**: Every `.lean` file should start with a module docstring that
includes:

```lean
/-!
# Title

Summary of what this file contains.

## Main definitions / statements

- `FooBar` : description
- `fooBar_baz` : description

## References

- [arXiv:XXXX.XXXXX](https://arxiv.org/abs/XXXX.XXXXX) -- Author, *Title*
-/
```

**Docstrings**: Required on every `def`, `structure`, `class`, and significant
`theorem`. Encouraged on supporting lemmas. Use Markdown; refer to Lean
identifiers in backticks.

**Sectioning comments**: Use `/-! ### Section Title -/` to organize long files
into logical sections.

**Variable naming**: Follow the conventions in [naming.md](naming.md). For
this project specifically:
- `A`, `B` for MPS tensors
- `E` for transfer matrices / quantum channels
- `d` for physical dimension, `D` for bond dimension
- `N`, `L` for chain length

---

## 7. CI & Automation

The following workflows run automatically:

| Workflow | Trigger | What it does |
|----------|---------|-------------|
| **Lean CI** (`lean_action_ci.yml`) | Push to `main`, PRs touching `.lean`/`lakefile.toml`/`lean-toolchain` | Runs `lake build` with Mathlib cache |
| **Claude Code Review** (`claude-code-review.yml`) | PR opened/synced/reopened touching `.lean`, `.tex`, `lakefile.toml`, `lean-toolchain` | Automated review for sorrys, Mathlib style, type safety, performance, modularity, documentation |
| **Issue Tracker** (`tracking-issue-sync.yml`) | Issue closed/reopened; PR merged/opened | Reads sub-issue parent/child links to find the relevant tracking issue, refreshes the bullet-list mirror in the tracker body, posts progress comments on linked issues when PRs merge, scans merged PRs for follow-ups (deferred review feedback, new `sorry` markers, missing blueprint tags), creates follow-up issues with the `follow-up` label and **attaches them as sub-issues** of the relevant tracker, adds `all-resolved` when every sub-issue is closed |
| **Blueprint Lint** (`lint-blueprint.yml`) | PRs touching blueprint files | Validates LaTeX blueprint for broken labels and references |
| **Docs & Blueprint Sync** (`docs-blueprint-sync.lock.yml`) | Daily (weekdays) + manual dispatch | Detects stale documentation and opens a sync PR if needed |
| **Lean Audit** (`lean-audit.yml`) | On demand | Audits Lean code for style and correctness |
| **PR Cleanup** (`pr-cleanup.yml`) | AI-generated PR opened (`claude/*` or `codex/*` branches) | Normalizes title to `type(scope): desc`, restructures body to PR template, copies labels from linked issue, adds `Addresses #N` reference, comments on the issue |

### What CI checks before merge

- `lake build TNLean` must succeed (no type errors, no broken imports).
- No new `sorry` without explicit justification.
- Blueprint labels must resolve (no broken `\ref` or `\label`).
- Claude Code Review should not flag critical issues (proof correctness,
  type safety).
