# Contributing to MPSLean

This document codifies the conventions for pull requests, issues, code review,
Lean style, and CI automation used in the MPSLean project.

---

## 1. Pull Request Conventions

### Title format

Use **conventional-commit** style for pull requests:

```
type(scope): short description
```

| Type       | When to use                                      |
|------------|--------------------------------------------------|
| `feat`     | New definition, lemma, theorem, or module         |
| `fix`      | Bug fix (broken proof, wrong identifier, etc.)    |
| `refactor` | Restructuring without changing API surface        |
| `doc`      | Documentation or blueprint changes only           |
| `style`    | Formatting, naming, or prose cleanup              |
| `ci`       | CI/CD workflow changes                            |
| `chore`    | Dependency bumps, linting, toolchain updates      |

**Scope** is a shortened module path: `MPS/Symmetry`, `Channel`, `blueprint+docgen`,
`MPS/Core`, etc. Omit the `TNLean/` prefix.

The description should be short, lower-case except for mathematical names, and
written in ordinary mathematical language. Avoid bracket prefixes, bot markers,
and process shorthand such as "endpoint", "wrapper", "package", "live block",
"one-shot", or "bookkeeping" when a mathematical description is available.

Examples:
- `feat(MPS/Symmetry): add twistedTensor as MonoidHom`
- `fix(blueprint+docgen): resolve broken labels and malformed docstring table`
- `refactor(MPS): move Correlations.lean from ParentHamiltonian/ to Core/`
- `doc(MPS/CanonicalForm): rewrite equal-case prose in MPS language`

### Body template

Every PR body must contain three sections:

```markdown
### Motivation
- Why this change is needed (1--3 bullets).
- For mathematical work, cite the paper theorem, blueprint entry, or issue
  that fixes the scope.

### Description
- What was changed: files added/modified, definitions introduced, lemmas proved.
- Use bullet points.
- State the mathematical content precisely enough for a reader who has not read
  the issue thread.

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

### Title format

Issue titles do **not** use conventional-commit prefixes such as `feat(...)` or
bracket prefixes such as `[Wolf Ch6]`. Use a plain mathematical title that says
what theorem, construction, chapter, or record the issue concerns.

This follows the practice used in the Lean/mathlib community: issue titles are
short mathematical or tooling phrases, while labels carry issue type and topic
metadata. For example, mathlib issue titles include phrases such as
`Rename Counterexamples/OrderedCancelAddCommMonoidWithBounds.lean`,
`Tracking issue: indentation linter enhancements`, and
`Kernel type checking performance depends on lexicographic ordering of universe
variables`; labels such as `enhancement`, `t-meta`, `t-linter`, and
`good first issue` carry the classification.

| Issue kind | Title format | Example |
|------------|--------------|---------|
| Overall tracker | `Tracking: <area>` | `Tracking: Wolf lecture notes on quantum channels` |
| Chapter or paper tracker | `Tracking: <paper/chapter/topic>` | `Tracking: Wolf Ch6 spectral properties` |
| Formalization task | `<area>: <mathematical result or construction>` | `MPS/CanonicalForm: assemble cyclic sectors at a common blocking length` |
| Blueprint or documentation task | `<document area>: <mathematical documentation change>` | `Blueprint Ch6: add Lean tags for Wolf spectral theorems` |
| CI or repository maintenance | `<area>: <concrete maintenance task>` | `CI: repair blueprint declaration check` |
| Daily record | `<record type> -- <date>` | `Daily Standup -- 2026-04-22` |

Rules:

- Start every overall tracker with `Tracking:`.
- Keep titles bracket-free. Brackets can leak into generated branch names and
  break PR workflows.
- Put parent issue numbers, PR numbers, audit filenames, and implementation
  notes in the body unless they are essential to disambiguate the title.
- Put type, topic, paper, chapter, and priority metadata in labels and
  sub-issue relations rather than encoding all of it in the title.
- Use the terminology of the relevant literature: blocked tensors, physical
  words, sector decompositions, zero-tail terms, transfer maps, fixed-point
  algebras, gauge equivalence, and finite-length span equality.
- Avoid titles that sound like internal task management or software automation.
  For example, prefer `Prove equality of the blocked MPS under iterated-blocking
  relabelling of physical indices` to `Prove physical-label compatibility
  between canonical blocked live tensor and relabeled one-shot live blocks`.

### Issue templates

Three issue templates are available in `.github/ISSUE_TEMPLATE/`:

| Template | When to use |
|----------|-------------|
| **Formalization Task** | A specific theorem, definition, or lemma to formalize |
| **Bug Report** | Broken proof, type error, sorry regression, CI failure |
| **Tracking Issue** | Umbrella issue tracking a group of sub-issues |

### Formalization issues

Use a descriptive title that names the mathematical content:

```
Symmetry/SPT 3/6 Definitions: twisted tensor and on-site symmetry
```

Label with **area** + **arXiv paper** + **topic** as applicable.

The body must identify the mathematical source precisely. Include the paper or
book citation, the theorem/lemma/definition label when available, the repository
file path and line number when the source is in `blueprint/`, `Papers/`, or
`Notes/`, and either a short quotation or a precise paraphrase of the claim.
Avoid AI vocabulary, software-process metaphors, and local shorthand when
describing the mathematics.

### Scientific prose in issues and PRs

Issue titles, tracking issues, sub-issues, PR descriptions, and tracking
comments should read like working mathematical notes, not administrative reports.
Use the vocabulary of tensor networks, matrix product states, quantum channels,
operator algebras, and the relevant source text. For example, say "formalize
the peripheral spectral decomposition in Wolf Chapter 6" rather than "organize
the remaining items."

Avoid AI or process slang in public mathematical discussion: "agent", "bot", "auto-generated",
"AI-generated", "prompt", "handoff", "nit", "cleanup pass", and similar phrases
should not appear unless the issue is explicitly about CI or automation. When a
tracking issue covers a source such as Wolf's lecture notes, state the
mathematical scope, chapter structure, dependencies, and expected formalization
outcome in ordinary scientific prose.

### References for formalization work

Before drafting a formalization issue, sub-issue, tracking issue, or PR
description, read the relevant mathematical source. When the work corresponds
to the blueprint or another LaTeX source, point to that source directly and
include all available references:

- the source file path;
- the relevant line number or narrow line range;
- the LaTeX label, theorem name, or proposition number;
- a short quotation of the mathematical statement or proof step being formalized.

For Wolf lecture-note tracking, use the convention at three levels. The
overall tracking issue should have the chapter tracking issues as its sub-issues. Each
chapter tracking issue should identify the chapter-level source material and list
the theorem-level formalization issues. Each theorem-level sub-issue should
identify the precise theorem, proposition, lemma, definition, or proof segment
it formalizes. If the LaTeX source has not yet been written or does not contain
the result, say that explicitly and cite the paper or lecture-note location
instead.

### Multi-part work

For work spanning multiple PRs, use the `Area K/N: title` pattern and create
an umbrella **tracking issue**:

```
RFP/MPDO 1/5 Pure-state RFP: definitions, ZCL <=> E^2=E, structural form
RFP/MPDO 2/5 Commuting parent Hamiltonians and decorrelation theorem
...
```

The tracking issue should use GitHub's native **Sub-issues** relation for its
child issues. Do not encode parent-child structure as Markdown checkbox lists;
those lists do not give the same issue hierarchy and are easy to let drift from
the true issue state.

Use the issue body for mathematical scope, references in the source text, dependencies, and
the intended order of attack. Keep the child issue list itself in the native
Sub-issues panel.

Generated tracking issues should create sub-issues for the mathematical tasks
rather than using Markdown task lists as the only record of work. Each sub-issue
should carry its own source citation and precise statement.

### Tracking issues

Use the **Tracking Issue** template (`.github/ISSUE_TEMPLATE/tracking-issue.yml`).
Label with `tracking`. Add child issues through GitHub's native Sub-issues UI
or API. The `tracking-issue-sync` workflow will automatically:

- Post progress comments on linked issues when PRs are merged (what was done, what remains).
- Add the `all-resolved` label when every task is complete.

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
topics that do not determine a single concrete issue (e.g., "Should MPDO live
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
| `wolf-ch3`           | Wolf Lecture Notes -- Chapter 3: Positive but not completely positive maps |
| `wolf-ch4`           | Wolf Lecture Notes -- Chapter 4: Convex structure                     |
| `wolf-ch5`           | Wolf Lecture Notes -- Chapter 5: Schwarz Inequalities                 |
| `wolf-ch6`           | Wolf Lecture Notes -- Chapter 6: Spectral Properties                  |
| `wolf-ch7`           | Wolf Lecture Notes -- Chapter 7: Semigroup Structure                  |

### Workflow labels

| Label             | Description                                    |
|-------------------|------------------------------------------------|
| `tracking`        | Tracking issue for a formalization area        |
| `blueprint-sync`  | Blueprint out of sync with Lean code           |
| `automation`      | Automated documentation/sync PR                |
| `scout`           | Issue-side request for a Mathlib scouting report |
| `auto-fix-claude` | PR-only: enable review-comment fixes           |
| `auto-fix-codex`  | PR-only: opt into alternate auto-fix workflows |

**General rule.** Workflow-control labels belong on the artifact whose workflow
they control. Pull-request automation labels should be applied to pull requests,
not issues.

**TNLean labels.** The `auto-fix-claude` and `auto-fix-codex` labels control
TNLean pull-request workflows. Do not apply them to issues; they do not trigger
issue-side automation here. The `scout` label belongs on issues and is
reserved for maintainer-reviewed requests for a Mathlib scouting report.

See [ci-automation.md](ci-automation.md#auto-fix-labels-are-pr-only) for the
issue-started workflow behavior that creates pull requests from trusted issue
events.

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
| **Issue Classification** (`issue-classification.yml`) | Human-authored issue opened | Applies label taxonomy for repository members; records preliminary labels for outside reports; identifies missing source or dependency information; posts a concise next-step comment |
| **Claude Code Review** (`claude-code-review.yml`) | PR opened/synced/reopened touching `.lean`, `.tex`, `lakefile.toml`, `lean-toolchain` | Automated review for sorrys, Mathlib style, type safety, performance, modularity, documentation |
| **Issue Tracker** (`tracking-issue-sync.yml`) | Issue closed/reopened; PR merged/opened; review submitted | Tracks native sub-issue state, posts progress comments on linked issues when PRs merge, scans merged PRs for follow-ups (deferred review feedback, new `sorry` markers, missing blueprint tags), creates follow-up issues with `follow-up` label, adds `all-resolved` when all sub-issues are complete |
| **Blueprint Lint** (`lint-blueprint.yml`) | PRs touching blueprint files | Validates LaTeX blueprint for broken labels and references |
| **Docs & Blueprint Sync** (`docs-blueprint-sync.lock.yml`) | Daily (weekdays) + manual dispatch | Detects stale documentation and opens a sync PR if needed |
| **Lean Audit** (`lean-audit.yml`) | On demand | Audits Lean code for style and correctness |
| **PR Cleanup** (`pr-cleanup.yml`) | PR opened from a `claude/*` or `codex/*` branch | Normalizes title to `type(scope): desc`, restructures body to PR template, copies labels from linked issue, adds `Addresses #N` reference, comments on the issue |

### What CI checks before merge

- `lake build TNLean` must succeed (no type errors, no broken imports).
- No new `sorry` without explicit justification.
- Blueprint labels must resolve (no broken `\ref` or `\label`).
- Claude Code Review should not flag critical issues (proof correctness,
  type safety).
