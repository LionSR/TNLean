# Contributing to TNLean

This document codifies the conventions for pull requests, issues, code review,
Lean style, and CI automation used in the TNLean project.

> **Before you write code.** Unsolicited agent-generated pull requests from accounts with no prior contribution here are closed without review; please contribute by opening an issue and waiting for it to be assigned to you. Code contributions require working knowledge of quantum mechanics and tensor networks.
> Agent-assisted work carries disclosure and accountability requirements. Some subprojects such as `tenkz` are closed to outside contribution entirely. See
> [`.github/CONTRIBUTION_POLICY.md`](../.github/CONTRIBUTION_POLICY.md).
> The conventions below apply once you hold an assigned issue.

---

## 1. Pull Request Conventions

### Title format

Use mathlib-style conventional titles:

```
type(scope): short description
```

| Type       | When to use                                      |
|------------|--------------------------------------------------|
| `feat`     | New definition, lemma, theorem, or module         |
| `fix`      | Broken proof, wrong identifier, or wrong statement |
| `refactor` | Reorganization without changing mathematical content |
| `doc`      | Documentation or blueprint changes only           |
| `style`    | Naming, formatting, prose, or title cleanup       |
| `ci`       | CI workflow changes                               |
| `chore`    | Dependency bumps, linting, toolchain updates      |

**Scope** is a shortened module path: `MPS/Symmetry`, `Channel`, `blueprint+docgen`,
`MPS/Core`, etc. Omit the `TNLean/` prefix.

Examples:
- `feat(MPS/CanonicalForm): assemble cyclic sectors at a common blocking length`
- `doc(Wolf Chapter 6): add Lean tags for spectral theorems`
- `style(MPS/CanonicalForm): rewrite equal-case prose in MPS language`

### Body template

Every PR body must contain three sections:

```markdown
### Motivation
- Why this change is needed (1--3 bullets).
- For mathematical work, cite the paper theorem, blueprint entry, or issue
  that fixes the scope.
- For mathematical work whose source is in `blueprint/`, `Papers/`, or
  `Notes/`, give the source file path, line range,
  theorem/lemma/definition/equation label when available, and a short quotation
  of the source statement.

### Description
- What was changed: files added/modified, definitions introduced, lemmas proved.
- Use bullet points.
- State the mathematical content precisely enough for a reader who has not read
  the issue thread.
- When renaming a public declaration and intentionally omitting a
  `@[deprecated] alias` because the old name encodes misleading terminology,
  explicitly note: `No compatibility alias is provided — the old name encodes
  [term] (see docs/CONTRIBUTING.md Section Mathematical-language renames).`

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
| **Tracking Issue** | Umbrella issue tracking a group of sub-issues |

### Title format

Issue titles are plain mathematical or repository-maintenance titles, not
PR-title prefixes. Labels carry the type, topic, paper, chapter,
priority, and status metadata.

Use these forms:

| Issue kind | Title form |
|------------|------------|
| Overall tracker | `Tracking: <area>` |
| Formalization task | `<area>: <mathematical result or construction>` |
| Blueprint or documentation task | `<document area>: <mathematical documentation change>` |
| CI or repository maintenance | `<area>: <concrete maintenance task>` |
| Daily record | `<record type> -- <date>` |

Keep issue titles bracket-free. Use `Wolf Chapter 6: ...`, not `[Wolf Chapter 6] ...`.
Do not put `feat(...)`, `fix(...)`, `doc(...)`, or `formalization(...)` at
the start of an issue title. Put parent issue numbers, PR numbers, audit
filenames, and implementation notes in the body unless they are needed to
disambiguate the title.

### Formalization issues

Use a descriptive title that names the mathematical content:

```
MPS/Symmetry: twisted tensor and on-site symmetry
```

Label with **area** + **arXiv paper** + **topic** as applicable.

The body must identify the mathematical source precisely. Include the paper or
book citation and, when the source is in `blueprint/`, `Papers/`, or `Notes/`,
the repository file path, line range, theorem/lemma/definition/equation label
when available, and a short quotation of the source statement. Use a precise
paraphrase only when the source is not available as repository text. Avoid AI
vocabulary, software-process metaphors, and local shorthand when describing the
mathematics.

### Multi-part work

For work spanning multiple PRs, create an umbrella **tracking issue** and put
the part numbering in the body or in native GitHub sub-issue relations when it
is not needed to distinguish the mathematical statement:

```
RFP/MPDO: algebra structure and fusion isometries
RFP/MPDO: commuting parent Hamiltonians and decorrelation theorem
```

Attach child issues using GitHub's native **Sub-issues** panel so that each
child displays "Tracked by #N" in its sidebar. Do not mirror that relation with
Markdown tasklists or checkbox lists in the tracking issue body. If the tracking
template includes issue numbers in the body, attach those numbers through the
Sub-issues panel after creation and keep the body for mathematical scope,
sources, dependencies, and order.

Generated tracking issues should create sub-issues for the mathematical tasks.
Each sub-issue should carry its own source citation and precise statement.

### Tracking issues

Use the **Tracking Issue** template (`.github/ISSUE_TEMPLATE/tracking-issue.yml`).
Label with `tracking`. The `issue-automation` workflow reads the native
Sub-issues relation and will automatically:

- Post progress comments when sub-issues are closed or reopened.
- Post progress comments on linked issues when PRs are merged (what was done, what remains).
- Add the `all-resolved` label when every native sub-issue is complete.

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

2. **Mathlib style** -- Follow the naming conventions in
   [MATHLIB_naming.md](MATHLIB_naming.md) and documentation standards in
   [MATHLIB_doc.md](MATHLIB_doc.md). See [MATHLIB_pr-review.md](MATHLIB_pr-review.md)
   for the full Mathlib review guide. For renames that intentionally omit
   deprecated aliases under the mathematical-language exception, confirm the
   PR body states the reason (see [CONTRIBUTING.md Section Mathematical-language renames](#mathematical-language-renames)).

3. **Type safety** -- No universe mismatches, coercion problems, or unresolved
   metavariables.

4. **Performance** -- Avoid expensive tactics on large types (e.g., `decide` on
   `Fin 1000`). Watch for timeout-prone proof terms.

5. **Modularity** -- Are new lemmas general enough to be reused? Could any be
   upstreamed to Mathlib?

6. **Documentation** -- Every new `def` and major `theorem` must have a docstring.
   Module files should have a header comment with `## References` citing the
   relevant arXiv paper(s). Every new public predicate must add or update its
   entry in the [concept glossary](glossary.md), including its source, sanctioned
   bridges, and any conditional or missing equivalences.

7. **Blueprint sync** -- If the PR formalizes a statement from the blueprint,
   add `\lean{LeanDeclName}` and `\leanok` tags to the corresponding
   `blueprint/src/chapter/*.tex` file.

---

## 6. Lean Code Style

This project follows Mathlib conventions with project-specific additions.

### Reference guides

- **Documentation style**: [MATHLIB_doc.md](MATHLIB_doc.md) -- module headers, docstrings,
  LaTeX in comments, sectioning comments.
- **Naming conventions**: [MATHLIB_naming.md](MATHLIB_naming.md) -- capitalization rules,
  symbol-to-name dictionary, variable conventions.
- **Review guide**: [MATHLIB_pr-review.md](MATHLIB_pr-review.md) -- detailed examples of
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

**Variable naming**: Follow the conventions in [MATHLIB_naming.md](MATHLIB_naming.md). For
this project specifically:
- `A`, `B` for MPS tensors
- `E` for transfer matrices / quantum channels
- `d` for physical dimension, `D` for bond dimension
- `N`, `L` for chain length

### Mathematical-language renames

The standard Mathlib deprecation convention says renamed declarations should keep
a `@[deprecated] alias`.  When the **old name encodes misleading terminology** —
process jargon, project-internal shorthand, or non-mathematical phrasing — a clean
one-step rename without a deprecated alias is preferred.

#### When to skip a deprecated alias

Skip the alias when the old name contains a term that appears in, or is a
contextual variant of, the banned-vocabulary list in
[`docs/prose_style.md` Section 2](prose_style.md#2-banned-software-engineering-terms--replacements).
Apply context-qualified bans only in the stated context: for example, "Assembly"
is banned as a section or chapter title, but not when it is part of a standard
mathematical phrase.

Examples of terms that make an alias inappropriate in declaration names:

- exact entries or variants of process/software metaphors from the prose guide:
  `pipeline`, `package`, `scaffolding`/`scaffold`, `workflow`, `plumbing`,
  `boilerplate`, `glueLayer`, `reexport`
- additional project-internal cleanup terms with the same non-mathematical force:
  `raw`, `helper`, `wrapper`, `endpoint` when it means a proof milestone rather
  than a boundary point
- project-internal shorthand: `liveBlock`, `oneShot`, `deadProof`, `sourceAnchor`
- AI/LLM vocabulary in declaration names

Keep the `@[deprecated] alias` when the old name uses genuine mathematical language that
is merely imprecise or outdated (e.g., `transferMap` → `transferMatrix` when the object is
a matrix) — the old name is not misleading, just suboptimal.

#### What PRs must state

When a rename skips a deprecated alias under this exception, the PR body must explicitly say:

> **No compatibility alias is provided.** The old name encodes [misleading term]
> (see [`docs/CONTRIBUTING.md` Section Mathematical-language renames](CONTRIBUTING.md#mathematical-language-renames)).

This makes the exception visible to reviewers and prevents downstream users from
wondering whether the omission was an oversight.

#### Blueprint references

In the same PR, update every `\lean{OldName}` tag in `blueprint/src/` to
`\lean{NewName}`.  Run `leanblueprint checkdecls` to confirm no stale references
remain.

#### Migration within the project

Before deleting or renaming, search the project for call sites of the old name
(`rg -n "oldName" TNLean/`) and update them in the same PR.  If the old name
appears in a module docstring or comment, rewrite the surrounding prose to use
the new mathematical name.

---

## 7. CI & Automation

The following workflows run automatically:

| Workflow | Trigger | What it does |
|----------|---------|-------------|
| **Lean CI** (`pr-ci.yml`, `build` job) | Push to `main`, PRs touching `.lean`/`lakefile.toml`/`lean-toolchain` | Runs `lake build` with Mathlib cache |
| **PR Review** (`pr-review.yml`) | After a successful PR CI run | Automated review for sorrys, Mathlib style, type safety, performance, modularity, documentation, plus blueprint/prose review |
| **Issue Automation** (`issue-automation.yml`) | Issue opened/labeled/closed/reopened; PR opened/merged | Classifies new issues, posts Mathlib scouting reports, keeps tracking issues current (progress comments, sub-issue counts, `all-resolved` label — deterministic, no model), and scans merged PRs for follow-ups (deferred review feedback, new `sorry` markers, missing blueprint tags), filing them with the `follow-up` label |
| **Blueprint Lint** (`pr-ci.yml`, `blueprint` job) | PRs touching blueprint or Lean files | Validates LaTeX blueprint for broken labels and references |
| **Lean Module Policy** (`pr-ci.yml`, `file-length` job) | PRs and main pushes touching Lean policy paths | Blocks ordinary files above 1000 lines and new numbered-sequel production modules; validates exact import-only aggregator exemptions |
| **Import Completeness** (`import-completeness.yml`) | PRs and main pushes touching TNLean sources or generator files | Tests the generator and checks that every production module appears in the generated hierarchical import frontier |
| **Lean Linter-Warning Sweep** (`housekeeping.yml`, `linter-sweep` job) | Weekly + manual dispatch | Captures Lean compiler/linter warnings and uploads a report for maintainer triage |
| **Lean Linter-Warning Auto-Fix** (`lean-linter-warning-autofix.yml`) | Manual dispatch | Runs the warning sweep and can open a guarded Lean-only PR when explicitly requested |
| **Docs & Blueprint Sync** (`docs-blueprint-sync.lock.yml`) | Daily (weekdays) + manual dispatch | Detects stale documentation and opens a sync PR if needed |

### Generated import aggregators

`TNLean.lean` and the hierarchical directory aggregators are generated files;
never edit them by hand. After adding, moving, or removing a production Lean
module, run:

```bash
python3 scripts/generate_import_aggregators.py
python3 scripts/generate_import_aggregators.py --check
```

The first command updates the hierarchy. The second is the same deterministic
completeness check enforced by CI. `TNLean/Archive/` remains outside the
production manifest; see `docs/import_structure.md` for details.

### Splitting large Lean modules

Do not split a proof according to where editing happened to stop. A filename
such as `Recovery2.lean` or `Recovery3b.lean` hides the module's mathematical
role and is rejected for new tracked production files. Instead:

1. identify the mathematical responsibilities in the large module;
2. move repeated definitions, notation, and setup into a family `Basic.lean`;
3. give each proof module a concept name, for example
   `BoundaryRecovery.lean` or `OverlapInjectivity.lean`; and
4. if callers need one import, provide a concept-named import-only aggregator.

The numbered-file allowlist in `scripts/check_numbered_lean_files.py` records
legacy debt and may only shrink; pull-request CI compares it with the merge-base
allowlist and rejects additions. Numerals intrinsic to a mathematical object
(such as `ZMod2`) or to an explicitly cited source result require an exact,
documented semantic exception. Import-only aggregators can exceed the
line cap only when their exact path is passed to the size checker; the checker
validates that uncommented content contains imports and nothing else.

### What CI checks before merge

- `lake build TNLean` must succeed (no type errors, no broken imports).
- No new `sorry` without explicit justification.
- Blueprint labels must resolve (no broken `\ref` or `\label`).
- Claude Code Review should not flag critical issues (proof correctness,
  type safety).
