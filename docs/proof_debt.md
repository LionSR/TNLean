# Proof-Debt Reduction Loop

This document defines the weekly process by which structural proof debt —
the formalization analogue of tech debt — is detected, ranked, and removed.
It complements the tactic loop in
[`docs/tactic_development.md`](tactic_development.md): that loop targets
*repeated tactic text*; this one targets everything larger — duplicated
lemmas and structures, missing abstractions, file/module organization,
over-specialized statements, and dead weight.

The process has these artifacts:

- **This document** — the process rules (stable).
- [`docs/proof_debt_ledger.md`](proof_debt_ledger.md) — the *debt ledger*, a
  living ranked registry of open debts and their burn-down status (updated
  weekly), including the Metrics table the shrink rhythm ratchets down.
- `.claude/workflows/proof-debt-tournament.js` — the structural audit: ten
  independent finder lenses, adversarial evidence verification, and a
  three-judge ranking panel. Run it with the Workflow tool
  (`name: 'proof-debt-tournament'`).
- `.claude/workflows/proof-shrink-tournament.js` — the demolition audit:
  nine lenses hunting mathematically excessive code rankable by *net
  deletable lines* (`name: 'proof-shrink-tournament'`).
- `scripts/loc_report.py` — the deterministic size snapshot feeding the
  Metrics table.

## What counts as proof debt

Debt is anything that makes the *next* theorem more expensive than it should
be. The tournament's lens taxonomy doubles as the ledger's category set:

| Category | Meaning |
|----------|---------|
| `duplication` | The same lemma/def/structure re-stated or re-proved in several files |
| `architecture` | Directory/layering problems; filename-prefix pseudo-modules; orphan files |
| `abstraction-gap` | A missing general interface forcing per-case redevelopment |
| `proof-length` | Overlong proofs caused by missing helper lemmas or simp API |
| `tactic-infra` | Patterns past the rule of three not yet promoted (see tactic loop) |
| `api-design` | Core definitions lacking simp/ext lemmas; parallel variant predicates |
| `generality` | Special-case theorems where one general statement would serve |
| `hygiene` | Non-terminal `simp`, debug artifacts, set_option debris, stale TODOs |
| `naming-docs` | Systematic naming inconsistency; missing module docstrings |
| `dead-weight` | Unimported files, unused declarations, superseded developments |

## The weekly rhythm

Each week runs one **audit** and at least one **burn-down PR**:

1. **Audit (start of week).** Run the tournament workflow. It re-scans the
   repo, verifies its own findings adversarially, and returns a ranked top
   list. Refresh the ledger: add new debts, update evidence counts on open
   ones, retire debts whose evidence is gone.
2. **Pick.** Take the highest-ranked debt whose `first_week_pr` (recorded in
   the ledger) fits in one week. Skip a moonshot only in favor of the next
   item down, never in favor of nothing.
3. **Burn down.** One `refactor(scope):` PR scoped to that single debt item.
   Debt PRs follow the standard rules: minimal diffs, `lake build` clean, no
   unrelated changes. A debt PR must not change theorem statements unless
   the debt *is* statement-level (`generality`, `api-design`); statement
   changes follow the faithfulness rule in `CLAUDE.md` and, where a source
   paper is involved, the paper-realignment process.
4. **Record.** Update the ledger entry: status, PR link, net line delta.
   A debt is **burned down** when the duplication/gap it names is gone from
   the tree, not when a replacement merely exists alongside it.
5. **Feed the tactic loop.** Any `tactic-infra` findings go to
   [`docs/tactic_patterns.md`](tactic_patterns.md) as candidates and follow
   that loop's promotion criteria instead of the ledger.

Large debts (multi-week) get a tracking issue (`Tracking: <area>`, per
`docs/CONTRIBUTING.md`) and are burned down in weekly slices, each slice a
self-contained PR.

## The shrink rhythm

Structural clean-up alone tends to *add* code (bundling structures,
interfaces). The shrink rhythm is the counterweight: a standing mechanism
that removes code the mathematics and physics never needed — code generated
by the process of formalization (staged exploration, hand-mirroring,
forked variants, degenerate-case admission) rather than by the theorems.

1. **Measure (weekly, with the audit).** Run `python3 scripts/loc_report.py`
   and append the row to the ledger's Metrics table. The tracked quantities
   — total lines, cross-file duplicated windows, numbered-sequel files,
   cap-riding files, degenerate-case sites, sorries — must trend down or
   the trend gets an explanation in the ledger.
2. **Net-line discipline.** Every `refactor(scope):` PR states its net line
   delta in the body. Debt burn-down PRs should be net-negative; a
   net-positive refactor must say what future deletion it enables and cite
   the ledger entry that will collect it.
3. **Demolition audit (monthly, or after any large merge).** Run the
   `proof-shrink-tournament` workflow. It hunts nine excess classes —
   degenerate-case tax, superseded routes, subsumed special cases,
   scaffolding chains, mirrors, Mathlib shadows, dead weight, compressible
   proofs, parallel theories — verifies each candidate adversarially
   (safety: nothing blueprint-cited is lost; arithmetic: the net count
   survives recounting), and ranks by verified net deletable lines. Results
   land in the ledger's Demolition section.
4. **Deletion outranks abstraction.** When a ledger entry can be resolved
   either by abstracting the duplication or by deleting one side, prefer
   deletion: the general route stays, the superseded route goes, and the
   blueprint is updated to cite the survivor. Physically meaningless
   regimes (bond dimension 0, empty chains, dimension-0 physical space) are
   the canonical example — the cited papers assume nonzero parameters, so
   carrying those cases is *less* faithful, not more general.

## Ledger entry format

```markdown
## D<n>. <title>  —  <category>, impact <i>/10, effort <e>/10
- **Status**: open | in-progress (#PR) | burned-down (#PR, net -N lines) | retired
- **Evidence**: <quantified: files, counts, line refs — as verified, not as guessed>
- **Remediation**: <the refactor, 1-3 sentences>
- **First PR**: <the one-week slice that starts it>
```

Entries stay ranked: the ledger lists open debts in current tournament
order. Burned-down and retired entries move to the bottom section with
their outcome recorded, so the same debt is not re-proposed later.

## Rules

- **Evidence or it does not enter the ledger.** Every entry carries counts
  and file paths that were actually checked. The tournament's verification
  stage enforces this for tournament-sourced entries; hand-added entries
  meet the same bar.
- **Rank by compounding cost.** Breadth (files affected) and recurrence
  (every future proof pays it) outrank size. A 50-line annoyance touched
  weekly outranks a 1000-line file nobody edits.
- **Deletion is a first-class remediation.** For `dead-weight` and
  superseded developments, prefer deleting over maintaining. Git history
  preserves everything; `Archive/` is for results with historical value,
  not a landfill.
- **No debt PRs that add debt.** A burn-down PR that leaves a transitional
  duplicate ("old and new API side by side") must carry the tracking issue
  that removes the old one, and the ledger entry stays in-progress until it
  is gone.
