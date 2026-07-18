# Tactic Self-Improvement Loop

This document defines the process by which repeated proof patterns are
detected, recorded, and promoted into reusable lemmas, simp sets, and custom
tactics. The goal is that **proof text grows sublinearly with the mathematical
content**: a pattern paid for once should never be paid for a fourth time.

The process has two artifacts:

- **This document** — the process rules (stable).
- [`docs/tactic_patterns.md`](tactic_patterns.md) — the *pattern ledger*, a
  living registry of observed patterns and their status (updated continuously).

Promoted tactics live in the source tree:

- `TNLean/MPS/Tactic/Basic.lean` — MPS/channel/overlap-specific simp sets and
  tactic macros (`mpv_ext`, `block_words`, `transfer_simp`).
- `TNLean/Tactic/` — cross-cutting tactics not tied to MPS (create the
  directory when the first such tactic is promoted).

## The loop

Every proof-writing session (closing a `sorry`, adding a theorem, refactoring
a proof) follows this loop:

1. **Consult** — before writing a proof, skim the ledger's *promoted* section
   and use existing tactics/simp sets where they apply. Writing out by hand a
   pattern that already has a promoted tactic is a review-blocking style issue.
2. **Detect** — while writing, notice when you copy-paste or re-derive a
   tactic block you have seen before. Periodically (and in any PR that touches
   many proofs) run the scanner:

   ```bash
   python3 scripts/tactic_pattern_scan.py                 # default report
   python3 scripts/tactic_pattern_scan.py --min-count 5   # stricter
   ```

3. **Record** — add newly noticed repetition to the ledger as a *candidate*
   entry (see the entry format in `docs/tactic_patterns.md`). Recording is
   cheap and requires no design decision; do it in the same PR.
4. **Promote** — when a candidate meets the promotion criteria below, implement
   the abstraction, mark the ledger entry *promoted*, and link the declaration.
5. **Refactor** — rewrite the call sites the scanner found to use the
   abstraction, in the same PR as the promotion or an immediately-following
   `refactor(...)` PR. Record the net line delta in the ledger entry.
6. **Retire** — if a promoted tactic loses all call sites (e.g. the underlying
   API changed), mark it *retired* in the ledger and deprecate or delete it.

## Promotion criteria

Promote a candidate when **either**:

- it occurs **>= 3 times across >= 2 files** (rule of three), or
- it is **>= 5 lines and occurs >= 2 times** with more occurrences clearly
  coming (e.g. an in-progress multi-file development).

Below these thresholds, leave the entry as a candidate — premature
abstraction is its own maintenance cost.

## Choosing the abstraction

Prefer the weakest mechanism that removes the duplication, in this order:

1. **A lemma.** Most "repeated tactic blocks" are a missing lemma. If the
   block proves the same *statement shape* each time, state that shape once
   and `exact`/`apply` it. Scout Mathlib first (`exact?`, `rw?`, grep
   `.lake/packages/mathlib/Mathlib/`) — the lemma may already exist.
2. **A simp set** (`register_simp_attr`). When the block is a fixed list of
   rewrites (`simp only [a, b, c, ...]` repeated verbatim), tag the lemmas
   with a custom attribute and replace the list with the set. Existing sets:
   `mps_block_words`, `mps_transfer`.
3. **A macro** (`macro "name" : tactic => ...`). Thin sugar over a fixed
   tactic sequence. Cheap to write, transparent to review, easy to inline
   away if it ages badly.
4. **An elab tactic** (`elab "name" : tactic => ...`). Only when the pattern
   needs goal inspection or branching (like `mpv_ext`). These cost the most
   to review and maintain; the ledger entry must say why a macro is not
   enough.

## Design rules for promoted tactics

These extend the design notes in `TNLean/MPS/Tactic/Basic.lean`:

- **No search.** Promoted tactics normalize or discharge a *known* pattern.
  When the pattern does not apply they must fail fast or leave clear unsolved
  goals — never silently try alternatives. (Search belongs in interactive
  scouting with `exact?`/`apply?`, not in committed proofs.)
- **Docstring states the pattern.** Every promoted tactic's docstring shows
  the tactic block it replaces, so `grep` on the old pattern leads to the
  replacement.
- **Named per Mathlib conventions** (`docs/MATHLIB_naming.md`): tactics and
  simp attributes are `snake_case`; MPS-specific sets carry the `mps_` prefix.
- **One file per topic.** Keep MPS-specific tactics in `TNLean/MPS/Tactic/`,
  cross-cutting ones in `TNLean/Tactic/`; do not scatter `register_simp_attr`
  calls through content files.
- **Simp-set hygiene.** A lemma enters a custom simp set via
  `attribute [mps_foo] lemma_name` next to the lemma (or `@[mps_foo]` at the
  declaration), and the set's registration docstring lists its intended
  normal form.

## Scanner notes

`scripts/tactic_pattern_scan.py` is a heuristic line-based n-gram scanner,
not a Lean parser:

- It only sees lines starting with a known tactic keyword; extend its
  `TACTIC_HEADS` list when a promoted tactic introduces a new head symbol
  (e.g. `mpv_ext` is already listed).
- It excludes `Archive/` and `Scratch/`.
- Its ranking weight is `lines x occurrences` — an estimate of removable
  lines, not a proof of semantic equivalence. Always confirm that the
  occurrences really are the same pattern (same goal shape, not just the
  same text) before promoting.
- It is a reporting tool, not a lint gate: it never fails CI.

## Interaction with other rules

- Promotion refactors are `refactor(scope):` PRs (`docs/CONTRIBUTING.md`)
  and must not change theorem statements — only proof text.
- A promotion PR must keep `lake build` clean; there is no
  paper-realignment relaxation here since statements are untouched.
- Ledger updates (`docs/tactic_patterns.md`) do not require blueprint
  changes; the ledger is engineering metadata, not mathematics, and the
  prose rules of `docs/prose_style.md` do not apply to it.
