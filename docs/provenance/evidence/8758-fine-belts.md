# Sparse belts in actual dyadic layers

Actual fine-cell subdivision, finite averaging of two coordinate residue
classes, and the two integer-floor bounds give

\[
|\mathcal B_k|\le64(2C+1)^2\,|\partial_\Lambda A|\,2^{-\delta_0k/2}.
\]

The estimate is uniform in the domain, cut, origin and nonnegative scale,
including empty layers. It is the estimate `geometry:belt-count` in OpenAI,
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 11, `10-geometry.tex`, lines 200–237, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The 21 original declarations comprise six definitions and fifteen theorems
in `DyadicRefinement.lean`, `DyadicScales.lean` and `FineBelts.lean`.
No upstream Lean proof text is reused.

The exact verified source is
`fc87534a119694461e9c3d3c37a7bfa1bf3ea960`, published in
[TNLean #8837](https://github.com/LionSR/TNLean/pull/8837).
Its three mathematical modules are byte-identical to their initial source
commit `e20ae078889fb8c447879f28b5b55b625c84a689`.

## Canonical local verification

Both commands ran consecutively through the worktree's
`scripts/lake_build_locked.sh --` under the shared repository lock, reusing
the existing warmed cache and pinned prebuilt Mathlib artifacts. No Mathlib
source rebuild or local full-library build was performed. Lock acquisition
waited without consuming CPU; after the server restart, only the idle orphaned
waiter was replaced, before it had started a child build.

| Check | Command | Result | Elapsed seconds |
|---|---|---|---|
| Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Exit 0 | 14.644 |
| Imported-declaration audit | `lake env lean docs/provenance/evidence/8758-fine-belts-axioms.lean` | Exit 0 | 3.351 |

The three leaf modules compiled in 4.7, 4.8 and 4.9 seconds respectively,
without warnings. The audit prints all 21 exact imported names; every reported
axiom belongs to `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorryAx`, additional axiom or prohibited proof mechanism in this contribution.

Committed evidence logs and SHA256 hashes:

- `8758-fine-belts-build.log`:
  `d88ead29e8941d88736f791287c58c3d30b4d2a7bd1afe9d32be00add50c8c30`.
- `8758-fine-belts-axioms.log`:
  `d147edf52795e3911c08b4990799c455dba500af44ca3595927908cf31b80451`.

Each log records the command, exact source revision, elapsed time and exit
code. Captured output has trailing whitespace removed; no diagnostic or
dependency output is replaced. The provenance update changes only the new
21 rows' status, declared-name status and verification fields. The previous
35 geometry row texts and all prior evidence remain unchanged. Complete
current-policy validation, including the pinned source, license and notices,
passes all 182 entries in this tree.

## Full-library and blueprint verification

All nine checks passed on the exact source head. The
[workflow](https://github.com/LionSR/TNLean/actions/runs/37642857977)
includes the successful
[full Lean build](https://github.com/LionSR/TNLean/actions/runs/37642857977/job/112868120210)
and
[blueprint rendering](https://github.com/LionSR/TNLean/actions/runs/37642857977/job/112868120223).
The build also runs `lake exe checkdecls blueprint/lean_decls` against the
compiled declarations. Source synchronization reports 20,136 distinct
references and 20,130 theorem-like entries. Generated imports, provenance,
module policies and changed-module compilation-time checks passed.

The later scale asymptotics and polynomial absorption are separate follow-ups.
Primary tiles, contacts, repairs, birth separation and the full two-family
construction remain open, as do both manuscript headline theorems.
