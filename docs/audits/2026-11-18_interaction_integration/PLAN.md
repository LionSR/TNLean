# Canonical Interaction integration: source scaffold, not merge-ready

Start from 10881 fa9a40e2 (including range restorations and fixtures), merge exact
main 7376dab08421ab99afcc5373be11104c76cc8a50. This main commit is the #10816
merge and is an ancestor of this branch. The resulting baseline is 34f0770445.
Do not use a PR's old base.sha as the current main revision.

The existing review/evidence branch contains the complete 233 paths, 68 overlaps,
46 conflicts and explicit 224-file semantic-review gap. This source branch does
not claim that migration has been fully reviewed or compiled.

## Current implementation boundary

Four shared owner files have been ported from the read-only merge result:
- TNLean/Lattice/LocalHamiltonian.lean
- TNLean/MPS/AreaLaw/Hamiltonian.lean
- TNLean/MPS/AreaLaw/ComponentReduction.lean
- TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean

The three bundled structures are removed; no old-owner alias, operator alias,
or second support/evolution/ground-state implementation is introduced. QIC's
existing Interaction is the sole object. This is an intentionally incomplete
source checkpoint: 229 delta files have NOT been ported. Existing consumers and
fixtures still referring to removed APIs must be migrated before the repository
can compile. Do not interpret a clean git status/diff check as Lean validation.

The auto-merged rectangular projector-gap theorem retained old call arity and
.operator references despite having no textual conflict. These were repaired
here, preserving the broad PSD/member signature and dropping the obsolete norm
parameter, which is not used by this coordinate-transport proof.

## Shared API contract

1. ChainInteraction L q R, DomainInteraction Lambda q R, and PlaneInteraction
   Lambda q R are QIC abbreviations of Interaction. J is a bound parameter of
   statements, not part of an object's type. term/mem/hamiltonian replace
   term/supported/operator. No compatibility implementations are authorized.
2. Geometry/placement conversions do not receive norm or gap assumptions.
   Hermiticity and norm preservation are proved separately where needed.
   DomainInteraction.toChain inserts zero across gaps; norm_toChain_term_le
   still explicitly uses J>=0 for these added zeros, as the prior conversion
   required. Do not impose that premise on toChain itself or unrelated APIs.
3. RectangleInteraction.toAreaLawHamiltonian takes only Phi and returns the
   canonical PlaneInteraction. isHermitian_toAreaLawHamiltonian_term holds
   because terms are Hermitian parts. norm_toAreaLawHamiltonian_term_le takes
   the original term bound and preserves arbitrary J, including empty domains.
4. toAreaLawHamiltonian_hamiltonian takes only total-Hermitian hH. The broad
   projectorGap_toAreaLawHamiltonian API is:
   Phi -> hH -> norm Omega = 1 -> projector-PSD gap -> groundSpace membership,
   returning transported norm/PSD/membership for every real Delta. No termwise
   Hermitian, positive gap, singleton, norm-bound, or nonempty premise is added.
5. IsGapped/singleton bridge statements may remain separately named stronger
   results on the SAME object. Do not replace broad public statements with them.
   Tail/area-law conclusions that mathematically require positive Delta retain
   their actual positive-Delta premise; this is not a blanket generalization.

## Exclusive work allocation

allocation.tsv and lane lists partition all 233 delta paths without overlap.
A nonconflict path means only no git content conflict, NOT semantic clearance.

- Shared lane (this branch owner): 6 paths, no text conflicts. Four implemented
  above; the two remaining Lattice paths stay pending. Other lanes must not
  rewrite these owners. Request an explicit API adjustment if necessary.
- MPS lane: 86 paths; 68 text-nonconflict and 18 conflicting. Own ChainInteraction
  consumers, ThreeWaySplitting broad PSD/member transport, algorithms and MPS
  viable-space wrappers. Preserve the positive-gap premises only where needed.
- PEPS lane: 107 paths; 81 text-nonconflict and 26 conflicting. Own plane/range
  consumers, IsRangeSquareGroundState, square/pinned zero-floor and box entropy.
  Preserve arbitrary Delta/J, empty physical regions and only necessary total
  Hermiticity; do not reinstate singleton assumptions for zero-gap fixtures.
- Documentation lane: 34 paths; 32 text-nonconflict and 2 conflicting. Wait for
  stable signatures before updating Blueprint owners/uses. Keep nonpositive-gap
  scope and the distinction between positive-size IntRect and empty intersection.

The MPS/PEPS nonconflict lists are safe FILE BOUNDARIES for independent work,
not permission to take the external version wholesale. Each worker starts at
this exact source checkpoint, ports only its assigned list, and reports scoped
checks and unresolved assumptions. Do not build shared caches concurrently.

## Fixture ownership outside the 233 delta paths

MPS lane owns scripts/ground_state_gap_scope_regression.lean.
PEPS lane owns scripts/range_square_zero_gap_regression.lean,
scripts/box_supremum_zero_gap_regression.lean and scripts/generic_gap_boundary_regression.lean.
Shared lane owns scripts/zero_gap_tn_wrappers_regression.lean after both API lanes
settle, because it combines rectangle and ThreeWaySplitting assertions.
Retain existing selector coverage. Tests may construct zero Interaction values
using the canonical constructor; do not restore removed production zero owners.

## Integration and validation order

1. Complete the shared contract and narrow owner checks where cached dependencies
   permit; otherwise report the exact missing closure, never cold-build all TN.
2. Port MPS and PEPS consumers on disjoint file sets. Treat range-square,
   ThreeWaySplitting, rectangular coordinate transport, zero-floor and box entropy
   as mandatory scope checks, with q=2, Delta=0 degenerate fixtures retained.
3. Port the strip-count proof refactor once (MPS owns StripGeometry); do not mix
   it with a new crossingTerms owner or an unrelated proof rewrite.
4. Migrate the five existing fixtures, then synchronize docs and Blueprint.
5. Compile affected owners/consumers/fixtures with exact source/pin, then aggregate
   checks on a coherent warmed tree. Until then this checkpoint is not buildable
   and must not be merged or used as passing evidence for either existing PR.

No implementation files or caches in other worktrees have been changed.
No build, strict check, axiom audit, or external PR mutation was run in this step.
