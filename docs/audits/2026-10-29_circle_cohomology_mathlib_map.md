# Circle coefficient comparison on Mathlib objects

Issue: #8318. Source: arXiv:2502.20257, lines 1927–1931, with the existing
finite-discrete clarification in
`docs/paper-gaps/fbc25_circle_complex_units_cohomology.tex`.

The circle coefficient object is now literally
`Rep.ofMulDistribMulAction G Circle`. The existing scoped trivial action is
generalized from complex units to a commutative coefficient group, so both
coefficient objects use the same convention. Mathlib has no canonical global
trivial action; keeping this convention scoped permits nontrivial actions.

Deleted, without compatibility aliases:

- `Circle.trivialMulDistribMulAction`; replaced by the common scoped action.
- `circleH2Representation`; replaced by Mathlib's representation.
- `circleH2ToComplexUnitsH2` and `complexUnitsH2ToCircleH2`; replaced directly by
  `groupCohomology.map` along the existing coefficient homomorphisms.
- `circleH2EquivComplexUnitsH2`; replaced by
  `circleToComplexUnits_map_bijective`, a theorem about the induced Mathlib map.

The left-inverse, injectivity and surjectivity theorems are renamed around
the actual maps. Their mathematical arguments are retained. No hypotheses
are added; injectivity holds for every group and surjectivity uses finiteness.
The Blueprint and gap note cite the direct-map statements.

Validation: exact pinned Mathlib source inspected, stale-name census, source
formatting, tactic-pattern scan, Blueprint declaration-source scan and
`git diff --check`. No new tactic pattern is introduced by this restatement.
The hosted build of the pull request head verifies the restated declarations;
the Blueprint entry and its proof keep their formalized status.

## Current-main reconciliation

The original head `9d36dabe23565f51100687218490af20e8151870` passed the hosted
full build and strict checks for both changed algebra modules in job
123421331593; the log records that exact `PR_HEAD_SHA`. No source repair was
needed. The merge with main `c7d2992c89c16d85237e18557ff292979b3a67b4` retains
both algebra source files byte-for-byte and carries the declaration tags to
the relocated circle-coefficient entry in `ch29_mpu_cocycles.tex`. The former
chapter retains main's contents exactly. Native import, declaration-sync,
role, prose, formatting and whitespace checks pass. The hosted build and
strict checks of the refreshed combined head also pass, so the Blueprint entry
keeps its formalized status.
