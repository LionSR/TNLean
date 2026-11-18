# MPS canonical Interaction source checkpoint

This checkpoint is not merge-ready. No Lean compilation or strict Lean run has
been performed for this lane at the new pin. Static checks are not mathematical
acceptance, and a conflict-free merge is not a proof of equivalent scope.

## Exact inputs and commits

- Base: `b2c72008326f3166d3bcdc9e79013443142b0aa8`.
- QIC: `729428582b78ab7529b3796099193649f947354a` (unchanged).
- Independent branch: `refactor/mps-canonical-interaction`.
- Production migration: `54ab66ae0` (85 allocated files).
- Existing MPS regression migration: `42229ed94` (one file).
- Shared owner input: `b992c791dc35580cb84e1161150b98b9963284bb`,
  applied separately as `81e70a7d4`; this changes only MarginalTails and
  ProductForm. It is the shared author's commit, not a local owner rewrite.
- Static check source snapshot: `81e70a7d4`.

An integrator who already has the shared changes should pick only the two MPS
commits and this evidence commit. Do not apply the shared change twice.

All 86 allocated MPS files were processed. Hastings/AreaLaw.lean remains
byte-identical to the base: its factorization result is independent of a
Hamiltonian input. The other 85 files and the existing MPS fixture were ported.
No PEPS source, shared owner implementation, CI selector or other fixture was
edited by this lane. The two shared files above were cherry-picked unchanged.

## Scope-sensitive decisions

The external migration was used as a porting candidate, not accepted wholesale.
All 18 MPS textual conflicts were resolved; broad conclusions from the baseline
were retained where the candidate attempted to reintroduce uniqueness inputs.

- OverlapEnergy takes total Hamiltonian Hermiticity, a term norm budget,
  normalization and canonical membership. It does not require termwise
  Hermiticity or a singleton ground space. Constants remain 8 L delta and 8 c.
- BoundaryGap retains arbitrary real gap, projector positivity and canonical
  membership. It still requires a positive chain length and local dimension
  at least two. Its norm argument needs no Hermiticity premise.
- ThreeWaySplitting transports normalization, projector positivity and membership
  for every gap. Pure algebraic transport receives no extra Hermiticity input.
- RangeOneSupport and leftObjective_norm_bounds use the term norm budget alone;
  unnecessary Hermiticity parameters in the candidate were removed with callers.
- Positive-gap wrappers retain their existing positive-gap and uniqueness inputs,
  using the canonical bridge only when they actually need the broader APIs.
- Constructors, doubled interactions, swaps and domain conversions use canonical
  Interaction objects, with separate Hermiticity and norm estimates. Geometry
  does not receive newly bundled energy or gap data.
- No new nonnegative-J, nonempty or nonzero-dimension premise was introduced by
  the scoped source scan. Token counts in files.json are a screening measure,
  not a substitute for reviewing complete quantified statements.

The 86-path allocation plus the fixture are recorded individually in files.json,
including source hashes, changed status, static review depth and explicit unrun
Lean status. Only the named sensitive statements received targeted proof/scope
inspection; the ledger does not assert exhaustive independent semantic review
of every higher-level wrapper.

## Fixture acceptance

Read the complete acceptance document on documentation branch
`codex/interaction-docs-b2c72008`, file
`docs/audits/2026-11-18_interaction_docs/FIXTURE_ACCEPTANCE.md`.
The owned ground_state_gap_scope_regression keeps the two-dimensional zero
matrix, normalized vector, non-singleton proof and actual one-site q=2 chain
calls to OverlapEnergy and BoundaryGap. Its square-ground-state witness remains.
The zero chain now uses the canonical term/mem constructor, not a restored owner.
The four other mandatory fixtures are unchanged here and remain assigned to the
PEPS/shared lanes. Their full compilation is not claimed by this checkpoint.

## Verification and limitations

checks.json records exact static commands, exit codes and wall times. Import
layers, generated aggregators, diff whitespace and proof-integrity token checks
passed. The allocated source scan found no remaining old owner names outside
imports, no conflict markers and no source lines over 100 columns.

The isolated checkout has no .lake directory and no matching QIC729 cache.
The preserved warm checkout is still on QIC1af32a2b. Its artifacts and historical
verification are deliberately not counted here. No cold dependency build was
started with approximately 2.1 GiB free disk. Shared-lane reported overlay
verification is separate evidence and does not validate these 85 consumers.

Remaining gates: provision a matching new-pin overlay or cache; compile narrow
norm/constructor and broad-gap clusters, then all allocated downstream consumers;
compile the complete migrated fixture together with the PEPS owner changes;
run strict checks and final selector tests on the combined tree; review the full
higher-level API/caller delta. In particular, caller elaboration and namespace
lookup after moving methods to ManyBody remain unverified. Keep this source
checkpoint out of either existing PR until those integration gates are met.
