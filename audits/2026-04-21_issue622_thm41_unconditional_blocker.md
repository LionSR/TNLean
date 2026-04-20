# Issue #622 blocker audit — unconditional Thm. 4.1

Date: 2026-04-21
Branch: `feat/622-thm41-unconditional`
Target file: `TNLean/MPS/Periodic/Symmetry.lean`

## Goal

Remove at least one of the conditional hypotheses

- `MPSTensor.PRefinementCanonicalization`
- `MPSTensor.PRefinementInverseCanonicalization`

from Theorem 4.1 in `TNLean/MPS/Periodic/Symmetry.lean`, ideally making
`MPSTensor.thm_4_1_p_refinement` unconditional.

## Current forward-stage state on `main`

The first three forward steps are already formalized by
`MPSTensor.pRefinementCanonicalization_pullback`:

1. from `IsPRefinable B p`, choose a witness `(A, W)`;
2. form the pullback tensor
   `C τ := ∑ σ, W τ σ • B σ`;
3. prove both
   - `transferMap C = transferMap B`, and
   - `SameMPV C (blockTensor A p)`.

So the remaining work is exactly the paper's second stage: turn this blocked
`SameMPV` relation into a left-canonical root witness whose `p`-blocked transfer
map is `transferMap B`.

## Why the forward direction is still blocked

There are **two distinct missing bridges**.

### 1. The equal-case periodic FT is still not available unconditionally

The natural next step is to apply the periodic equal-case fundamental theorem to
`C` and `blockTensor A p`. However the current repository surface is still:

- `MPSTensor.PeriodicEqualCaseFT` in
  `TNLean/MPS/Periodic/Symmetry.lean` — an abstract `Prop` hypothesis;
- `MPSTensor.fundamentalTheorem_periodic_equalCase` in
  `TNLean/MPS/Periodic/FundamentalTheorem.lean` — a **conditional** theorem
  requiring both
  - `PeriodicOverlapHypothesis`, and
  - the per-block power-equality hypothesis `hPowEq`.

Those hypotheses are not derivable here from the current library because the
underlying overlap infrastructure in `TNLean/MPS/Periodic/Overlap.lean` is still
admitted. In particular, the current `periodicOverlapDichotomy` proof remains
blocked by the sector-match transport chain.

Relevant missing declarations in `TNLean/MPS/Periodic/Overlap.lean`:

- `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp`
- `exists_sector_match_of_gaugePhaseEquiv`
- `periodicOverlapDichotomy`

So there is not yet an unconditional theorem in the repo that turns
`SameMPV C (blockTensor A p)` plus irreducible-form hypotheses into a blocked
`ZGaugeEquiv` witness.

### 2. Even granting blocked `Z`-gauge data, the repo still lacks the root-reconstruction step

The paper's proof does not stop at a blocked `Z`-gauge equivalence. One must
**distribute the blocked `Z`-gauge back to a root tensor** `A'` so that
`blockTensor A' p = C` (or at least enough to conclude
`transferMap B = transferMap (blockTensor A' p)` with `A'` left-canonical).

That blocked-to-unblocked transport is precisely the infrastructure still marked
as missing in `TNLean/MPS/Periodic/Overlap.lean`:

- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`
- `repeatedBlocks_of_blockedSectorGaugePhase`

The accompanying file `TNLean/MPS/Periodic/CornerTransition.lean` explicitly
states that the ambient staircase tensors are available there, but that the
identification with the compressed blocked-sector tensors through the compression
isometries `φ k` must be supplied by the missing Tier-A bridges in
`Overlap.lean`.

So the key Eq. A.8 / A.14–A.18 transport step needed to rebuild an unblocked
root from the blocked `Z`-gauge has not yet been formalized on `main`.

## Why the reverse direction is still blocked

The reverse implication remains blocked by the same-size Kraus-rank reduction
already packaged as `PRefinementInverseCanonicalization`.

Current repo status:

- `kraus_isometry_freedom_iff` / `kraus_unitary_freedom_iff` are available;
- they identify Kraus families of the **same completely positive map** up to an
  isometry;
- but `IsPDivisibleChannel (transferMap B) p` only provides an abstract root
  channel with an arbitrary finite Kraus family `K : Fin r → Matrix ...`.

What is still missing is a theorem producing a **`d`-indexed** Kraus family for
that root, so that the witness fits the current definition
`IsPRefinable B p : ∃ A : MPSTensor d D, ...`.

I found no theorem in the current channel/Kraus API that supplies this
cardinality reduction. The missing statement is exactly the one currently
packaged as

- `MPSTensor.PRefinementInverseCanonicalization`
  in `TNLean/MPS/Periodic/Symmetry.lean`.

## Conclusion

On the current `main` branch, neither canonicalization hypothesis can be removed
honestly.

To finish issue #622, the repo first needs:

1. an unconditional blocked equal-case route (or an unconditional replacement for
   `PeriodicEqualCaseFT`) built on top of the remaining periodic-overlap sector
   bridges; and
2. the blocked-to-unblocked cyclic transport needed to absorb the blocked
   `Z`-gauge into a genuine root tensor; and, independently for the reverse
   implication,
3. a same-size Kraus-rank reduction theorem for channel roots.

Because these bridges are still missing, I did **not** edit
`TNLean/MPS/Periodic/Symmetry.lean` or introduce any placeholder proof.
