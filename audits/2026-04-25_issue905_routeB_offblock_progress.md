# Issue #905 Route B progress — off-block-zero commutant layer (2026-04-25)

## Scope of this PR

This branch does **not** attempt the full reverse inclusion

```lean
chainGroundSpace (toTensorFromBlocks μ A) L N ≤ ⨆ j, chainGroundSpace (A j) L N
```

for a CF/BNT family.  Instead it proves the first algebraic off-block-zero step
needed by the boundary-matrix route.

## Lean declarations added

In `TNLean/Algebra/ScalarCommutant.lean`:

- `Matrix.blockProjection`: the dependent block projection onto a chosen summand
  of `Σ i, n i`.
- `Matrix.IsBlockDiagonal`: a matrix is a dependent `Matrix.blockDiagonal'`.
- `Matrix.isBlockDiagonal_iff_offBlock_zero`: equivalence with vanishing of all
  off-diagonal block entries.
- `Matrix.isBlockDiagonal_of_commutes_blockProjection`: if a matrix commutes with
  every block projection, then it is block diagonal.

In `TNLean/MPS/SharedInfra/BlockAssembly.lean`:

- `MPSTensor.evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal`: word
evaluation of the assembled tensor is the reindexed block diagonal of the
blockwise word evaluations, with weights `(μ k) ^ w.length`.

## Why this is the right lower-level result

Route B from the latest #905 issue comment asks for a theorem saying that a
boundary matrix commuting with all sufficiently long assembled words is block
diagonal.  The expected proof factors through block projections:

1. Use the assembled-word formula to read every long word of
   `toTensorFromBlocks μ A` as a reindexed block diagonal matrix.
2. Use CF/BNT separation to show that the commutant of these block-diagonal word
   matrices contains the projections onto individual BNT blocks, and no
   off-diagonal intertwiner survives between distinct blocks.
3. Apply `Matrix.isBlockDiagonal_of_commutes_blockProjection` to force the
   boundary matrix to have zero off-diagonal blocks.

This PR proves step 3, and adds the word-evaluation identity used in step 1.
It deliberately does not claim step 2: that is the finite-length
Schur/intertwiner argument using `blocks_not_equiv` (or an equivalent consequence
of the cross-overlap decay results), and is still the mathematical content of the
full Route B commutant theorem.

## Remaining route to close #905

A future PR should prove a CF/BNT-specific statement along the following lines:

```lean
theorem isBlockDiagonal_of_commutes_assembled_long_words
    (hCF : IsCanonicalFormBNT μ A) ...
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
      evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    ∃ Xb, X = (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
      (Matrix.blockDiagonal' Xb)
```

The missing ingredient is to derive commutation with each block projection from
commutation with all assembled long words.  Equivalently, for every pair of
distinct blocks `j ≠ k`, the off-diagonal block `X_{jk}` must be shown to vanish
from the intertwining relation obtained by projecting the commutator entrywise:

```text
X_{jk} · (μ k)^m A_k(w) = (μ j)^m A_j(w) · X_{jk}
```

for every word `w` of length `m`.  This is where BNT separation enters.  The
generic block-projection theorem in this PR is ready to consume that conclusion
once it is available.

## Relation to PR #907

PR #907 proves only the forward inclusion
`⨆ j, chainGroundSpace (A j) L N ≤ chainGroundSpace (toTensorFromBlocks μ A) L N`.
This branch does not edit those lines and should merge independently.  Once the
full Route B commutant theorem is proved, it should compose with PR #907's
forward inclusion to give the equality requested by #905.
