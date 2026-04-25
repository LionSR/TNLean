# Issue #911 Route B commutant reduction audit (2026-04-25)

Branch: `wave14-B-911-blockdiag-reverse`.

## Scope

This note records the status after adding the first Route B algebraic reduction for the
reverse inclusion from issue #911 / parent issue #905. The branch was rebased onto
`origin/main` after PR #899 landed the blockwise-injective endgame in
`DegenerateGS.lean`.

```lean
chainGroundSpace (toTensorFromBlocks μ A) L N ≤ ⨆ j, chainGroundSpace (A j) L N
```

## New formal layer

The new module `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean` proves:

- `Matrix.isBlockDiagonal'_of_commutes_span_blockProjection`: if every dependent
  block projection lies in the span of a family of matrices, then any matrix
  commuting with that family is block diagonal.
- `MPSTensor.isBlockDiagonal'_of_commutes_reindexed_wordSpan`: for a tensor on
  the reindexed direct-sum bond space, if the pulled-back length-`m` word span
  contains all block projections, then any boundary matrix commuting with every
  length-`m` word has block-diagonal pullback.
- `MPSTensor.offBlock_zero_of_commutes_reindexed_wordSpan`: the entrywise
  off-block-zero form of the previous theorem.

This uses the project-native #913 API:

- `Matrix.blockProjection`
- `Matrix.IsBlockDiagonal'`
- `Matrix.isBlockDiagonal'_of_commutes_blockProjection`

and keeps the finite-span hypothesis explicit.

## Remaining mathematical input

The full CF/BNT commutant theorem still requires the finite-span/separation step:
for canonical BNT data, prove that the virtual sector projections of the assembled
tensor lie in the span of sufficiently long assembled word products after pulling
back along `finSigmaFinEquiv`.

Concretely, for `B = toTensorFromBlocks μ A`, the remaining target has the shape

```lean
∀ k,
  Matrix.blockProjection (n := fun j : Fin r => Fin (dim j)) (R := ℂ) k ∈
    Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
      Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
        (MPSTensor.evalWord B (List.ofFn ω)))
```

or, equivalently using `evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal`, the
span of block-diagonal matrices

```lean
Matrix.blockDiagonal' fun j => (μ j)^m • MPSTensor.evalWord (A j) (List.ofFn ω)
```

contains each sector projection.

This is the finite-length Schur/BNT-separation step described in the issue thread:
projecting long-word commutation onto off-diagonal blocks gives intertwiners
between distinct CF/BNT blocks, and block separation should force those
intertwiners to vanish. The available asymptotic separation theorem is
`cross_overlap_tendsto_zero_of_separated_CFBNT_data`; it still has to be converted
into the finite word-span/projection statement above.

## Downstream use once the finite-span step lands

1. A periodic-chain ground vector of the assembled tensor gives a boundary matrix
   `X` by `contiguous_mem_groundSpace`.
2. The wrapping-window argument gives commutation of `X` with sufficiently long
   assembled words.
3. The new `MPSTensor.isBlockDiagonal'_of_commutes_reindexed_wordSpan` theorem
   turns that commutation plus the finite-span projection statement into block
   diagonality of `X`.
4. The block-diagonal boundary matrix can then be decomposed blockwise, and the
   existing forward inclusion / blockwise uniqueness results finish the planned
   reverse inclusion.

No reverse-inclusion theorem is claimed in this branch; the finite-span CF/BNT
projection statement is still the load-bearing missing input.

## Validation

Local validation on this branch:

- `lake build TNLean.MPS.CanonicalForm.BlockDiagonalCommutant`
- `lake build TNLean.MPS.ParentHamiltonian.DegenerateGS`
- `lake build TNLean.MPS.ParentHamiltonian.DegenerateGS TNLean.MPS.SharedInfra.BlockAssembly TNLean.Algebra.ScalarCommutant TNLean.MPS.CanonicalForm.BlockDiagonalCommutant`
- `lake build TNLean`
- `cd blueprint && leanblueprint web && leanblueprint checkdecls` initially needed the root `TNLean.olean`; after `lake build TNLean`, `cd blueprint && leanblueprint checkdecls` succeeded.
- Proof-integrity grep over the touched Lean/blueprint files found only the pre-existing deferred proof in `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` (`parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition`).
