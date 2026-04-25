# Issue #911 — projection-span reduction from product-word span (2026-04-25)

## Scope

Wave 15 Slot B targeted the remaining finite-span input for the periodic block-decomposition
commutant argument: the virtual sector projections should lie in the span of pulled-back
length-`m` assembled word products.

The fully paper-level CF/BNT theorem still requires a finite-length separation statement turning
separated canonical-form/BNT data into a full product-word span for simultaneous block words. The
current repository has the relevant asymptotic cross-overlap decay and eventual BNT state linear
independence, but not yet the stronger boundary/matrix-entry product-word span needed here.

## Lean declarations added

File: `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean`

- `Matrix.blockProjection_mem_span_blockDiagonal'_of_pi_span_eq_top`
  - Pure algebra: if a family of tuples `T : α → (i : ι) → M_{n_i}(ℂ)` spans the
    full product algebra and `c i ≠ 0`, then the span of the block-diagonal matrices
    `blockDiagonal' (fun i => c i • T a i)` contains every dependent block projection.
  - Proof uses the linear map sending a tuple to its scaled dependent block diagonal and applies it
    to the tuple with `(c k)⁻¹ I` in the chosen component and zero elsewhere.

- `MPSTensor.blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top`
  - MPS specialization: if the simultaneous length-`m` block-word tuples
    `ω ↦ (k ↦ evalWord (A k) (List.ofFn ω))` span the full product algebra and all `μ k` are
    nonzero, then every sector projection belongs to the span of the pulled-back length-`m` word
    products of `toTensorFromBlocks μ A`.
  - Uses `evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal` to identify the pulled-back
    assembled word products with `blockDiagonal' (fun k => (μ k)^m • evalWord (A k) w)`.

- `MPSTensor.isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top`
  - Composes the projection-span theorem with PR #921's commutant criterion: length-`m` word
    commutation plus product-word span implies the pulled-back boundary matrix is block diagonal.

- `MPSTensor.offBlock_zero_of_commutes_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top`
  - Entrywise off-block-zero corollary for the same hypotheses.

Blueprint Chapter 14 now records these declarations as
`lem:block_projection_span_from_product_word_span` and updates the downstream dependency list for
`thm:parent_ground_space_le_bnt_span`.

## Remaining paper-level bridge

To close the original #911 target under bare `IsCanonicalFormBNT μ A`, one still needs a theorem of
one of the following equivalent finite-length forms:

1. **Product-word span:** there exists a length `m` such that
   `ω ↦ (k ↦ evalWord (A k) (List.ofFn ω))` spans `Π k, M_{dim k}(ℂ)`.
2. **Block selector words:** for each sector `k`, a finite linear combination of length-`m` words is
   the identity on block `k` and zero on all other blocks.
3. **Matrix-entry independence:** the scalar word-entry family over all block matrix entries is
   linearly independent for some finite length.

`TNLean/MPS/MPDO/BiCFDerivation.lean` already contains abstract algebraic routes among these
conditions (`WordTupleSpanTop`, `HasBlockSelectorWords`, `PropBlockInjective`, and
`wordEntryFamily`). What is not yet formalized is the implication from separated CF/BNT data
(`blocks_not_equiv` plus block injectivity/left canonicality, via the cross-overlap separation
lemmas) to one of these finite-length witnesses. That implication is the remaining
asymptotic-to-finite Schur / block-separation theorem.

## Validation

- `lake build TNLean.MPS.CanonicalForm.BlockDiagonalCommutant` succeeded after the Lean cache was
  fetched/decompressed in this fresh worktree.
- `lake build TNLean` succeeded after rerunning with `ulimit -n 8192`; the first full-root attempt
  failed only with macOS `Too many open files in system` while compiling independent modules.
- `cd blueprint && leanblueprint web` succeeded; the first combined `checkdecls` invocation failed
  only because `TNLean.olean` did not exist yet in the fresh worktree.
- After `lake build TNLean`, `cd blueprint && leanblueprint checkdecls` succeeded.
- `git diff --check` succeeded.
- A proof-integrity grep over touched Lean/blueprint/audit files found no forbidden proof tokens.
