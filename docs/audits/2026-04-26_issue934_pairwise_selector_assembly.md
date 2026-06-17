# Issue #934 — pairwise selector assembly (2026-04-26)

## Scope

Wave 17 Slot D targeted the missing finite selector-word input for the Route B parent-Hamiltonian
reduction.  The full paper-level theorem

```lean
IsCanonicalFormBNT μ A → ∃ S, HasBlockSelectorWords A S
```

is still not proved from BNT separation alone.  This pass lands a checked finite-dimensional
predecessor: it reduces full block-selector words to **pairwise** block-separating word
polynomials.  Thus the remaining BNT separation task is sharpened from constructing one global
selector for each block to constructing, for every ordered pair of distinct blocks, a common-length
word polynomial that is identity on the first block and zero on the second.

## Lean declarations added

File: `TNLean/MPS/MPDO/BiCFDerivation.lean`

- `MPSTensor.HasBlockSelectorOn`
  - Tuple-span form of a partial selector: a length-`S` word polynomial is identity on a block `k`
    and zero on a finite target set of other blocks.

- `MPSTensor.HasPairBlockSeparatingWords`
  - Pairwise predecessor to global selector words: for each ordered pair `k ≠ j`, there is a
    length-`S` partial selector for `k` on `{j}`.

- `MPSTensor.pointwise_mul_mem_span_wordTuple_add`
  - The span of simultaneous word tuples is closed under pointwise matrix multiplication, with
    word lengths adding by concatenation.

- `MPSTensor.hasBlockSelectorOn_empty`
  - The empty word gives the identity tuple, hence a selector on the empty target set.

- `MPSTensor.HasBlockSelectorOn.mul`
  - Multiplying partial selectors for the same block unions their target sets.

- `MPSTensor.hasBlockSelectorOn_finset_of_pairBlockSeparatingWords`
  - Inducts over a finite target set and multiplies the relevant pairwise separators.

- `MPSTensor.hasBlockSelectorWords_of_forall_hasBlockSelectorOn_univ_erase`
  - Converts tuple-span selectors on `Finset.univ.erase k` into the existing coefficient-based
    `HasBlockSelectorWords` predicate.

- `MPSTensor.hasBlockSelectorWords_of_pairBlockSeparatingWords`
  - Pairwise separators of length `S` give full block-selector words of length `(r - 1) * S`.

- `MPSTensor.propBlockInjective_of_common_blockInjective_of_pairBlockSeparatingWords`
  - Common block injectivity plus pairwise separators gives the abstract Proposition-IV.3 data.

- `MPSTensor.wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords`
  - Common block injectivity plus pairwise separators gives full product-word span.

- `MPSTensor.hasBiCF_of_common_blockInjective_of_pairBlockSeparatingWords`
  - The same hypotheses give the biCF trace-separation predicate.

File: `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean`

- `MPSTensor.wordTupleSpanTop_of_isCanonicalFormBNT_of_pairBlockSeparatingWords`
  - Composes CF/BNT block injectivity with the pairwise-to-global selector assembly and the merged
    selector-word product-span reduction.

- `MPSTensor.exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairBlockSeparatingWords`
  - Issue-#934 product-span shape with pairwise block-separating words as the explicit remaining
    finite separation input.

Blueprint Chapter 14 records the new definition/lemma at
`def:pairwise_block_separating_words` and `lem:block_selectors_from_pairwise_separators`, and cites
that reduction from the existing product-span and parent-ground-space roadmap entries.

## Remaining blocker

The remaining paper-level argument is now:

```lean
IsCanonicalFormBNT μ A → ∃ S, HasPairBlockSeparatingWords A S
```

or any equivalent construction implying it.  Concretely, from injectivity, left-canonical
normalization, and `blocks_not_equiv`, one must produce a finite word polynomial separating each
ordered pair of distinct blocks.  The expected route is still the BNT separation/Gram argument:
use cross-sector overlap decay from `cross_overlap_tendsto_zero_of_separated_CFBNT_data`, prove
nondegenerate same-sector limits for matrix-inserted word states, then extract finite pairwise
separators (or global matrix-entry word-family linear independence).

## Validation

Successful local checks in `wave17-D-934-selector-words`:

- `lake build TNLean.MPS.MPDO.BiCFDerivation`
- `lake build TNLean.MPS.MPDO.BiCFDerivation TNLean.MPS.CanonicalForm.BlockDiagonalCommutant`
- `lake env lean TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean`
- `lake env lean TNLean/MPS/MPDO/BiCFDerivation.lean`
- `ulimit -n 8192 && lake build TNLean`
  - The first full-build continuation reached the command timeout after substantial progress; the
    immediate continuation completed successfully, with only pre-existing warnings in unrelated
    modules.
- `cd blueprint && leanblueprint web`
- `cd blueprint && leanblueprint checkdecls`
- `git diff --check`
- touched-file forbidden-token scan clean
