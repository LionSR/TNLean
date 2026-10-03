# Lemma 1'(ii) variants derived from the repeated-overlapping bound

This audit records the declarations and modules removed when the variants of
arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), became corollaries of
the bound for repeated overlapping blocks,
`MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum`. It is
the audit note required by `docs/project_conventions.md` §Style. All
non-`Archive` uses are migrated, no blueprint `\lean{...}` tag cites a removed
name, and no compatibility alias is kept.

## Removed modules

- `TNLean/MPS/Preparation/OrthogonalBlockError.lean`: the proof of Lemma 1'(ii)
  for orthogonal blocks of multiplicity one.
- `TNLean/MPS/Preparation/ComplexWeightError.lean`: the reduction of complex
  weights to nonnegative weights by moving the phases into the blocks.

Their theorems `MPSTensor.exists_approximationError_le_blockSum`,
`MPSTensor.exists_approximationError_le_mul_blockSum`,
`MPSTensor.exists_approximationError_le_overlappingBlockSum_complexWeight` and
`MPSTensor.exists_approximationError_le_mul_overlappingBlockSum_complexWeight`
are kept under their names in `TNLean/MPS/Preparation/BlockSumError.lean`. The
complex-weight theorems no longer assume `|μⱼ| ≤ 1` or that some weight has
modulus one, and their constant does not depend on the weights.

The theorems `exists_approximationError_le(_mul)_repeatedBlockSum` (from
`RepeatedBlockError.lean`), `exists_approximationError_le(_mul)_repeatedBlockSum_oneCopy`
(from `OneCopyPairState.lean`) and `exists_approximationError_le(_mul)_overlappingBlockSum(_weight)`
(from `OverlappingBlockError.lean`) also move, under their names, to
`BlockSumError.lean`.

## Removed declarations and their replacements

From `OrthogonalBlockError.lean`:

- `MPSTensor.norm_nonNormalApproxOverlap_blockSum`, the overlap of the
  approximating state for orthogonal blocks of multiplicity one. Replacement:
  `MPSTensor.nonNormalApproxOverlap_blockSum_eq_copyApproxOverlap`, which
  identifies this overlap with that of the corrected state with one copy per
  block, followed by the master bound.
- `MPSTensor.one_sub_norm_sum_div_le`, the triangle inequality once the cross
  terms vanish. Replacement: `MPSTensor.one_sub_norm_div_le_of_norm_sub_le` in
  `OverlappingBlockError.lean`, used by the master bound.
- `MPSTensor.sum_star_mpv_approximatingTensor_mul_mpv` and
  `MPSTensor.sum_star_mpv_blockedConfigEquiv`, the overlap and norm of one
  block read in blocked configurations. They served only the proof of
  `norm_nonNormalApproxOverlap_blockSum`; the replacement is the master bound,
  through the corollaries above.

From `ComplexWeightError.lean`:

- `MPSTensor.blockSum_eq_blockSum_phase`, moving the phases of the weights
  into the blocks. Replacement: none needed; the master bound takes complex
  weights directly, through `MPSTensor.repeatedBlockSum_single`.
- `MPSTensor.hasEigenvalue_of_hasEigenvalue_smul` (private), an eigenvalue of
  `c • f` gives one of `f`. It served only the phase reduction above.

From `RepeatedBlockError.lean` (which keeps the definition
`MPSTensor.copyApproxOverlap`):

- `MPSTensor.norm_overlap_of_orthogonal`, the overlap of two combinations of
  orthogonal families, and `MPSTensor.norm_copyApproxOverlap_repeatedBlockSum`,
  its application to the corrected state. Replacement: the orthogonal-block
  corollaries in `BlockSumError.lean`, which obtain the bound on the mixed
  transfer maps from
  `MPSTensor.eq_zero_of_hasEigenvalue_mixedMapLM_of_conjTranspose_mul_eq_zero`
  and then apply the master bound.

From `OverlappingBlockGram.lean`:

- `MPSTensor.exists_norm_polarPos_blockTensor_blockSum_weight_sub_le`, the
  rate of the positive part for weights of different moduli, through the
  Hölder bound and only for `γ < 1/2`. Replacement: the weighted theorems are
  derived from the complex-weight theorem, which rests on the master bound and
  holds for every `γ < 1`.

From `SecondOrderBlockError.lean`:

- `MPSTensor.exists_abs_norm_mpvState_blockSum_sq_sub_le_of_lt_one`.
  Replacement: `MPSTensor.exists_abs_norm_mpvState_blockSum_sq_sub_le`, which
  now holds for every `γ < 1` and so has the same statement.
