# Remove unused whole-increment Gram corrections

Issue: #7741, under parent-Hamiltonian tracker #190.

On main at `fafa75e42`, `WholeIncrementCorrectionBounds.lean` had no
non-aggregator importer. None of its fifteen declarations had a Lean
consumer outside the module. Their only live blueprint references were
twelve consecutive entries in the martingale chapter, with no incoming
references from the rest of the blueprint. The module and these entries
are removed together; the generated parent-Hamiltonian import is removed.

The replacement proof route already lives in `FNWGeometricDefect.lean`.
This deletion does not identify its prefactor with the source constant;
that independent mathematical problem remains tracked by #6367.
No compatibility aliases are retained under TNLean's no-stable-API policy.
The earlier inverse-Gram helpers remain outside the scope of this deletion.

## Removed declarations

- `MPSTensor.wholeIncrement_limitingOverlapProduct_eq`
- `MPSTensor.reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram`
- `MPSTensor.inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram`
- `MPSTensor.wholeIncrementLeftFiniteGramCancellation_eq_groundSpaceMapES_adjoint`
- `MPSTensor.wholeIncrementTailFiniteGramCancellation_eq_groundSpaceMapES_adjoint`
- `MPSTensor.wholeIncrementTailFiniteGramCorrectionES`
- `MPSTensor.wholeIncrementFullInverseGramCorrectionES`
- `MPSTensor.wholeIncrementLeftFiniteGramCorrectionES`
- `MPSTensor.norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt`
- `MPSTensor.wholeIncrement_virtualResidual_eq_centered_sub_gramErrors`
- `MPSTensor.wholeIncrementCenteredProjectorResidualES`
- `MPSTensor.wholeIncrement_injectiveRangeProjector_residual_eq_centered_sub_corrections`
- `MPSTensor.wholeIncrementTailFiniteGramCorrectionES_norm_le`
- `MPSTensor.wholeIncrementFullInverseGramCorrectionES_norm_le`
- `MPSTensor.wholeIncrementLeftFiniteGramCorrectionES_norm_le`

## Removed blueprint entries

- `thm:whole_increment_limiting_overlap_product`
- `thm:reassociated_tail_boundary_gram`
- `thm:reassociated_tail_inverse_gram`
- `thm:whole_increment_finite_gram_cancellations`
- `def:whole_increment_tail_gram_correction`
- `def:whole_increment_full_inverse_gram_correction`
- `def:whole_increment_left_gram_correction`
- `thm:reassociated_tail_pseudoinverse_bound`
- `thm:whole_increment_virtual_correction_telescope`
- `def:whole_increment_centered_projector_sandwich`
- `thm:whole_increment_finite_gram_corrections`
- `thm:whole_increment_correction_bounds`
