# Gaussian absolute first-moment consolidation

Issue #9945 concerns repeated proofs of the first absolute moment of the
centred Gaussian. At base commit `122186095a`, the additional
`integral_abs_gaussianReal_le_sqrt` reported in the issue is already absent: commit `77eda47996`
removed it before #9902 was merged.

The independent Cauchy–Schwarz proof
`TNLean.MPS.AreaLaw.Hastings.integral_abs_gaussianReal_le` is removed. Its
replacement is `TNLean.Lattice.integral_abs_gaussianReal_le`, a corollary of
`TNLean.Lattice.integral_abs_gaussianReal_le_sqrt_two_mul_div_pi`, which
specializes the existing tail estimate to zero. The filtered-increment proof
also uses this sharper shared bound instead of repeating the specialization.
All three Hastings consumers and the blueprint reference use the replacement;
no compatibility alias is retained.

The integral is unchanged on deleting zero because its integrand vanishes
there. Thus the argument applies also to the zero-variance Dirac measure.
The simpler bound follows from `2 ≤ π`. No source hypothesis changes.

Mathlib v4.35.0-rc3 and QICLean at the pinned revision
`5aa0a041a679bc76c6b031cf6d3009306962c505` were searched for a suitable
absolute-moment theorem; neither supplies one. Issue #9990 can subsequently
move this shared Gaussian result and its tail proof to QICLean. The Duhamel
bound and the dependency pin are unchanged here.

Verification: the full build and all five affected module builds passed under
`scripts/lake_build_locked.sh`, with no changed-file linter warnings.
Blueprint synchronization and `leanblueprint checkdecls` passed. Kernel axiom
reports for both shared bounds and the filtered-increment and time-average
consumers contain only `propext`, `Classical.choice`, and `Quot.sound`.
