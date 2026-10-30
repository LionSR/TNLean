# Remaining canonical hypothesis cleanup

Issue: #7916. Audited main `efa3070d3060aa49df30530b9eda1b6484c668f2`.
The bulk canonical/periodic/ZCL cleanup already landed in #9254; this change
addresses one small surviving part of the sector-match layer.

`SectorMatch/CyclicTrace.lean` removes `[NeZero D]` from the private
`trace_cyclic_matrix_single_chain` and the public
`piTensorProduct_eq_smul_of_corner_cyclic_products`. Their proofs use only
the nonzero number of cyclic factors, `[NeZero m]`, which remains. The
matrix-unit indices are explicit coordinates, and the finite matrix basis
and tensor-product basis allow empty bond index types. The existing proofs
are unchanged. Thus the public tensor-product identity also covers the
zero bond dimension, without a separate degenerate predicate or theorem.

The sole production caller is in `SectorMatch/Contraction.lean`. Its own
bond-dimension instance is still required by its cyclic-sector-decomposition
hypotheses, so it is retained; no caller-only instance can be deleted here.
No Blueprint declaration tag cites either changed lemma, so no declaration
redirect or verification-status change is needed. No compatibility alias
is added, and no theorem name or mathematical conclusion changes.

The broader issue remains open. In particular,
`IsCyclicSectorDecompWith` and `IsCyclicSectorDecomp` in
`Overlap/SelfOverlapSetup.lean` themselves take `[NeZero D]`. Most remaining
public sector-match and sector-overlap signatures mention those predicates;
removing their ambient instance alone would leave the statements unable to
elaborate. The previously recorded sequencing issue #7762 remains open.
This small change does not claim to discharge that separate interface work.

Validation: source caller/tag searches, generated-import check, reader-facing
prose check and whitespace check passed. The live open-PR scan found no
change to this file. No local Lean invocation or build was run, as requested;
hosted verification is pending, so this is a draft source change.
