# The actual original-side residual of one regional soft replacement

Original positive-contraction nearest-neighbour bonds determine three disjoint
internal regional sums and at most two crossing bonds. The theorem constructs
one common unit vector attaining the three regional minima and an original
centered ground vector at an actual ground energy between zero and two. These
choices precede every low-energy width, auxiliary hard cutoff, soft scale and
Taylor order. There is no supplied low-energy family, regional energy, residual
bound, spectral gap or unique-ground-state premise.

The actual soft operator replaces the centered middle regional matrix by its
finite soft function. It is Hermitian and lies below the original centered
Hamiltonian. The original-side restricted error is bounded by the sum of the
previously derived physical hard tail and the exact polynomial low-band error:
32 exp(-(T-eta)/8) + (t/m)(T/t)^m, for eta>0, T>=eta+7, t>0 and m>=1.
The hard cutoff is only an estimate parameter; the actual soft operator does
not depend on it. Order four gives the additional error T^4/(4 t^3), and
independent large scale is allowed. Empty regions, coincident or endpoint cuts,
zero sites and local dimension one are included where the indexed chain permits
them. No unit-vector or dimension condition is added beyond positive local
dimension.

The proof constructs the hard replacement and its actual restricted error from
the existing physical theorem. The exact scalar-shift clipping identity and
regional sum identity identify its discrepancy with the hard residual of the
same positive regional matrix used in the soft function. The new generic
restricted soft–hard estimate then gives the stated bound. No global norm
smallness of the truncation error is inferred. The reverse soft-to-original
residual, comparison on a soft low-energy space, and the final GEN parameter
and running-time conclusions remain separate.

The existing private three-region sum identity in `AKLV/TwoBlockTruncation`
is exposed without altering its statement or proof, with a mathematical book
entry. This avoids a third copy of the same spatial partition. Its selected
existing importer `ALVV/HardTruncationResidual` was freshly re-elaborated from
byte-identical source after the declaration became public. That unchanged
importer source is not part of the patch.

This is a corrected one-direction auxiliary for ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1420. It is
not marked as a formalization of the printed uniform energy estimate or the
complete efficient-filter theorem. Existing source-error records and
counterexamples remain unchanged in `docs/paper-gaps/alvv16_cluster_approximation.tex`
and the companion hard-truncation-window note at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.

Selected sources, objects, build inputs and the prebuilt Mathlib record were
guarded. No provider, dependency cache or Mathlib source was changed. Full
ordinary integrated and compiled-book checks remain pending. No permanent
foundation fixture is introduced.
