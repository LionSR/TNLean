# Retiring the region insertion-algebra isomorphism predicate

`TNLean/PEPS/RegionBlock/Algebra.lean` carried a bundled existential predicate
for the region-level insertion-algebra isomorphism together with the single
theorem producing it. Neither had a consumer anywhere in the production corpus
at the audited head: the downstream capstone `exists_regionEdgeGauge_of_transfer`
builds its Skolem--Noether input directly from
`RegionInsertionTransfer.fwdAlgEquiv`, bypassing the predicate. No blueprint
`\lean{...}` tag cited either name.

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.IsRegionBlockedInsertionAlgebraIsomorphism` | unbundled: the algebra equivalence `RegionInsertionTransfer.fwdAlgEquiv` together with the `fwd_coeff` field of `RegionInsertionTransfer`, which are exactly the two components the existential packaged |
| `TNLean.PEPS.isRegionBlockedInsertionAlgebraIsomorphism_of_transfer` | `TNLean.PEPS.exists_regionEdgeGauge_of_transfer`, which already assembled its own algebra isomorphism from the same transfer datum and never called this theorem |

Per the pass-through exception in `docs/project_conventions.md` §Style, no
transition declaration is left behind: both removals forward to declarations
that already exist, all non-`Archive` uses are migrated (there were none), and
no blueprint tag cited the old names.

## Prose and citation repairs

The scope-restriction marker on `exists_regionEdgeGauge_of_transfer` used to
delegate to the deleted theorem's docstring. The restriction is now stated in
place: the explicit transfer datum stands in for the region analogue of the
physical-to-virtual recovery `physical_to_virtual_insertion`, which remains
unformalized (remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`), and the positivity
hypotheses are the region analogue of the positive-bond restriction recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

The module docstring of `Algebra.lean` named the deleted theorem as the headline
of the file; it now names `RegionInsertionTransfer.fwdAlgEquiv` as the algebra
read-off and `exists_regionEdgeGauge_of_transfer` as the headline.

In `docs/paper-gaps/peps_normal_ft_section3_route.tex`, the footnote listing the
formal declarations behind the transfer-to-gauge step had its middle entry
redirected rather than dropped, so the clause "it gives a region
insertion-algebra isomorphism" still closes on a formal declaration: the entry
now reads `TNLean.PEPS.RegionInsertionTransfer.fwdAlgEquiv`.

## Surviving neighbours

`RegionInsertionTransfer`, `RegionInsertionTransfer.fwdLinearMap`,
`RegionInsertionTransfer.fwdAlgHom`, `RegionInsertionTransfer.fwdAlgEquiv`, and
`exists_regionEdgeGauge_of_transfer` all survive with independent uses. The
unconditional region-level injectivity `regionInsertedCoeff_injective` and the
linearity lemmas `regionInsertedCoeff_add` and `regionInsertedCoeff_smul` are
untouched and remain cited in the paper-gap route document.
