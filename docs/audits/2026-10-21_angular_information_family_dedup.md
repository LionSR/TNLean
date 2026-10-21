# Angular information for a family: removed transport theorem

Date: 2026-10-21. PR: refactor(PEPS/Approximation): range-one angular
information as instances of the family statements (#9792).

The entropy comparison of the information reset on the open square,
`mutualInformation_cores_le_of_reset_unitary`, is now derived from the
comparison on any finite set of sites,
`mutualInformation_cores_le_of_sites_reset_unitary`, by relabelling the sites
through `rectangleSiteEquiv`. The transport of the reset unitary to two
replicas, which the square proof used to carry out itself, now happens once
inside the finite-site comparison. The square-specific transport theorem has
no remaining use and is deleted without a deprecated alias.

## Removed declarations and replacements

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.Approximation.reindex_rectangle_sumArrow_unitary` | the relabelling `embedOp_equiv_eq_reindex` with `Matrix.reindex_mem_unitaryGroup` (square to sites), followed by `reindex_sumArrow_sitePair_mem_supportedOperators` (sites to two replicas) inside `mutualInformation_cores_le_of_sites_reset_unitary` |
