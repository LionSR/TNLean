# Deleting the region insertion-algebra isomorphism compatibility API

The region insertion-algebra existential predicate and its transfer constructor
have no production consumers: `exists_regionEdgeGauge_of_transfer` uses
`RegionInsertionTransfer.fwdAlgEquiv` directly. The maintainer explicitly
confirmed that TNLean does not promise public API compatibility, so both
superseded declarations are deleted rather than retained with deprecations.

| Deleted declaration | Direct replacement |
|---|---|
| `TNLean.PEPS.IsRegionBlockedInsertionAlgebraIsomorphism` | `RegionInsertionTransfer.fwdAlgEquiv` together with `RegionInsertionTransfer.fwd_coeff`, the two components formerly packaged by the existential |
| `TNLean.PEPS.isRegionBlockedInsertionAlgebraIsomorphism_of_transfer` | use `RegionInsertionTransfer.fwdAlgEquiv` and `RegionInsertionTransfer.fwd_coeff` directly; consumers seeking the gauge capstone may use `TNLean.PEPS.exists_regionEdgeGauge_of_transfer` |

No blueprint tag cites either deleted name. The active implementation remains
unbundled: the transfer datum supplies its algebra equivalence and coefficient
identity, and the gauge capstone passes that equivalence directly to
Skolem--Noether. No compatibility declarations are retained under the
maintainer's explicit no-public-API-compatibility policy.
