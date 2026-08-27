# Retaining the region insertion-algebra isomorphism compatibility API

The region insertion-algebra existential predicate and its transfer constructor
have no production consumers at the audited head, because
`exists_regionEdgeGauge_of_transfer` uses
`RegionInsertionTransfer.fwdAlgEquiv` directly. Review nevertheless identified
the two declarations as public API that must remain source-compatible.

| Deprecated compatibility declaration | Preferred replacement |
|---|---|
| `TNLean.PEPS.IsRegionBlockedInsertionAlgebraIsomorphism` | `RegionInsertionTransfer.fwdAlgEquiv` together with `RegionInsertionTransfer.fwd_coeff`, the two components packaged by the existential |
| `TNLean.PEPS.isRegionBlockedInsertionAlgebraIsomorphism_of_transfer` | use `RegionInsertionTransfer.fwdAlgEquiv` and `RegionInsertionTransfer.fwd_coeff` directly; consumers seeking the gauge capstone may use `TNLean.PEPS.exists_regionEdgeGauge_of_transfer` |

Both names are retained in `TNLean/PEPS/RegionBlock/Algebra.lean` with deprecation
attributes dated 2026-08-27. The active implementation remains unbundled: the
transfer datum supplies its algebra equivalence and coefficient identity, and
the gauge capstone passes that equivalence directly to Skolem--Noether.

No blueprint tag cites either compatibility name. The module and paper-gap prose
continue to point new developments to `RegionInsertionTransfer.fwdAlgEquiv` and
`exists_regionEdgeGauge_of_transfer`; deprecation exists solely to avoid breaking
downstream imports and references.
