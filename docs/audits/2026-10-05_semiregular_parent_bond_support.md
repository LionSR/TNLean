# Canonical semi-regular parents impose product bond support

## Main result

`TNLean.PEPS.regionParentGroundSpace_mem_product_matchingSectorRange` proves
that every ground vector of the **actual weighted block tensor's regional
parent** lies in the full product matching-sector inclusion range, after
regrouping the physical endpoints by bonds. Its hypotheses are:

- positive block dimensions and a matrix representation in each block;
- finite physical enumerations of the site's incident endpoint coordinates;
- genuine regional parent conditions;
- each edge has both endpoints in at least one parent region.

It assumes neither a closed-state identity nor an inserted-state expansion
of the ground vector. Irreducibility and completeness of the block family
are unnecessary for this support statement. Thus it applies in particular
to the derived minimal semi-regular representation of Section 7.

The theorem supplies exactly the range hypothesis needed by
`physicalProductMap_eq_on_inclusion_range`. Consequently the full-domain
isometric extension of the multiplicity-restoring map agrees with the
explicit supported bond formula on **every** weighted canonical parent
ground vector, not only the original closed state.

## Derivation from actual open regions

`GraphOpenSemiRegularSupport.lean` starts from the already established
`GraphOpenAveragingBondState` coefficient identity. With arbitrary virtual
boundary labels and fixed physical crossing endpoints, it proves:

1. The remaining internal-bond vector is a coherent product of
   Θ²V(q_head q_tail⁻¹).
2. This entire internal vector has matching-sector support.
3. Multiplicity restoration replaces the internal weighted matrices by the
   repeated representation matrices while retaining all crossing endpoint
   factors ΘV(q_tail⁻¹) or V(q_head)Θ.
4. Linearity extends the support assertion to the full actual regional
   ground space, not merely its generating boundary vectors.
5. Edge-covering parent regions then force matching sectors on every bond
   of an arbitrary global ground vector. The pointwise zero condition is
   identified with membership in the full product inclusion range.

The endpoint-inclusion utilities in `SemiRegularBondSupport` and
`SemiRegularBondProductIsometry` identify inclusion ranges with vectors
supported on the included coordinates. The pre-existing embedding and
image-evaluation lemmas are made public and reused, rather than duplicated.

## Source and remaining boundary comparison

Source: SCP10, arXiv:1001.3807v3, regional contractions at local lines
1765–1920 and 1935–1957, Theorem 5.7, and the Section 7 endpoint-pair
isometry at lines 2977–3019.

The support statement alone does not prove that applying the supported global
bond map preserves the repeated representation's canonical regional constraints.
That crossing-boundary step is now proved for the multiplicity-one-to-repeated
construction in `2026-10-05_canonical_multiplicity_parent_equivalence.md`. The map crosses the region boundary.
The retained boundary factors in the new internal-transport formula are
therefore essential; they cannot be discarded or declared equal to arbitrary
regular boundary data.

A concrete route is to fix the output coordinates outside the region,
expand the crossing-bond map one endpoint at a time, and absorb the remaining
nonzero scalar sector weights into the virtual boundary coefficients of the
repeated representation. The internal transformation is already proved.
The product-support theorem then replaces the supported map by the ambient
isometry on all source ground vectors. The subsequent canonical equivalence implements this route in both directions.
The arbitrary-multiplicity semi-regular classification and its complete
ground-space degeneracy statement remain separate.

## Validation

The new module and changed dependencies compile using the project Lean
options with no linter warnings and the default heartbeat bound. All
artifacts were written to an isolated validation directory; shared package
artifacts remained read-only. The dependency closure uses the pinned QICLean
revision `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`.
Axiom inspection of the main product-support theorem and both open-region
support/transport theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`. No root-import regeneration or full-library build is claimed.
