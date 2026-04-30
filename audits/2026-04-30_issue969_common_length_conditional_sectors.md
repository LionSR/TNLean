# 2026-04-30 — Common-length cyclic sectors with conditional exact nonzero parts (#969/#942)

## Scope

This note records the additional common-length statement added for issues #969 and
#942 on the non-Gemma canonical-form route.  The Lean declarations keep the
blocked-word relabeling hypothesis explicit, so they do not overlap with #990,
which is the remaining theorem identifying the directly blocked nonzero family
with the family obtained from iterated blocking.

The new result strengthens the existing two-sided common-length theorem as a
conditional exact statement: once the two blocked-word relabeling equalities are
available, the canonical blocked nonzero parts are replaced by the weighted
common cyclic-sector families on both sides, including the zero-tail equations,
positive-length MPV equalities, and the length-zero identity.

## Source anchors

- `Papers/1606.00608/MPDO-22-12-17-2.tex:214--231` is the structural reduction
  used here: the tensor is written as a nilpotent contribution plus a finite
  nonzero block family, and the periods of the nonzero blocks are removed by
  blocking a common multiple.
- `Papers/2011.12127/TN-Review-main.tex:1798--1820` gives the same trace-preserving
  irreducible block form and explains that blocking the period of an irreducible
  block makes the transfer map primitive.
- `Papers/2011.12127/TN-Review-main.tex:1841--1884` is the later BNT comparison
  stage.  It consumes common normal blocks and compares their coefficients after
  phase and gauge matching; the present theorem supplies the common-length cyclic
  sectors in the exact MPV form needed before that comparison.

## Lean declarations

### `TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean`

- `MPSTensor.CommonBlockedCyclicSectorFamily.commonFlatBlocksAt` expresses the
  derived flattened common-sector family at a prescribed length `p'` when
  `F.p = p'`.
- `MPSTensor.CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonFlatAt_of_relabeling`
  is the prescribed-length form of the canonical-to-common-sector comparison.
  Its hypothesis is the `SameMPV₂` equality between the directly blocked
  nonzero family and the explicitly reindexed family.  This is exactly the
  hypothesis expected from #990.

### `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`

- `MPSTensor.zeroTail_commonFlat_of_blockWordRelabeling` is the renamed one-sided
  zero-tail conversion; it avoids the earlier informal wording about labels.
- `MPSTensor.zeroTail_commonFlatAt_of_blockWordRelabeling` gives the same
  zero-tail conversion at a prescribed common length.
- `MPSTensor.sameMPV₂Pos_blockTensor_commonFlatAt_of_blockWordRelabeling` records
  that the zero-tail term vanishes at positive system sizes, so the blocked tensor
  and the weighted common-sector family have equal MPV coefficients there.
- `MPSTensor.fundamentalTheorem_after_blocking_1606_commonLength_commonSector_of_blockWordRelabeling`
  starts from `SameMPV₂ A B`, chooses one positive blocking length for both sides,
  obtains common cyclic-sector families on both sides, and then conditionally
  rewrites all nonzero-part and zero-tail conclusions with the weighted
  common-sector families.

## Relation to neighboring issues

- #990 should supply the two blocked-word relabeling equalities assumed by the
  new two-sided theorem.  This branch keeps those assumptions visible rather
  than hiding them behind a new name.
- #942 can use the conclusion as the exact common primitive irreducible block
  data at one physical blocking length, after the #990 equalities are supplied.
- #970 and #944 still need the later common phase-cover or BNT proportional
  comparison data, as well as any additional injectivity blocking required for
  the overlap-span theorem.

## Remaining mathematical statements

1. Prove the blocked-word relabeling equality for a `CommonBlockedCyclicSectorFamily`
   on each side, reducing the direct blocked family to the explicitly reindexed
   family.  This is issue #990.
2. If one-site injectivity is required by the final overlap theorem, add the
   separate Wielandt/injectivity blocking stage without identifying it with the
   period-removal length.
3. Derive the common phase-cover or BNT proportional-decomposition hypotheses
   from the exact common-length nonzero-sector data.
