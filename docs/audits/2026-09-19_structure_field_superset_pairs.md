# Structure pairs where one restates every field of the other

A field-superset scan over the repository's structures isolated five pairs in
which one structure repeats every field name of another and adds one field,
with a hand-written forgetful bridge in place of `extends`. This audit records
which pairs were collapsed, which were retained, and why.

## What changed

Two structures now inherit rather than repeat their parent's fields, and one
forgetful bridge was removed.

| Removed | Replacement |
|---|---|
| `MPSTensor.HasAppendixD2ParentCommutingHamiltonian.to_overlapping` | `MPSTensor.HasAppendixD2ParentCommutingHamiltonian.toHasOverlappingTwoSiteCommutation` |

`MPOTensor.GroupFamily.IsRepresentation` now extends
`MPOTensor.GroupFamily.IsRawRepresentation` and declares only `isSimple`; the
raw structure moved above it so the two-stage raw-then-simple reading stays in
source order. `MPSTensor.HasAppendixD2ParentCommutingHamiltonian` now extends
`MPSTensor.HasOverlappingTwoSiteCommutation` and declares only
`kernel_intersection`.

Three proof bodies shrank accordingly.
`MPOTensor.GroupFamily.IsRawRepresentation.block` is new: it carries the four
raw fields through a positive physical blocking, and
`MPOTensor.GroupFamily.IsRepresentation.block` and
`MPOTensor.GroupFamily.IsRawRepresentation.block_common` now adjoin `isSimple`
to it instead of rebuilding five fields each.
`MPOTensor.OrthogonalCommutingSectorFamily.toProportional` keeps its name and
its statement but copies its five shared fields with structure-update syntax
rather than field by field; the two sector families are not joined by
`extends`, for the reason recorded below.

## What was checked

No structure in either pair is built with a positional anonymous constructor,
so reordering `isSimple` and `kernel_intersection` to last is invisible to
callers; every construction uses `where` or structure-update syntax and every
use is field projection by dot notation, which resolves through the parent.
`IsRawRepresentation` has no use outside its own file.
`IsRepresentation` is used as a hypothesis in ten files, none of which
constructs it positionally. The four uses of the removed bridge, two in
`TNLean/MPS/ParentHamiltonian/LocalSupport.lean` and two in
`TNLean/MPS/RFP/AppendixBStructuralData.lean`, were renamed to the inherited
parent projection.

The one blueprint tag naming the removed bridge, on the overlapping two-site
supports definition of
`blueprint/src/chapter/ch13_parent_hamiltonian_commuting_gap_local_terms.tex`,
was redirected to the parent projection, which proves exactly the statement the
bridge proved. It is one of seventeen tags on that node, so no node text
changed. Every other tag on the affected structures keeps its name, because
`extends` preserves the names of both structures.

## What is retained, and why

Three of the five pairs are left alone.

The two orthogonal commuting sector families of
`TNLean/MPS/MPDO/GSNNCHOrthogonalSectors.lean` share five fields but are not
given a common base. Their field docstrings cite different passages of
arXiv:1606.00608 — lines 838--842 with 1786--1796 for the exact family, lines
838--842 with 1641--1665 for the proportional one — and a shared base would
have to carry one of the two citations or drop both. A five-field base with its
own source docstrings and scope-restriction marker costs more lines than the
fifteen it would remove, and both families are blueprint definition nodes.

The three rank-one trace factorizations — `RankOneTraceFactorization`,
`Matrix.EtaRankOneTraceFactorization`, and `NeighboringTraceFactorization` —
share a shape but not a statement. Their carriers are dependent index families
with different parameters, their trace fields have different names, and
`NeighboringTraceFactorization` orders its fields differently, is constructed
in four files, and receives about fourteen blueprint tags. Unifying them would
rename roughly twenty-nine field occurrences across twelve files to remove four
duplicated lines, and `EtaRankOneTraceFactorization` carries its own scope
restriction that a generic base would have to shed.

The two weight-normalization predicates are retained on purpose, as a
source-guarded carrier beside an ambient-free one.
`MPSTensor.CPSVCanonicalFormData.IsWeightNormalized` states that some weight
has unit modulus under the guard that the ambient tensor is nonzero, which is
the source's own condition; the empty canonical form occurs exactly when that
tensor vanishes. `MPSTensor.PreparedBNTBlocks.IsWeightNormalized` is
unconditional because a prepared block collection has no ambient tensor to be
zero. A shared predicate would have to either drop the guard from the tagged
definition, which strengthens a blueprint-tagged statement and so is barred by
the faithfulness rule, or add a vacuous guard to the unconditional one. The
honest passage between them already exists in two lines of
`TNLean/MPS/FundamentalTheorem/SectorBNT/CanonicalFormBridge.lean`.

## What is deferred

Nothing. The three retained pairs are recorded as decided, not postponed.
