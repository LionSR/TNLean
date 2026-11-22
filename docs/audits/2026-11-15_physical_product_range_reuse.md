# Constant physical-product ranges from the dependent theorem

This implements rank 1 of the comprehensive 2026-11-15 simplification audit
and the consolidation deferred in
`2026-10-05_dependent_physical_product_ranges.md`.

## Mathematical contract

The three public statements in `PEPS/Injectivity/Multiplicity/PhysicalProductRangeSupport.lean` are
unchanged, including every typeclass binder:

| Public theorem | Existing replacement proof in `TNLean.Lattice` |
|---|---|
| `physicalProductMap_fixed_of_slices_fixed` | `dependentPhysicalProductFamilyMap_fixed_of_slices_fixed` |
| `physicalProductMap_slice_mem_range` | `dependentPhysicalProductFamilyMap_slice_mem_range` |
| `mem_range_physicalProductMap_iff` | `mem_range_dependentPhysicalProductFamilyMap_iff` |

Each application uses the constant local matrix family. The input and output
alphabet families are consequently constant too. Both product maps reduce to
`Matrix.mulVecLin` of the same literal product of matrix entries. The slice
expressions and local matrix ranges are identical.

The fixed-slice statement still permits arbitrary square matrices, without
projection or positivity assumptions. The forward range statement still
requires no finite output alphabet. The range equivalence retains `Finite Out`,
without requesting `Fintype Out` from its caller. Empty sites, empty alphabets,
zero matrices and arbitrary ranks remain covered.

The Blueprint label `thm:peps_parent_support_product_range` retains its three
public declaration anchors. No Blueprint statement or declaration tag changes.
Source context remains SCP10, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex:2992–3019`, where the local bond-space maps
produce the physical equivalence. This auxiliary range criterion makes no new
claim about completing the global reconstruction theorem.

## Removed machinery and dependency direction

Four private declarations are removed:

- `productFamilyMatrix` and `productFamilyMap`: use the existing dependent
  product matrix and map through the three public theorem applications.
- `productFamilyMap_comp`: composition is already proved at the dependent owner.
- `productFamilyMap_oneCoordinate_apply`: the dependent fixed-slice theorem
  already supplies the coordinate argument.

No public declaration is removed or renamed, so no alias is needed. The file
shrinks from **188 to 59 lines: 7 additions, 136 deletions, net −129 Lean lines**.
This replaces the earlier 140–150-line estimate with the measured diff.

The direct import is
`TNLean.Lattice.Compression.DependentPhysicalProductRangeSupport`, whose imports
are all Mathlib modules. Importing the PEPS family wrapper instead would create
a cycle because it already imports the constant module. The existing
`SemiRegularBondProductIsometry` import is retained; changing that independent
transitive interface is outside this slice. The explicit Basis import becomes
unnecessary because the shared dependent owner already imports it.

## Ownership and source evidence

Base: `eb588dc15332a3798431015e6c27ecbaf329b2d1`.

- Original constant-module blob: `bdaf2d1e3b5ea73286ab57698f43dc9ded1db294`.
- Dependent-owner blob: `fa665fae06c0cc29f313a8b1a297e718d63f629b`.
- Existing family-specialization blob: `32e4805893c2360709dd0ce43f41ff7c5edb0ce1`.

All were read at the exact current-main revision and matched the local source.
All 25 open PR file lists were inspected before editing; none touches the
changed constant module or its dependent owner. Branch-name searches for
`product`, `range` and `simplif` found no competing product-range branch;
the matching inhomogeneous-preparation branch owns separate files. These checks
do not establish the absence of an unpublished remote session.

## Validation and remaining coverage

Passed: exact equality of all three public theorem headers, unchanged Blueprint
anchor search, absence of all four private names in the new file, import-cycle
inspection, the edited module's reader-facing prose check, 100-character line
limit, `git diff --check`, and the forbidden-token diff check.

The local command `lake build TNLean.PEPS.Injectivity.Multiplicity.PhysicalProductRangeSupport` exits
127 because Lake is not installed. There is no dependency cache and enforced
networking is disabled. No compiler result is claimed. Hosted acceptance must
build the changed module, `PhysicalProductFamilyRangeSupport`,
`GraphRepeatedParentSupport`, `TorusCutBondSupport`, and
`TorusCutCanonicalBondSpan`, then run the root build and strict changed-file
checks under the existing cache policy.

The scoped constant-product duplication is removed. The separate coherent-sum
expansion candidate, the phantom crossing-predicate parameter and the remaining
ranked audit items stay open; this change does not imply their completion.
At the continuation check, #10637 still has a queued PR CI workflow with no
completed build or status conclusion. Both changes require compiler acceptance
before integration. No merge is performed.
