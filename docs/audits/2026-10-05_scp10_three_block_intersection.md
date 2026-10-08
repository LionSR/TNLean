# SCP10 three-block open-region intersection

## Source and scope

The source is Schuch, Cirac, Pérez-García, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex`, Theorem 5.4 (`thm:2d:intersection`,
lines 1373–1420), with Definition 5.1 (`def:2d-Ug-inj`, lines 1278–1296)
and the independently assigned link representations at lines 1315–1320.
The source figures `figs3/grow-N.pdf`, `grow-M.pdf`, and
`grow-intersect.pdf` have been inspected. They depict three four-legged
cores on a path, two internal bonds, and eight exterior virtual legs.
The source repeats its endpoint tensor; allowing the two endpoint tensors
to differ is a generalization, not an added hypothesis.

The principal declaration is
`TNLean.PEPS.ThreeBlockDependent.regionalBoundarySpace_inf_eq_openBoundarySpace`
in `TNLean/PEPS/ParentHamiltonian/ThreeBlockGInjectiveIntersection.lean`.
It has only the source's finite-group, matched semi-regular representation,
and local G-injectivity assumptions, in finite coordinate spaces.

* Every one of the ten bonds has an independent finite alphabet `D e`.
* Each of the three original physical tensors has its own finite alphabet.
* Matched ends of an internal bond use the same representation, directly at
  the head and by inverse transpose at the tail.
* Each left/right region has exactly six virtual boundary incidences.
  Its boundary tensor is an arbitrary function of those six indices and
  the omitted core physical coordinate. No factorization is required.
* The whole-region map has exactly eight virtual boundary indices and
  exactly three physical output factors.
* No regular-representation, abelian-group, common-dimension, trace-dual
  coefficient, flatness, commuting-projector, or reconstruction hypothesis
  occurs in the capstone.

### Orientation convention

The labelled graph directs both internal bonds along the path and all
exterior bonds away from the cores. Reversing an exterior arrow in the
source picture replaces its chosen boundary representation by its
contragredient. This does not constrain the representation family:
`Representation.IsSemiRegular.dual` proves semi-regularity is preserved,
and `Representation.isSemiRegular_dual_iff` proves the converse
(`TNLean/Algebra/SemiRegularGroupAlgebra.lean`).
The coordinate contragredient acts as `(U(g⁻¹))ᵀ`; applying the tail
inverse transpose twice returns `U(g)`.
The coordinate reversal, involutivity, recovery identity, and preservation
of matrix semi-regularity are also checked independently in
`TNLeanTest/ThreeBlockBoundaryOrientation.lean`.
Thus the outward exterior convention includes the incoming exterior arrows
of the source figures. Interior cancellation uses the displayed matched
head/tail convention throughout.

### Physical coordinates

`ExtendedPhys` preserves the original physical alphabet at each of the
three core vertices and uses a virtual-coordinate alphabet only at an
auxiliary exterior vertex. `coreOutputEquiv` is the equality-induced
identification at a core. In the conclusion, the physical configuration
is indexed only by the three-element core subtype. The auxiliary
exterior physical factors have been eliminated, not assumed fixed as
part of the theorem's hypotheses.

## Noncircular proof chain

1. **Literal lifted regional ranges.** `liftedCutMap` sums only tensors
   belonging to its selected region. Its one joint boundary also contains
   every omitted physical coordinate. A site slice at a selected vertex
   therefore lies in that tensor's image.
2. **Derived local-image reconstruction.** A covering pair of regions
   forces every core physical slice into its local tensor image. Exterior
   identity maps are surjective. Product-range support follows from
   `mem_range_dependentPhysicalProductFamilyMap_iff`. Local linear
   retractions then absorb the omitted physical coefficients into the
   same arbitrary joint boundary; all omitted incidences are cut.
   This proves equality of the lifted intersection and the corresponding
   all-site cut intersection, without group or injectivity assumptions.
3. **One genuine inverse.** Local G-injective inverses satisfy
   `L_v A_v = P_v`, where `P_v` is the local invariant projector.
   Their product transforms all cuts simultaneously and the original
   tensors recover the original physical vector. No cut-specific inverse
   or assumed intersection is used.
4. **Derived coherent support.** The actual canonical cut coefficient is
   a sum over independent vertex group labels. An uncut bond is a
   representation matrix in every one-bond slice. Across the two cuts,
   this constrains both internal bonds. The independent product-range
   theorem then produces one coherent expansion in those representation
   matrices and full, unrestricted exterior matrix coordinates.
   Its existence is proved, not taken as a premise or inferred termwise.
5. **Tree gauge.** Canonical cut vectors are fixed by the product of local
   averages. Projecting each term of the coherent expansion gives its
   actual tensor network. For internal labels `p₀,p₁`, choose core gauges
   `q₀=1`, `q₁=p₀⁻¹`, `q₂=p₀⁻¹p₁⁻¹`, and trivial exterior gauges.
   Both internal insertions become identity matrices. The transformed
   exterior matrices remain unrestricted boundary data. There is no
   cycle and no holonomy compatibility premise.
6. **Remove auxiliary coordinates.** Constant extension and evaluation
   identify graph-wide lifted ranges with ranges on the three core
   physical factors. Explicit marginalization removes the unused
   virtual endpoints. Conversely, a boundary supported at one auxiliary
   configuration realizes every minimal boundary. Semi-regularity
   supplies nonempty bond alphabets through the existence of a nonzero
   invariant vector; nonemptiness is not an added capstone hypothesis.

The final regional contractions are defined independently by their finite
sums and compared to the auxiliary graph contractions. They are not
defined to be the desired intersection or a presumed reconstructible set.
No flattening to a one-dimensional MPS injectivity hypothesis occurs.

## File ownership and dependencies

This packet adds new files only. The prior regular prototype at commit
`4e22c9d73` is unchanged. The generic dependent graph, arbitrary joint cut,
product-range, and common-inverse foundations are reused from the full
four-cut packet `0fb7def90`; those sources are not copied or modified.
No shared root import, blueprint router, declaration index, MPU-gauging
file, push, or merge is part of this packet.

## Verification

Validation uses Lean 4.35.0-rc3 and the pinned prebuilt Mathlib cache.
All new production modules and all four regression modules are elaborated
with strict implicit arguments, the standard Mathlib linter set,
`maxSynthPendingDepth=3`, and warnings as errors. The regressions include
an arbitrary independently dimensioned signature, a full nonabelian permutation-group
capstone instantiation, nonabelian tree gauges,
and ten different virtual dimensions with nonregular trivial-group
representations and noncanonical nonsurjective physical maps.

The final source/artifact hash manifest, timings, and commands are retained
in `.validation/general-intersection/final-validation.json`.
Every public declaration is separately audited with `#print axioms`;
only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
A recursive import audit compares exact sources against the previously
validated donor source receipts and records the used artifact hashes.
No Mathlib source build, fresh checkout, or full repository build is run.
The focused checks are not a claim of a completed full-repository build.

The two new blueprint fragments are checked for declaration ownership,
source correspondence, references, prose, and rendered layout. Shared
router/index integration is intentionally left to the parent integration.

A broad blueprint scan reports 523 missing imported declarations because this
proof worktree deliberately has no local QICLean package checkout. Both new
fragments are nevertheless 161/161 in that scan, and the focused checker
validates every name against the already source-audited Lean environment.
The broad scan is not recorded as a full-tree pass.
