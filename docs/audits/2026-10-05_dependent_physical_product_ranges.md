# Dependent physical product ranges

## Mathematical scope

`TNLean/PEPS/DependentPhysicalProductRangeSupport.lean` proves the product-range
criterion for a finite site type and rectangular matrices
`F v : Matrix (Out v) (In v) ℂ`, with both alphabets depending on the site.
A global coefficient belongs to the product map's range if and only if every
one-coordinate slice belongs to the corresponding local matrix range.

The product matrix is the literal product of matrix entries. Global input and
output configurations are dependent functions. A slice uses dependent
`Function.update`, so neither padding to a common alphabet nor a common virtual
bond dimension is required. Local ranges may have different ranks, including
zero. There are no injectivity, surjectivity, positivity, normalization,
nonempty-site, or nonempty-alphabet assumptions. The range criterion requires
only `Finite (Out v)` at each site; its proof chooses the corresponding
`Fintype` instances internally.

This is supporting finite-dimensional algebra for the bond-space maps in
SCP10, arXiv:1001.3807, Section 7, lines 2992–3019 of the checked-in source.
Those lines describe the local change between semiregular and regular bond
spaces. This auxiliary criterion is not itself an assertion that the paper's
full torus reconstruction or global ground-space theorem has been proved.

## Public declarations

- `dependentPhysicalProductFamilyMatrix`
- `dependentPhysicalProductFamilyMap`
- `dependentPhysicalProductFamilyMap_apply`
- `dependentPhysicalProductFamilyMatrix_mul`
- `dependentPhysicalProductFamilyMap_comp`
- `dependentPhysicalProductFamilyMatrix_one`
- `dependentPhysicalProductFamilyMap_one`
- `dependentPhysicalProductFamilyMap_oneCoordinate_apply`
- `dependentPhysicalProductFamilyMap_fixed_of_slices_fixed`
- `dependentPhysicalProductFamilyMap_slice_mem_range`
- `mem_range_dependentPhysicalProductFamilyMap_iff`

The one-coordinate formula takes the dependent family obtained by updating the
identity-matrix family at a site. The fixed-slice criterion works for arbitrary
square local matrices; it does not require projections.

## Proof and dependency audit

The new module imports Mathlib only. Composition uses `Fintype.prod_sum`, and
the single-coordinate computation uses `Equiv.piSplitAt`. The reverse range
inclusion chooses a linear section onto each local range, extends it to the
full output space, and applies the resulting local retractions successively.
Thus its conclusion is derived from the slice hypothesis and not included as
an extra premise.

Mathlib scouting checked the matrix, tensor-product, and dependent
tensor-product developments. `PiTensorProduct.map_range_eq_span_tprod` describes
an abstract tensor-product range, but does not state the concrete
one-coordinate coefficient-slice criterion. No existing equivalent concrete
criterion was found. The existing regional product matrix is defined on region
subtypes and imports graph contraction infrastructure. Using it here would add
an unnecessary graph dependency and require reindexing arbitrary sites.

The tactic-pattern scan identifies the constant-alphabet product-range files
as specialization candidates. This new dependent criterion is the reusable
replacement for their repeated slice/retraction proofs. Consolidating those
existing consumers is left to the integrating change because this work owns
new files only; no separate tactic abstraction is needed.

## Regression and validation scope

`TNLeanTest/DependentPhysicalProductRangeSupport.lean` checks:

- the generic dependent statement, without nonemptiness or rank assumptions;
- an empty site set with empty local alphabets;
- rectangular local dimensions `1 → 2` and `2 → 3` at the two Boolean sites;
- one empty input fiber, forcing the entire product range to zero;
- one empty output fiber, making the global coefficient space zero-dimensional;
- a nonzero image for genuinely different input and output alphabets;
- the main theorem's axiom dependencies, exactly `propext`, `Classical.choice`,
  and `Quot.sound`.

The module and regression file are checked against the exact pinned Lean and
Mathlib cache, using a private symlink overlay and single-threaded compilation:

```text
-j1
-DautoImplicit=false
-DrelaxedAutoImplicit=false
-Dlinter.mathlibStandardSet=true
-DmaxSynthPendingDepth=3
-DwarningAsError=true
```

Both focused checks passed with no diagnostics: 2.674 seconds for the module
and 1.568 seconds for its regressions. The proof-integrity scan found no
placeholders, custom axioms, or kernel-bypass tactics.

No Mathlib source build is performed. These are focused checks of the new
module and its regressions, not a claim that the repository-wide aggregate
build has been run. Root import and blueprint integration remain with the
integrating change.

## Closure-packet consolidation

The final four-cut closure packet replaces the new common-alphabet family
proofs in `PhysicalProductFamilyRangeSupport` by direct specializations of
this dependent API. The pre-existing constant-matrix module is unchanged.
