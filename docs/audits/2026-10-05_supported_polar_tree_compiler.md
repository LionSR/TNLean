# Supported polar trees and their coherent physical implementation

Source: arXiv:2307.01696, eq. (16), the two measurement-preparation paragraphs,
and the non-normal polar support in the Supplemental Material.
Preparation follow-up: #8687; general preparation tracker: #8620.

## Mathematical scope

The new tree theorem assumes injectivity on one fixed coordinate support after
one fixed length. An injective enumeration of that support has arbitrary size
`χ`; it need not be a square. Restricting the input and both outputs of the polar
merge gives a genuine isometry. The proof first drops the zero child columns
from the exact polar-merge formula, and then uses the two child isometries and
the parent isometry to obtain identity Gram matrix for the restricted merge.
No orthogonality between individual sectors' physical block ranges is assumed.

The physical compiler acts on every coherent input in the zero-scratch subspace.
A fixed outcome history has one scalar on the whole subspace, including the
zero-dimensional and one-dimensional cases and branches whose scalar is zero.
This follows from the linearity of the history Kraus map and Mathlib's
`LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`.
The exact equality includes every physical output site.

This is the supported-tree milestone, not the full canonical block-form
preparation theorem. The sparse GHZ seed, canonical amplitude/error estimate,
and every-length quantitative composition remain separate requirements. In
particular, this change does not claim arbitrary-tensor canonicalization or
periodicity transport.

## Shared proof and dependency changes

Compared with main at `0e904435d645e416cd630cd2ac6646db6c74ef6e`:

- `pairPosTensor` and `treeLayers` move verbatim from `TreeMERA` to
  `TreeFactorization`. `PolarMerge` imports this algebraic owner.
- The existing algebraic `BinaryMERA` definitions, polar tree-layer results,
  normalization proof, and fixed-point-pair disentangler move verbatim to
  `BinaryMERA`. `TreeMERA` imports that module and retains the approximation
  theorems and its previous exported declarations.
- `TreeAmplitude` imports `BinaryMERA`, and `RegisterTree` imports
  `BlockStatePreparation` instead of the convergence result `DepthUpperBound`.
- `coarseOutput` and the unequal register-tree implementation are generalized
  to arbitrary virtual dimension and compatible isometric families. The normal
  consumer is migrated rather than retained as a copied proof.
- The shared `IsometryTreePreparation` theorem owns node/leaf compilation and
  round composition. `UnequalTreePreparation` only adds its pair-preparation
  stage. Its public normal preparation theorem has the identical signature.

The moved source bodies and preserved normal signature were compared byte for
byte. These are structural dependency changes; no compilation speedup is claimed.
The compiled import-boundary regression excludes normal-gauge construction,
approximation-error modules, `TreeMERA`, and the Brouwer dependency.

## Verification

- Strict, single-threaded production-import elaboration of the algebraic tree,
  generalized register-state proof, physical compiler, supported consumer and
  migrated normal consumer, using only exact-source and exact-pin artifacts.
- `TNLeanTest/SupportedPolarTree.lean`: nonsquare support, odd parent with unequal
  leaves, coherent complex inputs, empty and singleton support, unchanged normal
  theorem, and compiled import boundary.
- `TNLeanTest/MeasurementBranchCoherence.lean`: execution order and uniform
  scalars for zero, singleton-span and scratch subspaces, including zero branches.
- `scripts/test_supported_polar_tree.py`: typed diagram boundaries and numerical
  checks of the actual polar merge for three overlapping normal scalar sectors.
- The supported tensor-network equation is rendered with the pinned tenkz
  package and visually inspected. Physical subtree maps are explicitly not
  counted as free block gates.

The exact-head full repository CI remains a merge requirement.
