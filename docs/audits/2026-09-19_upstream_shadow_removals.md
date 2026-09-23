# Upstream-shadow removals in the algebra and example layers

Date: 2026-09-19.

This audit records local declarations that restated a result already available
from Mathlib or from the QICLean dependency, together with the surviving
upstream declaration used in their place. It also records one layout change and
the material that was examined and deliberately retained.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `Matrix.isNilpotent_of_forall_trace_pow_eq_zero` (`TNLean/Algebra/IsNilpotentOfTracePow.lean`) | `Matrix.isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt` (`QICLean/Algebra/ShiftedZeroTraceNilpotent.lean`) |
| `MPOTensor.swapMatrix_isUnitaryBetween`, private (`TNLean/MPS/MPU/Examples/ShiftSwapMatrices.lean`) | `Matrix.swapMatrix_isUnitaryBetween` (`TNLean/Algebra/SwapMatrix.lean`) |
| `MPOTensor.mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one_of_card_eq`, private (`TNLean/MPS/MPDO/BNTTripleFusionSeparation.lean`) | `Matrix.mul_eq_one_comm_of_card_eq` |
| `MPOTensor.isNilpotent_smul`, private (`TNLean/MPS/MPDO/NeighboringTraceObstructionAmbientCounterexample.lean`) | `IsNilpotent.smul` |
| `TNLean.PEPS.sdiff_union_sdiff_of_subset` (`TNLean/PEPS/TorusWindowChain4.lean`) | `Finset.union_comm` composed with `Finset.sdiff_union_sdiff_cancel` |
| `TNLean.PEPS.sdiff_disjoint_sdiff` (same file) | `Finset.disjoint_sdiff` weakened along `Finset.sdiff_subset` |
| `TNLean.PEPS.sdiff_subset_sdiff_left` (same file) | `Finset.sdiff_subset_sdiff_left` |
| `TNLean.PEPS.sdiff_subset_sdiff_right` (same file) | `Finset.sdiff_subset_sdiff_right` |
| `Matrix.eq_sum_smul_single`, private (`TNLean/QCA/BipartiteSupportAlgebra.lean`) | `Matrix.matrix_eq_sum_single` together with `Matrix.smul_single` |
| `MPSTensor.cyclic_offset_eq_sub`, private (`TNLean/MPS/ParentHamiltonian/CyclicTranslation.lean`) | `Fin.val_sub` with an arithmetic side goal |
| `MPOTensor.vecMulVec_mulVec_eq_smul` (`TNLean/MPS/MPDO/CZXDefectMaps.lean`) | `Matrix.vecMulVec_mulVec` together with `op_smul_eq_smul` |

Every removed declaration was a pass-through of the corresponding upstream
result. The removals follow the pass-through exception of
`docs/project_conventions.md`, so no deprecation alias was introduced.

## Layout change

`TNLean/Algebra/Matrix/ScalarIdentity.lean` was the only module of the
`TNLean/Algebra/Matrix/` subdirectory, which therefore carried a generated
one-line aggregator `TNLean/Algebra/Matrix.lean`. The module moved to
`TNLean/Algebra/MatrixScalarIdentity.lean`, matching the spelling of the
sibling modules `MatrixSingleSpan` and `MatrixCyclicPathSum`, and the
aggregator was removed by regenerating the aggregator files. The three
declarations `Matrix.PosSemidef.smul_one`, `Matrix.PosDef.smul_one`, and
`Matrix.trace_smul_one` are unchanged, and the entry recording them in
`docs/tactic_patterns.md` now names the new path.

## What was checked

- Consumer census by name over the Lean sources for each removed declaration:
  the nilpotency matrix lemma was used only by the endomorphism transport in
  its own module; each remaining removal had exactly one consuming module.
- Blueprint exposure: none of the removed declarations appeared in a `\lean{}`
  payload. The endomorphism statement
  `LinearMap.isNilpotent_of_forall_trace_pow_eq_zero` keeps its name, its
  hypothesis for every positive exponent, and its tag; the shifted matrix
  hypothesis is used only inside its proof.
  `Matrix.swapMatrix_isUnitaryBetween` keeps its tag and gains its first
  consumer, so the proof of the four-spin unitarity node now cites it.
  `TNLean.PEPS.threeBlockBlueCoeff_comp` keeps its tag; only the subset proof
  terms appearing inside its statement changed, which leaves the statement the
  same proposition.
- Upstream availability: each replacement term was elaborated against the
  pinned Mathlib and QICLean before the edit, then the affected modules and
  their importers were compiled.

## Retained material

- `MPOTensor.one_isUnitaryBetween` in `ShiftSwapMatrices.lean` stays: neither
  Mathlib nor QICLean states unitarity of the identity matrix between
  coordinate spaces.
- `StarSubalgebra.exists_starAlgEquiv_matrix_and_finrank_of_isCentral` in
  `TNLean/Algebra/CentralStarSubalgebraMatrix.lean` stays. It adds the
  dimension identity for the matrix factor to the QICLean existence statement,
  its blueprint node asserts that identity, and it is staged for the
  support-algebra matrix-factor development, which is not yet formalized.
- The three scalar-identity matrix lemmas stay as declarations. They are the
  recorded abstraction of a repeated argument in `docs/tactic_patterns.md`, and
  only their module path changed.

## Deferred

- `Submodule.flagQuot`, `LinearMap.flagQuotMap`, and `LinearMap.flagQuotMap_mk`
  in `TNLean/Algebra/FlagBlockTriangular.lean` duplicate `Submodule.subquot`,
  `Submodule.subquotMap`, and `Submodule.subquotMap_mk` in
  `TNLean/Algebra/Subquotient.lean`: the two subquotient definitions have the
  same body, one stated over a ring and one over a field. Collapsing them
  rewrites about thirty occurrences inside the flag module and its multi-block
  consumer, both of which are under active development, so the rewrite is left
  for a separate change.
- (Landed 2026-09-23.) The private range-indexed two-sided multiplication
  lemma in `TNLean/PEPS/CycleMPSChainOverlapCapstone.lean` restated the
  set-indexed lemma of `TNLean/PEPS/CycleMPSOverlapCapstone.lean`. The chain
  module does not import the other capstone, so the surviving statement had
  to move to an earlier module before the duplicate could go. The set-indexed
  `TNLean.PEPS.conj_eq_conj_of_span` now lives in the chain module under its
  original name and the duplicate is deleted; recorded in
  `docs/audits/2026-09-23_hygiene_second_pass.md`.
