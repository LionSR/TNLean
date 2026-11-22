# Tensor-power consolidation integration

PR #10697 continues the existing integration at
`328bd2c2c4ce87ccfa252e6f88b163989030df12` (tree
`f55525313b1baf29cfeba26e0d4fa0bbc73f2256`) on main
`77ec6436a9bf651b19d014de8523826a40aef3c4`. PR #10676 is already merged.
PR #10684 stays open and unchanged as a superseded coverage record.

This uses the declaration-removal policy in `docs/project_conventions.md`:
all non-Archive callers and blueprint tags move to the shared declarations,
without deprecated aliases. Mathematical hypotheses and conclusions are
unchanged under these definitionally equal substitutions.

| Removed declaration | Replacement |
| --- | --- |
| `MPOTensor.sitewisePhysicalMatrix V N` | `Matrix.tensorPower N V` |
| `MPOTensor.sitewisePhysicalMatrix_mul` | `Matrix.tensorPower_mul` |
| `MPOTensor.sitewisePhysicalMatrix_conjTranspose` | `Matrix.conjTranspose_tensorPower` |
| `MPOTensor.sitewisePhysicalMatrix_one` | `Matrix.tensorPower_one` |
| `MPOTensor.sitewiseMatrixFamily` | `Matrix.rectKronecker` |
| `MPOTensor.sitewiseMatrixFamily_mul` | `Matrix.rectKronecker_mul` |
| private `sitewiseMatrixFamily_one` | `Matrix.rectKronecker_one` |
| private `sitewiseMatrixFamilyMonoidHom` | private `piKroneckerMonoidHom` |
| `MPOTensor.siteProduct` and private `chainPower`, `rectangularProduct` | `Matrix.tensorPower` |
| `siteProduct_mul`, `chainPower_mul` | `Matrix.tensorPower_mul` |
| `siteProduct_one`, `chainPower_one` | `Matrix.tensorPower_one` |
| `chainPower_conjTranspose`, `rectangularProduct_conjTranspose` | `Matrix.conjTranspose_tensorPower` |
| `rectangularProduct_isIsometry` | `Matrix.IsIsometry.tensorPower` |
| `rectangularProduct_isUnitaryBetween` | `Matrix.IsUnitaryBetween.tensorPower` |
| `chainPower_mem_unitaryGroup` | `Matrix.tensorPower_mem_unitaryGroup` |

The surviving theorems whose names contain `sitewisePhysicalMatrix` are
renamed by replacing that component with `tensorPower`. This includes
`sitewisePhysicalMatrix_isometry`, `sitewisePhysicalMatrix_mul_conjTranspose`,
`sitewisePhysicalMatrix_isHermitian`, `singleKrausMap_sitewisePhysicalMatrix_mpo`,
`singleKrausMap_sitewisePhysicalMatrix_physCloseN`, the reindexing lemmas,
the two-site projection lemmas, and the inclusion, loop-product and common
fixed-point helpers. The surviving names containing `sitewiseMatrixFamily`
replace that component with `rectKronecker`, including
`sitewiseMatrixFamily_mulSingle` and
`prod_embedLocalOperator_one_eq_sitewiseMatrixFamily`.

Current main added five consumers since the temporary integration:
`PhysicalMatrixSymmetry`, `PhysicalMatrixBlocking`,
`PhysicalMatrixSymmetryTransport`, `FundamentalTheoremGatesSupplied`, and
`Examples/SwapAncillaCompatibility`. They now use the same API.
The public regrouping theorem becomes `MPOTensor.reindex_piKronecker_blockKron`,
and its existing blueprint tag follows that rename.

The `SitewisePhysicalMatrix` isometry proof retains the measured fast form:
rewrite adjoint, multiplication and the one-site hypothesis, then close by
`exact Matrix.tensorPower_one N`. The two shortened #10676 proofs survive;
its other Algebra and PEPS changes are identical to current main.

The unitary-group theorem is derived from `IsUnitaryBetween.tensorPower`
through `isUnitaryBetween_iff_mem_unitaryGroup`; it repeats no unitarity proof.
The promoted ledger entry subsumes the old MPU candidate while preserving
current-main promotions. The remaining entrywise MPDO isometry candidate is
recorded once. Site-dependent products continue to use `rectKronecker`;
no parallel constant-factor unitary API from #10684 is added.

The two existing distributed-compression regressions import their actual
production dependencies, `Lattice.Compression.CorrectedPositionCost` and
`Lattice.Compression.DistributedLinks`, instead of the entire PEPS approximation
aggregator. Their examples, hypotheses, proofs and axiom queries are unchanged.
This removes the unrelated aggregator-build requirement and selects both scripts
for the existing focused and strict CI checks on this repair head.

Full exact-head CI and fresh proof and blueprint reviews remain merge gates.
The earlier temporary-tree checks do not establish those gates.

## Blueprint review follow-up, 2026-11-17

The three review findings on `ef188899` concern dependencies on tensor powers
and their adjoint law. Each declaration must keep one blueprint owner: adding
its `\lean{}` tag at every consumer recreates the duplicate-tag failure
previously fixed in this PR. `Matrix.tensorPower` remains on
`def:mpdo_sitewise_physical_matrix`. The generic product, adjoint and identity
laws now share the supporting entry `lem:mpdo_tensor_power_laws`, without
the unrelated spectral assumptions of the former shared-estimates entry.

The gate-sufficiency and cyclic neighboring-operator proofs cite that lemma
through `\uses` and mathematical references. The non-normal pair-state
definition cites the tensor-power definition. The shared overlap estimates
also depend on the generic laws and retain all their mathematical statements. No Lean declaration, theorem statement or proof is changed.
