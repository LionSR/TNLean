# Spectral estimates and boundary edges in QICLean

The QICLean dependency advances from `40ad5ebdb7` to `8c016dc18a`. The spectral estimates
for arbitrary Hermitian matrices, the finite-chain truncation argument, and the graph boundary
counts now live in the corresponding layers of QICLean.

| Removed TNLean module | QICLean home |
| --- | --- |
| `Spectral.SpectralTail`, `Spectral.GroundStateTail` | `Spectral.Projection.ExponentialDrop` and `ManyBody.Hamiltonian.Chain.RegionalTruncation` |
| `Spectral.RegionalTruncationResidual`, `Spectral.TwoBlockTruncation` | `ManyBody.Hamiltonian.Chain.RegionalTruncation` and `Algebra.Combinatorics.FinSum` |
| `ProjectorFactorization.GaussianTimeAverage` | `Spectral.Filter.Gaussian.MatrixIntegral` and `ManyBody.Hamiltonian.GaussianFilter` |
| `Spectral.SupersiteHierarchy` | `Algebra.Combinatorics.DyadicBlock`, `ManyBody.Sites.Hierarchy.SupportedHierarchy`, and `Analysis.Norm.MatrixToEuclidean` |
| `Spectral.SupportedSpectralCutoff` | `ManyBody.Sites.Twirl` and the existing supported-operator theorems |
| `PEPS.AreaLaw.RectangularBoundary` | `ManyBody.Sites.Lattice.Rectangle` |

The two regional sums are named `threeRegionHamiltonians` and
`twoBlockTruncatedHamiltonian` in the `ManyBody.BondInteraction` namespace.
The Gaussian time average is the Gaussian intertwiner with right generator zero and input
the identity. Its variance is written as the nonnegative part of \(q / \Delta E^2\).
The placement theorem `ManyBody.cfc_place` commutes placement with the real functional
calculus of a regional self-adjoint matrix. The corresponding support and commutation
claims follow from `ManyBody.cfc_mem_supportedOperators` and
`ManyBody.commute_of_mem_supportedOperators_of_disjoint`. The graph predicates
`ManyBody.IsRegionBoundaryEdge` and `ManyBody.IsRegionIncidentEdge` and their incidence
lemmas live beside the definition of an edge.

## Dependency range

A comparison with the preceding pin finds 65 removed or renamed public declarations, three
declarations moved beyond the import closure of their old modules, and two deleted modules.
Nineteen of the removed declarations have TNLean uses. The three-region coordinate equivalences
now take the family of basis types as an argument, so a qudit dimension \(q\) is supplied
as the constant family `fun _ ↦ Fin q`. For the weighted Gaussian-source error, the blocks of a
rectangular matrix are obtained through `Matrix.comp`, and their combination is
`Matrix.halfWeightedBlockCombination`.

The range introduces fourteen names already declared in TNLean. Nine are the Hermitian-matrix
lemmas removed with the spectral modules. The five declarations below are removed from the
remaining lattice modules and supplied by QICLean.

| Declaration | QICLean home |
| --- | --- |
| `Matrix.toEuclideanLin_single_one_apply` | `Analysis.Norm.MatrixToEuclidean` |
| `Matrix.appendAuxiliaryVector`, `Matrix.partialTraceRight_appendAuxiliaryVector`, `Matrix.norm_appendAuxiliaryVector`, `Matrix.rectangularTraceNorm_appendAuxiliaryVector_error_le_two` | `Channel.Dilation.ChronologicalGarbage` |

The column-coordinate equality in QICLean permits rectangular matrices. The old statement is
its specialization at equal row and column index types. The four auxiliary-vector declarations
have the same types and explicit argument order as the TNLean declarations.
