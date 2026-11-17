# QICLean pin 49b9aa93: the Dynamics deletions and the follow-ups

Date: 2026-11-17.

This audit records the TNLean side of moving the QICLean pin from
`e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19` to `49b9aa933615d4a9ce663f94d2556a93ce7b76ea`, past QICLean's
Dynamics, Hamiltonian and lattice-geometry layers (LionSR/QICLean#1063, #1064,
#1067, #1079, #1082, #1084, #1085, #1086, #1087, #1088 and #1095; issue LionSR/QICLean#1062). Tracker:
#10718; the rule is the section "No dual systems" of
`docs/many_body_circuit_architecture.md`. The toolchain, Mathlib and every other
shared package do not move.

The pin move deletes what the range duplicates in the Dynamics layer. The
lattice geometry and the Hamiltonian structures are duplicated too, but their
TNLean definitions have hundreds of consumers each; they are listed below as
follow-ups, one pull request per notion, each deleting the TNLean definition in
the same pull request that ports its consumers.

## Deleted in the pin move

| Deleted TNLean module | QICLean module |
|---|---|
| `Circuit/LiebRobinson/CommutatorRecursion` | `ManyBody/Dynamics/CommutatorRecursion`, `ManyBody/Dynamics/HeisenbergEvolution` |
| `Circuit/LiebRobinson/ComponentLocality` | `ManyBody/Dynamics/ComponentLocality` |
| `Circuit/LiebRobinson/GraphPropagation` | `ManyBody/Dynamics/GraphPropagation` |
| `Circuit/LiebRobinson/GraphLocalization` | `ManyBody/Dynamics/GraphLocalization`, `ManyBody/Dynamics/GraphBall` |
| `Circuit/LiebRobinson/GraphBallStabilization` | `ManyBody/Dynamics/GraphBall` |
| `Circuit/LiebRobinson/SupportSeparation` | `ManyBody/Dynamics/GraphBall` |
| `Circuit/LiebRobinson/TimeScaling` | `ManyBody/Dynamics/HeisenbergEvolution` |
| `Circuit/LiebRobinson/Volterra` | `Analysis/Volterra` |
| `Circuit/ProjectedRelativeEvolution` | `ManyBody/Dynamics/ProjectedRelativeEvolution` |
| `Circuit/DisjointRelativeEvolution` | `ManyBody/Dynamics/DisjointRelativeEvolution`, `Analysis/UnitaryEvolution` |
| `Circuit/SupportedGaussianIntegral` | `ManyBody/Dynamics/SupportedGaussianIntegral` |

The names are `ManyBody.<name>` for the former `QuantumCircuit.<name>`; the root
declarations `norm_commutator_le`, `norm_exp_commutator_eq` and the four Volterra
comparisons, and `MatrixEvolution.hasDerivAt_ordered_prod_of_commute`, keep their
names. `QuantumCircuit.heisenbergEvolution_eq_hermitianUnitaryPath` has no
replacement: `ManyBody.heisenbergEvolution` unfolds to the unitary-path form.
`QuantumCircuit.mem_supportedOperators_of_forall_commute`
(`Circuit/SiteExpectationOrder`) is replaced by
`ManyBody.mem_supportedOperators_iff_forall_commute.mpr`, which needs no
positive local dimension. From LionSR/QICLean#1086, `Matrix.l2_opNorm_kronecker_le`
(`Algebra/MatrixKroneckerContraction`) and `Matrix.l2_opNorm_reindex_le`
(`Algebra/MatrixL2Contraction`) are QICLean's under the same names and
statements, and `Matrix.l2_opNorm_one_kronecker_rect_le` is QICLean's
`Matrix.l2_opNorm_one_kronecker_le`, generalized to rectangular matrices; its
eight consumers use the QICLean name. `Matrix.l2_opNorm_kronecker_le_one` has no
QICLean counterpart and stays. From LionSR/QICLean#1095,
`Matrix.IsHermitian.posSemidef_sub_smul_one_of_le_eigenvalues`
(`Algebra/KroneckerLeastEigenvalue`) is QICLean's, moved unchanged to
`ManyBody/Hamiltonian/GroundSpace`. `Matrix.finKronecker_mul` (`Algebra/FinKronecker`) is QICLean's
(`Analysis/FiniteKroneckerPowers`), stated in the opposite orientation, so its ten
consumer modules rewrite in the other direction.

The QICLean statements take an interaction `Φ : ManyBody.Interaction X T` and
regions `Finset V`. The TNLean consumers keep their statements: each builds
`Φ := ⟨h, fun k ↦ isSupportedOn_of_mem_supportedOperators (hSupport k)⟩` at the
call and converts its supports with the two lemmas of `Circuit/EntropySupport`.
`ManyBody.graphBall` is defined from `SimpleGraph.ball`; the three scanner
modules that unfolded the old filter definition use `ManyBody.mem_graphBall`.

### What stays, and why

`siteExpectation q K` and `ManyBody.regionExpectation K` are two definitions of
one normalized partial trace. The new module
`Circuit/SiteExpectationGraphLocalization` proves them equal
(`QuantumCircuit.siteExpectation_eq_regionExpectation`) and keeps
`QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphBall_le` and
`QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le`, now
the QICLean region-expectation estimates rewritten along that equation, for
their 53 consumers stated with `siteExpectation`. The QICLean projected and
disjoint relative evolutions and the supported Gaussian integral take
region-expectation bounds; their five TNLean consumers (`Hastings/BoundaryLocalization`,
`Huang/GridPropagation`, the three `SupportedGaussianIntegral` modules) feed
them site-expectation bounds through the same equation, and keep their
site-expectation statements. `QuantumCircuit.norm_sub_siteExpectation_le` stays
in `Circuit/SiteExpectation`. All three, with the equation, go in F12.

## Follow-ups

Module counts are of `origin/main` at `868d2c9`, by word match of the
identifiers; for the generic words `Edge` and `interval`, which also occur in
prose and in unrelated names, they are the counts of the TNLean declarations'
uses from the tracker. Each follow-up recounts. Order: F1 first; F8 needs F4–F7
and F9; F14 lands before the pin move that brings in QICLean's circuit core.

| | TNLean notion | QICLean replacement | Modules |
|---|---|---|---|
| F1 | `Edge` | `ManyBody.Edge` | 486 |
| F2 | `SquareLatticeVertex`, `PEPS/SquareLatticeGraph` | `ManyBody.SquareLatticeVertex`, `ManyBody.squareLatticeGraph` | 55 / 39 |
| F3 | `MPS.AreaLaw.interval` | `ManyBody.interval` | 347 |
| F4 | `IsChainSupport`, `ChainSupport` | `ManyBody.IsChainSupport`, `ManyBody.ChainSupport` | 29 |
| F5 | `sitePos`, the MPS `domainGraph`, `DomainSupport` | `ManyBody.sitePos`, `ManyBody.lineDomainGraph`, `ManyBody.DomainSupport` | 4 / 10 / 8 |
| F6 | `Lattice.domainGraph`, `AdmissibleSupport` | `ManyBody.planeDomainGraph`, `ManyBody.AdmissibleSupport` | 111 / 82 |
| F7 | the `RectangleInteraction` and `SquareInteraction` index types, `ForwardEdge`, `ForwardAdjacent`, `forwardSquareEdgeEquiv` | `ManyBody.SquareLatticeSiteOrEdge` | 12 |
| F8 | `ChainHamiltonian`, `DomainHamiltonian`, `LocalHamiltonian`, `RectangularHamiltonian`, `SquareHamiltonian` | `ManyBody.ChainInteraction`, `DomainInteraction`, `PlaneInteraction`, `RectangleInteraction`, `SquareInteraction`, with the former fields (Hermiticity, norm bounds) as hypotheses; one pull request each | 80 / 9 / 108 / 3 / 32 |
| F9 | `SquareHamiltonian.hermitianTerm`, `RectangularHamiltonian.hermitianTerm` and their lemmas | `ManyBody.Interaction.hermitianPart` | 5 |
| F10 | `Lattice.groundEigenspace` | `ManyBody.groundSpace` | 25 |
| F11 | `Matrix.IsGappedGroundState` | `ManyBody.IsGapped` with `groundSpace = span {Ω}`, through `ManyBody.isGapped_and_groundSpace_eq_span_iff` | 186 |
| F12 | `QuantumCircuit.siteExpectation`; deletes `QuantumCircuit.siteExpectation_eq_regionExpectation`, the one translating lemma admitted by this pin PR against the migration rules; with it the transitional bridge `QuantumCircuit.siteExpectation_eq_regionExpectation`, the corollaries through it `QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphBall_le` and `QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le`, its uses in `MPS/AreaLaw/Hastings/BoundaryLocalization`, `MPS/AreaLaw/Huang/GridPropagation`, `MPS/AreaLaw/SupportedGaussianIntegral`, `MPS/AreaLaw/DomainSupportedGaussianIntegral` and `PEPS/AreaLaw/SupportedGaussianIntegral`, and `QuantumCircuit.norm_sub_siteExpectation_le` | `ManyBody.regionExpectation`, `ManyBody.norm_sub_regionExpectation_le` | 53 |
| F12 | `QuantumCircuit.siteExpectation`; with it the transitional bridge `QuantumCircuit.siteExpectation_eq_regionExpectation`, the corollaries through it `QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphBall_le` and `QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le`, its uses in `MPS/AreaLaw/Hastings/BoundaryLocalization`, `MPS/AreaLaw/Huang/GridPropagation`, `MPS/AreaLaw/SupportedGaussianIntegral` (graph, chain and domain statements) and `PEPS/AreaLaw/SupportedGaussianIntegral`, and `QuantumCircuit.norm_sub_siteExpectation_le` | `ManyBody.regionExpectation`, `ManyBody.norm_sub_regionExpectation_le` | 53 |
| F13 | `Entropy.crossingTerms` (QICLean's temporary export) | `ManyBody.crossingTerms` | 35 |
| F14 | `QuantumCircuit.Layer`, the ring abbreviation `BondLayer d ringBond` (`Circuit/LocalCircuit`), which collides with the `QuantumCircuit.Layer` of QICLean's circuit core (step 3C.1) | renamed `QuantumCircuit.RingLayer`, with no alias, before the pin move that brings in the core; the modules that open `QuantumCircuit` are checked for unqualified `Circuit`, `Geometry`, `GateFamily`, `Interpretation` and `KrausGate` | 13 |
| F15 | `Matrix.toEuclideanLin_reindex_piLpCongrLeft` (`Algebra/MatrixReindexGap`), the statement of `ManyBody.toEuclideanLin_reindex_piLpCongrLeft` (LionSR/QICLean#1095) under another namespace | `ManyBody.toEuclideanLin_reindex_piLpCongrLeft` | 3 |

After F12, move the general Lieb–Robinson statements (i) and (ii) to QICLean `ManyBody/Dynamics` over `regionExpectation` at the next pin: `TNLean.MPS.AreaLaw.norm_heisenberg_commutator_le_graphDistance_inf` and `TNLean.MPS.AreaLaw.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le_of_sphere_le_two` in `MPS/AreaLaw/LiebRobinson.lean`, with the chain and domain corollaries left in TNLean.

F4 keeps three TNLean lemmas about QICLean's chain supports under their TNLean names and applies them explicitly instead of by dot notation: `TNLean.MPS.AreaLaw.IsChainSupport.exists_boundary_window_of_split` (`MPS/AreaLaw/BoundaryCounting`), `TNLean.MPS.AreaLaw.IsChainSupport.eq_interval_of_splits_of_range_one` (`MPS/AreaLaw/RangeOneCut`) and `TNLean.MPS.AreaLaw.ChainSupport.edist_le` (`MPS/AreaLaw/LiebRobinson`). They are chain geometry and move to QICLean `ManyBody/Sites/Lattice/Chain`; after that pin, delete the TNLean copies and restore dot notation.
