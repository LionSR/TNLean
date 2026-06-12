/-
# TNLean

Stable import surface for the maintained TNLean library.

This file imports the modules intended for downstream users. Most
specialized helper modules are still omitted from the root import list, but the
public chapter-index modules and the chapter-facing semigroup modules are
included so that blueprint links and the generated documentation can see
them.

The following archival modules are intentionally excluded
(they live in `TNLean/Archive/`):

* the archival alternate proof `TNLean.Archive.BlockingPeriodicityCFII2`;
* the documentary counterexample `TNLean.Archive.BlockSepCounterexample`.
-/

-- Layer 0: General algebra
import TNLean.Algebra.TracePairing
import TNLean.Algebra.BlockPermutation
import TNLean.Algebra.SkolemNoether
import TNLean.Algebra.GramMatrixLI
import TNLean.Algebra.HermitianHelpers
import TNLean.Algebra.MatrixSpectralDecomp
import TNLean.Algebra.LinearMapAux
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.Algebra.UnitModulusPowerSum
import TNLean.Algebra.BurnsideMatrix
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Algebra.MatrixFrobenius
import TNLean.Algebra.PerronFrobenius.RankOne
import TNLean.Algebra.ProjectiveRepresentation
import TNLean.Algebra.ScalarCommutant
import TNLean.Algebra.CocycleCohomology

-- Layer 0b: General analysis
import TNLean.Analysis.ConvergenceHelpers
import TNLean.Analysis.ProjectionGeometry

-- Layer 1: Generic convex/topological infrastructure
import TNLean.Topology.ConvexProjection
import TNLean.Topology.BrouwerProduct
import TNLean.Topology.CompactRetractFixedPoint

-- Layer 2: Quantum channels (general theory)
import TNLean.Channel.Basic
import TNLean.Channel.DensityRetract

-- Layer 2 (Ch. 2 infrastructure): Choi–Jamiolkowski, Kraus, Stinespring
import TNLean.Channel.PartialTrace
import TNLean.Channel.MaximallyEntangled
import TNLean.Channel.TensorMap
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.KrausRank
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.KrausUnitaryFreedom
import TNLean.Channel.Stinespring
import TNLean.Channel.OrderedCP
import TNLean.Channel.RadonNikodym
import TNLean.Channel.TransferMatrix
import TNLean.Channel.POVM
import TNLean.Channel.POVM.Uniqueness

-- Layer 2: Quantum entropy infrastructure (depends on Channel.Basic, Channel.PartialTrace)
import TNLean.Analysis.Entropy

-- Layer 2a: Density-matrix Brouwer fixed-point theorem used in Perron--Frobenius existence
import TNLean.Axioms.BrouwerFixedPoint
-- Layer 2a: Axiomatized entropy inequalities (strong subadditivity)
import TNLean.Axioms.Entropy
-- Layer 2a: `TNLean/Entropy/` namespace (issue #613) — entropy
-- declarations for the Simple MPDO RFP track (#236). SSA itself is sourced
-- from `TNLean.Axioms.Entropy`; the `TNLean.Entropy.*` modules
-- re-state the sanctioned entropy axioms under the Entropy namespace.
import TNLean.Entropy.VonNeumann
import TNLean.Entropy.StrongSubadditivity
import TNLean.Entropy.TripartiteTrace
import TNLean.Entropy.MarkovChain
import TNLean.Entropy.MutualInformation
-- Layer 2b: Axiomatized operator convexity/concavity results (pending upstream Mathlib)
import TNLean.Axioms.OperatorConvexity
-- Layer 2b: Trace convexity/concavity of matrix real powers (proved)
import TNLean.Analysis.OperatorConvexity
-- Layer 2b: Quantum channels (general theory)
import TNLean.Channel.Schwarz.KadisonSchwarz
import TNLean.Channel.Schwarz.PositiveMapProperties
import TNLean.Channel.Schwarz.Douglas
import TNLean.Channel.Schwarz.DiagonalJensen
import TNLean.Channel.Schwarz.OperatorJensenAux
import TNLean.Channel.Schwarz.OperatorConvexity
import TNLean.Channel.Schwarz.OperatorMonotone
import TNLean.Channel.Schwarz.AndoLieb
import TNLean.Channel.Schwarz.PositiveOnAbelian
import TNLean.Channel.Schwarz.SchwarzNormal
import TNLean.Channel.Schwarz.SchwarzSubnormal
import TNLean.Channel.Schwarz.SchwarzNotCP
import TNLean.Channel.Schwarz.TwoPositive
import TNLean.Channel.Schwarz.MultiplicativeDomain
import TNLean.Channel.Schwarz.MultiplicativeDomainPowers
import TNLean.Channel.Schwarz.MultiplicativeDomainFull
import TNLean.Channel.Schwarz.TraceCFC
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Channel.FixedPoint.ChoiEffros
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.Channel.FixedPoint.CornerAlgebra
import TNLean.Channel.FixedPoint.StationarySupport
import TNLean.Channel.FixedPoint.WedderburnDecomp
import TNLean.Channel.FixedPoint.Corollaries
import TNLean.Channel.Spectral.Support
import TNLean.Channel.Irreducible.Ergodicity
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Irreducible.Growth
import TNLean.Channel.Irreducible.Growth.Preservation
import TNLean.Channel.Irreducible.Growth.OneStep
import TNLean.Channel.Irreducible.Growth.KernelDescent
import TNLean.Channel.Irreducible.Growth.OrthogonalTrace
import TNLean.Channel.Irreducible.Growth.Exponential
import TNLean.Channel.PerronFrobenius.Normalization
import TNLean.Channel.PerronFrobenius.Existence
import TNLean.Channel.Irreducible.Similarity
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.Channel.Irreducible.SpectralRadius
import TNLean.Channel.Irreducible.FromSpectral
import TNLean.Channel.Schwarz.Basic
import TNLean.Channel.Primitive
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.Conjugation
import TNLean.Channel.Peripheral.Powers
import TNLean.Channel.Peripheral.PeriodicityRemoval
import TNLean.Channel.Peripheral.GroupStructure
import TNLean.Channel.Peripheral.CyclicGroup
import TNLean.Channel.Semigroup.RelaxationConditions

-- Layer 2c: Spectral theory (QPF + transfer-operator gaps)
import TNLean.QPF.PosDef
import TNLean.QPF.Uniqueness
import TNLean.QPF.Assembly
import TNLean.QPF.Primitive
import TNLean.Spectral.MixedTransfer
import TNLean.Spectral.MPVOverlapTrace
import TNLean.Spectral.TransferOperatorGap
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.TransferOperatorGapRect
import TNLean.Spectral.PrimitiveOverlap
import TNLean.Spectral.CrossCorrelation
import TNLean.Spectral.QuantitativeGap

-- Layer 3: MPS core
import TNLean.MPS.Defs
import TNLean.MPS.Core.RepeatedWord
import TNLean.MPS.Tactic.Basic
import TNLean.MPS.Chain.Defs
import TNLean.MPS.Chain.VirtualInsertion
import TNLean.MPS.Chain.TensorEquality
import TNLean.MPS.Chain.AlgebraIsomorphism
import TNLean.MPS.Chain.FundamentalTheorem
import TNLean.MPS.Chain.GaugePhase
import TNLean.MPS.Chain.BlockedChainFT
import TNLean.MPS.Chain.SameStateBridge
import TNLean.MPS.Chain.TranslationInvariance
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.SelfOverlapAux
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Core.OrthogonalProjectionInvariance
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint
import TNLean.MPS.Irreducible.FixedPointProjection
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Core.Correlations
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.Nonvanishing
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.SuffixWindow
import TNLean.MPS.ParentHamiltonian.BoundaryOverlap
import TNLean.MPS.ParentHamiltonian.RestrictTransport
import TNLean.MPS.ParentHamiltonian.ExtendRight
import TNLean.MPS.ParentHamiltonian.WrappingWindow
import TNLean.MPS.ParentHamiltonian.BoundaryStripping
import TNLean.MPS.ParentHamiltonian.BoundaryClosing
import TNLean.MPS.ParentHamiltonian.BoundaryClosingCoordinate
import TNLean.MPS.ParentHamiltonian.BoundaryClosingStripping
import TNLean.Axioms.Beigi
import TNLean.MPS.ParentHamiltonian.Commuting
import TNLean.MPS.ParentHamiltonian.Decorrelation
import TNLean.MPS.ParentHamiltonian.Martingale
-- The finite-chain uniqueness capstone is not part of this foundational layer.
-- Downstream files may import it when they need the periodic-chain definitions.

-- Layer 4: Fundamental theorem (single block)
import TNLean.MPS.Structure.LinearExtension
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.FundamentalTheorem.FiniteLength
-- Symmetry
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Symmetry.GaugeUniqueness
import TNLean.MPS.Symmetry.OnSiteSymmetry
import TNLean.MPS.Symmetry.VirtualRepresentation
import TNLean.MPS.Symmetry.CocycleCoboundary
import TNLean.MPS.Symmetry.SymmetricMPS
import TNLean.MPS.Symmetry.StringOrder

-- Layer 5: Multi-block
import TNLean.MPS.Core.MultiBlock
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.ParentHamiltonian.BNTBlockIntersection
import TNLean.MPS.ParentHamiltonian.CyclicSubmoduleIteration
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace
import TNLean.MPS.ParentHamiltonian.BlockDiagonalChainGroundSpace
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalChain
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalCrossing
import TNLean.Algebra.BlockTriangularTrace
import TNLean.Algebra.ProjectionTriangularTrace
import TNLean.MPS.BNT.Basic
import TNLean.MPS.BNT.Separation
import TNLean.MPS.BNT.PermutationRigidityPrimitive
import TNLean.MPS.BNT.Construction
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.MPS.Overlap.PeripheralToTransferMapGap
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.FundamentalTheorem.SectorWeightComparison
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.FundamentalTheorem.SectorBNT.CoeffIdentity
import TNLean.MPS.FundamentalTheorem.SectorBNT.CopyWeightMatching
import TNLean.MPS.FundamentalTheorem.SectorBNT.EqualModulus
import TNLean.MPS.FundamentalTheorem.SectorBNT.Fundamental
import TNLean.MPS.FundamentalTheorem.SectorBNT.FundamentalCoord
import TNLean.MPS.FundamentalTheorem.SectorBNT.StrongMatch
import TNLean.MPS.FundamentalTheorem.SectorBNT.WeightEquiv
import TNLean.MPS.FundamentalTheorem.SectorBNT.Api
import TNLean.MPS.FundamentalTheorem.SectorBNT.Examples
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch
import TNLean.MPS.FundamentalTheorem.SectorBNT.Supplier
import TNLean.MPS.Periodic.Overlap
import TNLean.MPS.Periodic.FundamentalTheorem
import TNLean.MPS.Periodic.ZGauge
import TNLean.MPS.Periodic.Symmetry
import TNLean.MPS.Periodic.ProjectiveRep
import TNLean.MPS.Periodic.Applications
import TNLean.MPS.Structure.InvariantSubspaceDecomp
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.Periodic.SectorIrreducibility
import TNLean.MPS.CanonicalForm.SectorComparison.CyclicSectorRelation
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Irreducible.ScalarFixedPoint
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Structure.BlockPermutation
import TNLean.PiAlgebra.Construction
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.PiAlgebra.TIReduction
import TNLean.PiAlgebra.GlobalSymmetry

-- Layer 3b: MPO / MPDO / LPDO foundations
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.MutualInfoMonotone
import TNLean.MPS.MPDO.PureAreaLaw
import TNLean.MPS.MPDO.VerticalCF
import TNLean.MPS.MPDO.BiCFDerivation
import TNLean.MPS.MPDO.ZCL
import TNLean.MPS.MPDO.RFP
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.MPDO.LocalPurificationRFP
import TNLean.MPS.MPDO.SimpleLocalStructure
import TNLean.MPS.MPDO.FusionIsometries
import TNLean.MPS.MPDO.AlgebraStructure
import TNLean.MPS.MPDO.BNTCoefficients
import TNLean.MPS.MPDO.BNTTheoremData
import TNLean.MPS.MPDO.BNTTheoremWitness
import TNLean.MPS.MPDO.BNTTheoremWitnessConsequences
import TNLean.MPS.MPDO.CommutingForm
import TNLean.MPS.MPDO.CommutingFormBridge
import TNLean.MPS.MPDO.BlockedRFPConstruction

-- MPS examples
import TNLean.MPS.Examples.AKLT
import TNLean.MPS.Examples.AKLTRotation
import TNLean.MPS.Examples.Cluster
import TNLean.MPS.Examples.EvenParity
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.Examples.GHZParentHamiltonian
import TNLean.MPS.Examples.ZMod2

-- Layer 5b: Renormalization fixed points (RFP) — pure-state scaffolding
import TNLean.MPS.RFP.Defs
import TNLean.MPS.RFP.ZeroCorrelationLength
import TNLean.MPS.MPDO.PureRecovery
import TNLean.MPS.RFP.StructuralForm
import TNLean.MPS.RFP.StructuralFull
import TNLean.MPS.RFP.CommutingBridge
import TNLean.MPS.RFP.Convergence
import TNLean.MPS.RFP.Assembly
import TNLean.MPS.RFP.Decorrelation

-- Layer 6a: Quantum Wielandt span-growth infrastructure
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.SpanGrowth.NonzeroTraceProduct
import TNLean.Wielandt.FittingDecomposition
import TNLean.Wielandt.SpanGrowth.EigenvectorSpreading
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Wielandt.RankOne.Construction
import TNLean.Wielandt.RankOne.Products
import TNLean.Wielandt.WielandtBound

-- Layer 6b: Proposition 3 and the quantum Wielandt inequality.
-- `Inequality/` records the bounds of arXiv:0909.5347 / Wolf §6.9 in their
-- standard notation. These declarations are independent of the MPS fundamental
-- theorem development above.
import TNLean.Wielandt.Primitivity.Definitions
import TNLean.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.PrimitiveBridge
import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.Inequality.NonzeroTraceWord
import TNLean.Wielandt.Inequality.EigenvectorSpreading
import TNLean.Wielandt.Inequality.MatrixSpanExistence
import TNLean.Wielandt.Inequality.MatrixSpanSharpBound
import TNLean.Wielandt.Inequality.Bounds

-- Layer 6c: Conditional Wielandt arguments
-- These modules support specialized span-growth and aperiodicity routes. They
-- are not on the active canonical / FT / BNT path, but they remain root-visible
-- where convenient for direct users.
import TNLean.Wielandt.SpanGrowth.InvertibleWordSpan
import TNLean.Wielandt.Primitivity.Normal
import TNLean.Wielandt.Primitivity.ToNormal
import TNLean.Wielandt.Primitivity.ImpliesIrreducible
import TNLean.Wielandt.Primitivity.TracePairing
import TNLean.Wielandt.RankOne.Element
import TNLean.Wielandt.RankOne.Extraction
import TNLean.Wielandt.RankOne.SpanGrowth
import TNLean.Wielandt.RankOne.Manufacture
import TNLean.Wielandt.RectangularSpan.Ranges
import TNLean.Wielandt.RectangularSpan.Basic
import TNLean.Wielandt.RectangularSpan.Growth
import TNLean.Wielandt.RectangularSpan.Universality
import TNLean.Wielandt.RankOne.BoundedWord
import TNLean.Wielandt.RankOne.ExtractionFull
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan

import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.Peripheral.Cycles
import TNLean.Channel.Peripheral.MultiCycleDecomposition

-- Chapter 2 §2.3 normal-form existence (SVD + Lorentz)
import TNLean.Channel.NormalForm

-- Public documentation index modules
import TNLean.Channel.WolfChapter2Index
import TNLean.Channel.WolfChapter6Index

-- Chapter 7 semigroup material exposed for blueprint/doc links
import TNLean.Channel.Semigroup.Basic
import TNLean.Channel.Semigroup.Perturbation
import TNLean.Channel.Semigroup.GeneratorDefs
import TNLean.Channel.Semigroup.LindbladForm
import TNLean.Channel.Semigroup.KossakowskiForm
import TNLean.Channel.Semigroup.Primitivity
import TNLean.Channel.Semigroup.LiouvillianKernel
import TNLean.Channel.Semigroup.ReducibleQDS
import TNLean.Channel.Determinant

-- PEPS (exploratory)
import TNLean.PEPS.Defs
import TNLean.PEPS.InjectiveRegion
import TNLean.PEPS.InjectiveRegionContraction
import TNLean.PEPS.FiniteKernelDescent
import TNLean.PEPS.VirtualInsertion
import TNLean.PEPS.SingletonRegion
import TNLean.PEPS.Blocking
import TNLean.PEPS.EdgeMiddlePhysical
import TNLean.PEPS.VertexComplement.Basic
import TNLean.PEPS.VertexComplement.KernelDescent
import TNLean.PEPS.RegionBlock.Basic
import TNLean.PEPS.RegionBlock.KernelDescent
import TNLean.PEPS.RegionBlock.UnionClosure
import TNLean.PEPS.NormalEdgeBlockingData
import TNLean.PEPS.NormalBlocking
import TNLean.PEPS.NormalEdgeGauge
import TNLean.PEPS.RegionBlock.Insertion
import TNLean.PEPS.SquareLatticeGraph
import TNLean.PEPS.TorusLatticeGraph
import TNLean.PEPS.TorusTranslation
import TNLean.PEPS.IsoTransport
import TNLean.PEPS.RegionTransport
import TNLean.PEPS.RegionTransportData
import TNLean.PEPS.RegionTransportInsertion
import TNLean.PEPS.RegionTransferCovariance
import TNLean.PEPS.SingletonEdgeBlockingData
import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.TorusRectangleRegion
import TNLean.PEPS.TorusEdgeBlockingRegion
import TNLean.PEPS.TorusEdgeBlockingCrossing
import TNLean.PEPS.TorusRectangleReferenceData
import TNLean.PEPS.TorusRectangleGauge
import TNLean.PEPS.TorusReferenceBlockingData
import TNLean.PEPS.TorusBlockingData
import TNLean.PEPS.TorusEdgeGauge
import TNLean.PEPS.TorusEdgeGaugeCovariance
import TNLean.PEPS.TorusConjCovarianceFamily
import TNLean.PEPS.TorusWitnessTransport
import TNLean.PEPS.TorusWitnessTranslate
import TNLean.PEPS.TorusWitnessCapstone
import TNLean.PEPS.NormalEdgeComplementCover
import TNLean.PEPS.NormalRectangleTiling
import TNLean.PEPS.NormalEdgeBlockingCoordinate
import TNLean.PEPS.NormalEdgeBlockingTranslated
import TNLean.PEPS.NormalEdgeBlockingInterior
import TNLean.PEPS.NormalEdgeSingleCrossing
import TNLean.PEPS.NormalSquarePEPSBlocking
import TNLean.PEPS.NormalEdgeBlockingMargins
import TNLean.PEPS.IdentityInsertion
import TNLean.PEPS.InsertionRealization
import TNLean.PEPS.InsertionCoefficientRealization
import TNLean.PEPS.PhysicalToVirtualCounterexample
import TNLean.PEPS.InsertionAlgebra
import TNLean.PEPS.LocalGauge
import TNLean.PEPS.TensorFactorScalar
import TNLean.PEPS.EdgeGaugeExtraction
import TNLean.PEPS.EdgeGaugeFamily
import TNLean.PEPS.TwoInjectiveComparison
import TNLean.PEPS.EdgeScalarSolve
import TNLean.PEPS.GaugeConsistencyConnectivityCounterexample
-- The injective PEPS Fundamental Theorem (arXiv:1804.04964, Theorem 2) capstone:
-- existence and uniqueness clauses, sorry-free and axiom-clean, now part of root.
import TNLean.PEPS.FundamentalTheorem
import TNLean.PEPS.FundamentalTheorem.Uniqueness
-- Region-insertion lemmas toward the normal PEPS Fundamental Theorem
-- (arXiv:1804.04964, Section 3, theorem labelled `normal`).
import TNLean.PEPS.NormalFundamentalTheorem
import TNLean.PEPS.RegionComplementComparison
import TNLean.PEPS.RegionScalarCondition
import TNLean.PEPS.TorusFundamentalTheorem
-- Region-blocked insertion-algebra isomorphism: the per-edge gauge engine for the
-- normal PEPS Fundamental Theorem (region analogue of the injective edge gauge).
import TNLean.PEPS.RegionBlock.Algebra
-- Region realization toward the region insertion transfer: the region/complement
-- closed-state decomposition feeding the region analogue of the physical-to-virtual
-- recovery.
import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.GaugeBridge
-- Region incidence product regrouped by edges: the region-restricted analogue of the
-- incident-edge product split, the foundational regrouping for the gauge-absorbed region
-- injectivity used by the normal PEPS Theorem 3 final comparison.
import TNLean.PEPS.RegionBlock.GaugeInjectivity
-- A gauge preserves blocked-region linear independence: the boundary coupling
-- factorization of the gauged blocked-region weight, its invertibility, and the
-- linear-independence transfer (the gauge-absorbed injectivity obligation of the
-- normal PEPS Theorem 3 final comparison).
import TNLean.PEPS.RegionBlock.GaugeInjectivity2
-- Region-level absorbed plain equality: turns the per-edge gauge's conjugation-form
-- region-inserted coefficient identity into the absorbed `applyGauge` form the region
-- comparison consumes (the first step of the normal PEPS Theorem 3 final comparison).
import TNLean.PEPS.RegionBlock.AbsorbedEquality
-- Region vertex-product split across an inserted site: the vertex-product half of
-- the block-granularity one-site quotient of the normal PEPS Fundamental Theorem.
import TNLean.PEPS.RegionBlock.InsertSplit
-- Inserted-site grouping by the local configuration at the inserted vertex: the
-- inserted-site tensor factored out of the residual region-vertex sum.
import TNLean.PEPS.RegionBlock.InsertResidual
-- Inserted-site scalar extraction: the per-vertex relation from the two region
-- proportionalities and linear independence of the smaller region's blocked family.
import TNLean.PEPS.RegionBlock.ScalarExtraction
-- Region-block scalar proportionalities from the edge-level absorbed equality: the
-- region-independence step feeding the region comparison its absorbed `hregion`.
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed
-- A single gauge family with the bare-edge absorbed equality at every torus edge,
-- read off the orientation-class coefficient-identity witness families.
import TNLean.PEPS.TorusEdgeAbsorbed
-- Translation covariance of the orientation-adapted absorbing gauge: the absorbing
-- gauges at two translates of one reference witness determine each other.
import TNLean.PEPS.TorusAbsorbedCovariance
-- The translation-covariant absorbed gauge family: the every-edge bare-edge absorbed
-- equality realized by one transported reference gauge per orientation class.
import TNLean.PEPS.TorusCovariantAbsorbedFamily
-- Translation covariance of the gauge-absorbed blocked weights: the comparison
-- proportionality scalar is the same at every translate of the comparison region.
import TNLean.PEPS.TorusGaugedWeightCovariance
-- A bond-dimension reindex preserves blocked-region linear independence.
import TNLean.PEPS.RegionBlock.ReindexInjectivity
-- The corner comparison region: the 3x3 square minus its corner, its insert-completed
-- square, the band decompositions of both complements, and their injectivity.
import TNLean.PEPS.TorusCornerRegion
-- The unconditional torus Fundamental Theorem: the covariant gauge family, the single
-- scalar, the per-vertex relation, and the scalar condition from the source hypotheses.
import TNLean.PEPS.TorusFundamentalTheorem2
-- Uniqueness of the torus gauge family up to a multiplicative constant: per-edge
-- proportionality of two absorbing families and the per-class transported constant.
import TNLean.PEPS.TorusGaugeUniqueness
-- Region physical realization: realizes a boundary-edge matrix insertion at the
-- in-region endpoint vertex and expresses it through region state vectors.
import TNLean.PEPS.RegionBlock.Realization
-- Region physical-to-virtual recovery: transfers the region realization across
-- `SameState` and isolates the conditional matrix-realization hypotheses.
import TNLean.PEPS.RegionBlock.Recovery2
-- Region spanning at the in-region endpoint and the region insertion transfer datum:
-- the state-vector coefficients span the local virtual space (row/column-rank
-- duality of the vertex-complement family), and a realized matrix transfer assembles
-- the `RegionInsertionTransfer` datum.
import TNLean.PEPS.RegionBlock.Recovery3
-- Incident-matrix form of the virtual pullback closes the matrix-structure hypothesis
-- `hform`: the region transfer matrix is the read-off of the pullback, so `hform` is the
-- read-off round-trip whenever the pullback is of incident-matrix form on the boundary leg.
import TNLean.PEPS.RegionBlock.Recovery4
-- Out-of-region endpoint of a boundary edge: the second endpoint feeding the region
-- resonate step; coincides with the in-region endpoint of `f` for the set complement.
import TNLean.PEPS.RegionBlock.Recovery5
import TNLean.PEPS.RegionBlock.Recovery6
-- The region resonate identity and the out-of-region-endpoint pin: the two endpoint
-- readings of the region-inserted coefficient agree on the second tensor's closed
-- state vectors, the region analogue of the resonate identity behind
-- `physical_to_virtual_insertion`.
import TNLean.PEPS.RegionBlock.Recovery7
-- Incident-matrix form to the realization bundle: the region physical-to-virtual
-- realization `RegionTransferRealizes` follows from the per-matrix incident-matrix
-- form of the virtual pullback, isolating the region resonate reconcile as the one
-- remaining mathematical content of the normal-PEPS recovery.
import TNLean.PEPS.RegionBlock.Recovery8
-- The region resonate reconcile: the virtual pullback of the transferred in-region
-- endpoint operator is of incident-matrix form on the boundary leg, the last gap
-- behind the normal-PEPS Fundamental Theorem.
import TNLean.PEPS.RegionBlock.Recovery9
import TNLean.PEPS.RegionBlock.Recovery10
import TNLean.PEPS.RegionBlock.Recovery11
-- Block-level image coincidence: under `SameState`, the range of the blocked-region
-- tensor map of a region is `SameState`-invariant given complement-block injectivity.
import TNLean.PEPS.RegionBlock.BlockRangeCoincidence
-- Region-injective conditional chain: the per-edge gauge from a coefficient transfer
-- (no single-vertex injectivity).
import TNLean.PEPS.RegionBlock.RegionReconcile
-- Block-frame coefficient transfer: the region-injective coefficient transfer from
-- the block-level image coincidence (no single-vertex injectivity).
import TNLean.PEPS.RegionBlock.BlockCoeffTransfer
-- Three-block resonate engine: ports the edge-level resonate engine to the three
-- injective region blocks (red/blue/complement) of a `NormalEdgeBlockingData`.
import TNLean.PEPS.RegionBlock.ThreeBlockReconcile
import TNLean.PEPS.RegionBlock.ThreeBlockResonate
import TNLean.PEPS.RegionBlock.ThreeBlockResonate2
import TNLean.PEPS.RegionBlock.ThreeBlockTransfer
import TNLean.PEPS.RegionBlock.BondLocalFromReconcile
import TNLean.PEPS.RegionBlock.UnionInjectivity
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneralBlue
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap2
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3b
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap4
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap5
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap6
import TNLean.PEPS.RegionBlock.CoarseThreeSite
import TNLean.PEPS.RegionBlock.CoarseThreeSite2
import TNLean.PEPS.RegionBlock.CoarseThreeSite3
import TNLean.PEPS.RegionBlock.CoarseThreeSite4
import TNLean.PEPS.RegionBlock.CoarseThreeSite5
import TNLean.PEPS.RegionBlock.CoarseThreeSite6
import TNLean.PEPS.RegionBlock.CoarseThreeSite7
import TNLean.PEPS.RegionBlock.CoarseThreeSite8
import TNLean.PEPS.RegionBlock.CoarseThreeSite9
import TNLean.PEPS.RegionBlock.CoarseThreeSite10
import TNLean.PEPS.RegionBlock.CoarseThreeSite11
import TNLean.PEPS.CoherentFrameInstance
import TNLean.PEPS.CoherentFrameInstance2
import TNLean.PEPS.NormalEdgeGaugeFamily
import TNLean.PEPS.NormalSquareInjectivity
-- The per-edge coefficient identity and absorbing gauge at interior edges of the
-- open square lattice, the open-lattice port of the torus per-edge witness layer.
import TNLean.PEPS.NormalSquareEdgeCoeff
import TNLean.PEPS.NormalSquareInteriorAbsorbedFamily
import TNLean.PEPS.NormalSquareComparisonRegion
-- The unconditional interior-window Fundamental Theorem on the open square lattice.
import TNLean.PEPS.NormalSquareFundamentalTheorem2
-- Shared blocking data for two normal PEPS tensors: the conjunction
-- region-injectivity predicate and its one-edge projections.
import TNLean.PEPS.NormalPairBlocking
-- The absorbed gauge family of a general normal PEPS blocking: the bare-edge
-- absorbed equality at every edge of an arbitrary finite simple graph.
import TNLean.PEPS.NormalAbsorbedFamily
-- The per-edge bond-dimension equality of two normal PEPS generating the same
-- state, derived from the blocking hypotheses by the isomorphism rigidity.
import TNLean.PEPS.NormalBondDimension
-- The per-vertex scalar of the general normal comparison: the one-site
-- comparison pair on a connected graph, including the degenerate regions.
import TNLean.PEPS.NormalComparisonScalar
-- The Fundamental Theorem for normal PEPS on a connected graph: the
-- scalar-free local gauge and its per-edge uniqueness up to a constant.
import TNLean.PEPS.NormalGeneralFundamentalTheorem
-- Arcs of consecutive sites on the cycle graph: the blocks of the
-- closed-chain MPS corollary of the normal PEPS Fundamental Theorem.
import TNLean.PEPS.CycleArcRegion
-- The cycle blocking data: per-edge three-block chains, one-site comparison
-- regions, and the single-crossing property on the closed chain.
import TNLean.PEPS.CycleBlockingData
-- The Fundamental Theorem for normal MPS on a closed chain: the MPS
-- corollary of the normal PEPS Fundamental Theorem, with gauge uniqueness.
import TNLean.PEPS.CycleFundamentalTheorem
-- The cycle-graph tensor of a translation-invariant MPS tensor and the
-- state bridge between graph-level coefficients and matrix-product traces.
import TNLean.PEPS.CycleMPSTensor
