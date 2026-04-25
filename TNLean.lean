/-
# TNLean

Stable import surface for the maintained TNLean library.

This file imports the modules intended for downstream users. Most
specialized helper modules are still omitted from the root import list, but the
public chapter-index modules and the chapter-facing semigroup modules are
included so that blueprint links and the generated documentation can see
them.

The following legacy archival modules are intentionally excluded
(they live in `TNLean/Archive/`):

* the legacy bi-canonical periodicity wrappers
  `TNLean.Archive.PeripheralClosure` and `TNLean.Archive.BlockingPeriodicity`;
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
import TNLean.Algebra.BurnsideMatrix
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Algebra.MatrixFrobenius
import TNLean.Algebra.ProjectiveRepresentation
import TNLean.Algebra.ScalarCommutant
import TNLean.Algebra.CocycleCohomology

-- Layer 0b: General analysis
import TNLean.Analysis.ConvergenceHelpers

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

-- Layer 2c: Spectral theory (QPF + spectral gap)
import TNLean.QPF.PosDef
import TNLean.QPF.Uniqueness
import TNLean.QPF.Assembly
import TNLean.QPF.Primitive
import TNLean.Spectral.MixedTransfer
import TNLean.Spectral.MPVOverlapTrace
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.PrimitiveOverlap
import TNLean.Spectral.CrossCorrelation
import TNLean.Spectral.QuantitativeGap

-- Layer 3: MPS core
import TNLean.MPS.Defs
import TNLean.MPS.Chain.Defs
import TNLean.MPS.Chain.VirtualInsertion
import TNLean.MPS.Chain.TensorEquality
import TNLean.MPS.Chain.AlgebraIsomorphism
import TNLean.MPS.Chain.FundamentalTheorem
import TNLean.MPS.Chain.BlockedChainFT
import TNLean.MPS.Chain.SameStateBridge
import TNLean.MPS.Chain.TranslationInvariance
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Overlap.Basic
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
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.SuffixWindow
import TNLean.MPS.ParentHamiltonian.RestrictTransport
import TNLean.MPS.ParentHamiltonian.ExtendRight
import TNLean.MPS.ParentHamiltonian.WrappingWindow
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.ParentHamiltonian.DegenerateGS
import TNLean.Axioms.Beigi
import TNLean.MPS.ParentHamiltonian.Commuting
import TNLean.MPS.ParentHamiltonian.Decorrelation
import TNLean.MPS.ParentHamiltonian.Martingale

-- Layer 4: Fundamental theorem (single block)
import TNLean.MPS.Structure.LinearExtension
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.FundamentalTheorem.ProportionalPrimitive
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
import TNLean.Algebra.BlockTriangularTrace
import TNLean.Algebra.ProjectionTriangularTrace
import TNLean.MPS.BNT.BasisNormal
import TNLean.MPS.BNT.Basic
import TNLean.MPS.BNT.PermutationRigidityPrimitive
import TNLean.MPS.BNT.PermutationRigidity
import TNLean.MPS.BNT.Construction
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.MPS.Overlap.PeripheralToSpectralGap
import TNLean.MPS.CanonicalForm.FromPrimitive
import TNLean.MPS.FundamentalTheorem.EqualProportional
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.MPS.FundamentalTheorem.Full.Helpers
import TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap
import TNLean.MPS.FundamentalTheorem.Full.BlocksMatch
import TNLean.MPS.FundamentalTheorem.OverlapConvergenceAux
import TNLean.MPS.FundamentalTheorem.CoefficientConvergence
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.Periodic.ZGauge
import TNLean.MPS.Periodic.FundamentalTheorem
import TNLean.MPS.Periodic.Applications
import TNLean.MPS.Periodic.Symmetry
import TNLean.MPS.Periodic.ProjectiveRep
import TNLean.MPS.Structure.InvariantSubspaceDecomp
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.SectorIrreducibility
import TNLean.MPS.CanonicalForm.Assembly
import TNLean.MPS.CanonicalForm.Assembly.TPPrimitiveReduction
import TNLean.MPS.CanonicalForm.Assembly.NormalityChain
import TNLean.MPS.CanonicalForm.Assembly.PrimitiveBlocks
import TNLean.MPS.CanonicalForm.Assembly.CyclicSectorDecomposition
import TNLean.MPS.CanonicalForm.Assembly.StructuralTheorem
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.CanonicalForm.EqualNormBridge
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Periodic.Overlap
import TNLean.MPS.Periodic.CornerTransition
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Structure.BlockPermutation
import TNLean.PiAlgebra.Construction
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.PiAlgebra.BlockSeparation
import TNLean.PiAlgebra.TIReduction
import TNLean.PiAlgebra.GlobalSymmetry

-- Layer 3b: MPO / MPDO / LPDO foundations
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.MPDO.VerticalCF
import TNLean.MPS.MPDO.BiCFDerivation
import TNLean.MPS.MPDO.ZCL
import TNLean.MPS.MPDO.PRFP
import TNLean.MPS.MPDO.RFP
import TNLean.MPS.MPDO.SimpleLocalStructure
import TNLean.MPS.MPDO.FusionIsometries
import TNLean.MPS.MPDO.AlgebraStructure
import TNLean.MPS.MPDO.CommutingForm
import TNLean.MPS.MPDO.BlockedRFPConstruction

-- MPS examples
import TNLean.MPS.Examples.AKLT
import TNLean.MPS.Examples.EvenParity
import TNLean.MPS.Examples.GHZ
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

-- Layer 6a: Quantum Wielandt backend / span-growth infrastructure
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.SpanGrowth.NonzeroTraceProduct
import TNLean.Wielandt.FittingDecomposition
import TNLean.Wielandt.SpanGrowth.EigenvectorSpreading
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Wielandt.RankOne.Construction
import TNLean.Wielandt.RankOne.Products
import TNLean.Wielandt.WielandtBound

-- Layer 6b: Preferred paper-facing Proposition 3 / Theorem 1 endpoints
-- These wrappers remain standalone with respect to the canonical / FT / BNT
-- assembly above. `Prop3.lean` is the preferred Proposition 3 entry point; the
-- direction-specific files `Prop3_ac` and `Prop3_cb` remain available
-- transitively through `Prop3` for specialized use.
import TNLean.Wielandt.Primitivity.PaperDefinitions
import TNLean.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.PaperResults.NonzeroTraceWord
import TNLean.Wielandt.PaperResults.EigenvectorSpreading
import TNLean.Wielandt.PaperResults.MatrixSpanExistence
import TNLean.Wielandt.PaperResults.MatrixSpanSharpBound
import TNLean.Wielandt.PaperResults.WielandtInequality

-- Layer 6c: Conditional / backend Wielandt assembly
-- These modules support specialized span-growth and aperiodicity routes. They
-- are not on the active canonical / FT / BNT path, but they remain root-visible
-- where convenient for direct users.
import TNLean.Wielandt.SpanGrowth.InvertibleWordSpan
import TNLean.Wielandt.Primitivity.Normal
import TNLean.Wielandt.Primitivity.ToNormal
import TNLean.Wielandt.Primitivity.ImpliesIrreducible
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
import TNLean.Wielandt.QuantumWielandt

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
import TNLean.PEPS.VirtualInsertion
import TNLean.PEPS.Blocking
import TNLean.PEPS.LocalGauge
import TNLean.PEPS.FundamentalTheorem
