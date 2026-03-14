/-
# TNLean

Stable import surface for the maintained TNLean library.

This file re-exports the modules intended for downstream users. A few
specialized helper or documentary modules are intentionally omitted from the
root import list; they remain available via direct imports when needed.

The following legacy or documentary modules are intentionally excluded
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
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.Algebra.BurnsideMatrix
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Algebra.MatrixFrobenius

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
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.Stinespring

-- Layer 2a: Density-matrix Brouwer fixed-point theorem used in Perron--Frobenius existence
import TNLean.Axioms.BrouwerFixedPoint

-- Layer 2b: Quantum channels (general theory)
import TNLean.Channel.Schwarz.KadisonSchwarz
import TNLean.Channel.Schwarz.PositiveMapProperties
import TNLean.Channel.Schwarz.PositiveOnAbelian
import TNLean.Channel.Schwarz.SchwarzNormal
import TNLean.Channel.Schwarz.MultiplicativeDomain
import TNLean.Channel.Schwarz.MultiplicativeDomainPowers
import TNLean.Channel.Schwarz.MultiplicativeDomainFull
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.Channel.Irreducible.Ergodicity
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Irreducible.Growth
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

-- Layer 2c: Spectral theory (QPF + spectral gap)
import TNLean.QPF.PosDef
import TNLean.QPF.Uniqueness
import TNLean.QPF.Assembly
import TNLean.Spectral.MixedTransfer
import TNLean.Spectral.MPVOverlapTrace
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.PrimitiveOverlap
import TNLean.Spectral.CrossCorrelation

-- Layer 3: MPS core
import TNLean.MPS.Defs
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint
import TNLean.MPS.FundamentalTheorem.TransferNormalization
import TNLean.MPS.Irreducible.FixedPointProjection
import TNLean.MPS.Core.CPPrimitive

-- Layer 4: Fundamental theorem (single block)
import TNLean.MPS.Structure.LinearExtension
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.FundamentalTheorem.Proportional

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
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.MPS.FundamentalTheorem.CoefficientConvergence
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.Structure.InvariantSubspaceDecomp
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.CanonicalForm.NormalPipeline
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.Assembly
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Structure.BlockPermutation
import TNLean.PiAlgebra.Construction
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.PiAlgebra.BlockSeparation

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

-- Wolf Chapter 2 index (documentation-only re-export; no new proofs)
import TNLean.Channel.WolfChapter2Index

-- Wolf Chapter 6 index (documentation-only re-export; no new proofs)
import TNLean.Channel.WolfChapter6Index
