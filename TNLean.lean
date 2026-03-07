-- Layer 0: General algebra
import TNLean.Algebra.TracePairing
import TNLean.Algebra.BlockPermutation
import TNLean.Algebra.SkolemNoether
import TNLean.Algebra.GramMatrixLI
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.Algebra.BurnsideMatrix
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Algebra.MatrixFrobenius

-- Layer 1: Generic convex/topological infrastructure
import TNLean.Topology.ConvexProjection
import TNLean.Topology.BrouwerProduct
import TNLean.Topology.CompactRetractFixedPoint

-- Layer 2: Quantum channels (general theory)
import TNLean.Channel.PositiveMap
import TNLean.Channel.DensityRetract

-- Layer 2a: Trusted topological input for Perron--Frobenius existence
import TNLean.Axioms.BrouwerFixedPointDensityMatrices

-- Layer 2b: Quantum channels (general theory)
import TNLean.Channel.KadisonSchwarz
import TNLean.Channel.MultiplicativeDomain
import TNLean.Channel.MultiplicativeDomainPowers
import TNLean.Channel.CesaroFixedPoint
import TNLean.Channel.Irreducible
import TNLean.Channel.PerronFrobeniusNormalization
import TNLean.Channel.PerronFrobeniusExistence
import TNLean.Channel.Schwarz
import TNLean.Channel.Primitive
import TNLean.Channel.PeripheralSpectrum
import TNLean.Channel.ConjugationSpectrum
import TNLean.Channel.PeripheralPowers
import TNLean.Channel.PeriodicityRemoval

-- Layer 2: Spectral theory (QPF + spectral gap)
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
import TNLean.MPS.CastLemmas
import TNLean.MPS.Blocking
import TNLean.MPS.MPVOverlap
import TNLean.MPS.Transfer
import TNLean.MPS.BlockingTransfer
import TNLean.MPS.BlockingPeriodicity
import TNLean.MPS.BlockingPeriodicityCFII2
import TNLean.MPS.TransferNormalization
import TNLean.MPS.FixedPointInvariantProjection
import TNLean.MPS.CPPrimitive

-- Layer 4: Fundamental theorem (single block)
import TNLean.MPS.LinearExtension
import TNLean.MPS.FundamentalTheorem
import TNLean.MPS.FundamentalTheoremProportional

-- Layer 5: Multi-block
import TNLean.MPS.MultiBlock
import TNLean.Algebra.BlockTriangularTrace
import TNLean.Algebra.ProjectionTriangularTrace
import TNLean.MPS.BasisNormal
import TNLean.MPS.BNT
import TNLean.MPS.BNTPermutationSimple
import TNLean.MPS.BNTPermutationThm44
import TNLean.MPS.BNTConstruction
import TNLean.MPS.PrimitivityBridge
import TNLean.MPS.PeripheralToSpectralGap
import TNLean.MPS.CanonicalFormFromPrimitive
import TNLean.MPS.FundamentalTheoremFull
import TNLean.MPS.CoefficientConvergence
import TNLean.MPS.FundamentalTheoremMulti
import TNLean.MPS.InvariantSubspaceDecomp
import TNLean.MPS.CanonicalFormReduction
import TNLean.MPS.CanonicalFormExistence1606
import TNLean.MPS.IrreducibleFormII
import TNLean.MPS.IrreducibleAdjoint
import TNLean.MPS.TPGaugeFromAdjointFixedPoint
import TNLean.MPS.BlockingPeriodicityCFII_viaAdjoint
import TNLean.MPS.BlockPermutationMPS
import TNLean.PiAlgebra.Construction
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.PiAlgebra.BlockSeparation

-- Layer 6: Quantum Wielandt bound (arXiv:0909.5347)
import TNLean.Wielandt.CumulativeSpan
import TNLean.Wielandt.NonzeroTraceProduct
import TNLean.Wielandt.FittingDecomposition
import TNLean.Wielandt.EigenvectorSpreading
import TNLean.Wielandt.Lemma2b
import TNLean.Wielandt.RankOneConstruction
import TNLean.Wielandt.RankOneProducts
import TNLean.Wielandt.WielandtBound
import TNLean.Wielandt.PrimitivityNormal
import TNLean.Wielandt.PrimitivityToNormal
import TNLean.Wielandt.PrimitiveImpliesIrreducible
import TNLean.Wielandt.RankOneElement
import TNLean.Wielandt.RankOneExtraction
import TNLean.Wielandt.RankOneSpanGrowth
import TNLean.Wielandt.RankOneManufacture
import TNLean.Wielandt.RectangularRanges
import TNLean.Wielandt.RectangularSpan
import TNLean.Wielandt.RankOneBoundedWord
import TNLean.Wielandt.RankOneExtractionFull
import TNLean.Wielandt.CumulativeToWordSpan
import TNLean.Wielandt.QuantumWielandt

-- NOTE: TNLean.PositiveMapSpectral, TNLean.TransferSpectral, and
-- TNLean.PiAlgebraExtension are backwards-compatible re-export hubs kept for
-- external downstream consumers. They are NOT imported here because every
-- module they re-export is already covered by the direct imports above.
