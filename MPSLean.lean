-- Layer 0: General algebra
import MPSLean.Algebra.TracePairing
import MPSLean.Algebra.BlockPermutation
import MPSLean.Algebra.SkolemNoether
import MPSLean.Algebra.GramMatrixLI
import MPSLean.Algebra.ScalarPowerSumIdentity

-- Layer 1: Quantum channels (general theory)
import MPSLean.Channel.PositiveMap
import MPSLean.Channel.KadisonSchwarz
import MPSLean.Channel.CesaroFixedPoint
import MPSLean.Channel.Irreducible
import MPSLean.Channel.Schwarz
import MPSLean.Channel.Primitive

-- Layer 2: Spectral theory (QPF + spectral gap)
import MPSLean.QPF.PosDef
import MPSLean.QPF.Uniqueness
import MPSLean.QPF.Assembly
import MPSLean.Spectral.MixedTransfer
import MPSLean.Spectral.MPVOverlapTrace
import MPSLean.Spectral.SpectralGap
import MPSLean.Spectral.MPVOverlapDecay
import MPSLean.Spectral.SpectralGapRect
import MPSLean.Spectral.PrimitiveOverlap
import MPSLean.Spectral.CrossCorrelation

-- Layer 3: MPS core
import MPSLean.MPS.Defs
import MPSLean.MPS.CastLemmas
import MPSLean.MPS.Blocking
import MPSLean.MPS.MPVOverlap
import MPSLean.MPS.Transfer
import MPSLean.MPS.TransferNormalization
import MPSLean.MPS.FixedPointInvariantProjection
import MPSLean.MPS.CPPrimitive

-- Layer 4: Fundamental theorem (single block)
import MPSLean.MPS.LinearExtension
import MPSLean.MPS.FundamentalTheorem
import MPSLean.MPS.FundamentalTheoremProportional

-- Layer 5: Multi-block
import MPSLean.MPS.MultiBlock
import MPSLean.Algebra.BlockTriangularTrace
import MPSLean.Algebra.ProjectionTriangularTrace
import MPSLean.MPS.BasisNormal
import MPSLean.MPS.BNT
import MPSLean.MPS.BNTPermutationSimple
import MPSLean.MPS.BNTPermutationThm44
import MPSLean.MPS.BNTConstruction
import MPSLean.MPS.FundamentalTheoremFull
import MPSLean.MPS.CoefficientConvergence
import MPSLean.MPS.FundamentalTheoremMulti
import MPSLean.MPS.InvariantSubspaceDecomp
import MPSLean.MPS.CanonicalFormReduction
import MPSLean.MPS.IrreducibleFormII
import MPSLean.MPS.BlockPermutationMPS
import MPSLean.PiAlgebra.Construction
import MPSLean.PiAlgebra.FundamentalTheoremComplete
import MPSLean.PiAlgebra.BlockSeparation

-- NOTE: MPSLean.PositiveMapSpectral, MPSLean.TransferSpectral, and
-- MPSLean.PiAlgebraExtension are backwards-compatible re-export hubs kept for
-- external downstream consumers. They are NOT imported here because every
-- module they re-export is already covered by the direct imports above.
