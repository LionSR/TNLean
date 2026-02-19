-- Layer 0: General algebra
import MPSLean.Algebra.TraceNondeg
import MPSLean.Algebra.TracePairing
import MPSLean.Algebra.BlockPermutation
import MPSLean.Algebra.SkolemNoether
import MPSLean.Algebra.GramMatrixLI

-- Layer 1: Quantum channels (general theory)
import MPSLean.Channel.PositiveMap
import MPSLean.Channel.KadisonSchwarz
import MPSLean.Channel.CesaroFixedPoint
import MPSLean.Channel.Irreducible
import MPSLean.Channel.Schwarz
import MPSLean.Channel.PeripheralSpectrum
import MPSLean.Channel.Primitive
import MPSLean.Channel.FixedPoints
import MPSLean.Channel.Ergodic

-- Layer 2: Spectral theory (QPF + spectral gap)
import MPSLean.QPF.PosDef
import MPSLean.QPF.Uniqueness
import MPSLean.QuantumPerronFrobenius
import MPSLean.Spectral.MixedTransfer
import MPSLean.Spectral.MPVOverlapTrace
import MPSLean.Spectral.SpectralGap
import MPSLean.Spectral.CrossCorrelation

-- Layer 3: MPS core
import MPSLean.MPS.Defs
import MPSLean.MPS.MPVOverlap
import MPSLean.MPS.Transfer
import MPSLean.MPS.CanonicalForm
import MPSLean.MPS.CPPrimitive

-- Layer 4: Fundamental theorem (single block)
import MPSLean.MPS.LinearExtension
import MPSLean.MPS.FundamentalTheorem

-- Layer 5: Multi-block
import MPSLean.MPS.MultiBlock
import MPSLean.MPS.BasisNormal
import MPSLean.MPS.FundamentalTheoremMulti
import MPSLean.MPS.BlockPermutationMPS
import MPSLean.PiAlgebra.Construction
import MPSLean.PiAlgebra.FundamentalTheoremComplete
import MPSLean.PiAlgebra.BlockSeparation

-- NOTE: MPSLean.PositiveMapSpectral, MPSLean.TransferSpectral, and
-- MPSLean.PiAlgebraExtension are backwards-compatible re-export hubs kept for
-- external downstream consumers. They are NOT imported here because every
-- module they re-export is already covered by the direct imports above.
