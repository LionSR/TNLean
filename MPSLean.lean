-- Layer 0: General algebra
import MPSLean.TraceNondeg
import MPSLean.TracePairing
import MPSLean.BlockPermutation
import MPSLean.SkolemNoether

-- Layer 1: Quantum channels
import MPSLean.Channel.PositiveMap
import MPSLean.Channel.KadisonSchwarz
import MPSLean.Channel.CesaroFixedPoint
import MPSLean.CPPrimitive

-- Layer 2: Spectral theory (QPF + spectral gap)
import MPSLean.QPF.PosDef
import MPSLean.QPF.Uniqueness
import MPSLean.QuantumPerronFrobenius
import MPSLean.Spectral.MixedTransfer
import MPSLean.Spectral.SpectralGap
import MPSLean.Spectral.CrossCorrelation

-- Layer 3: MPS core
import MPSLean.Defs
import MPSLean.Transfer
import MPSLean.CanonicalForm

-- Layer 4: Fundamental theorem (single block)
import MPSLean.LinearExtension
import MPSLean.FundamentalTheorem

-- Layer 5: Multi-block
import MPSLean.MultiBlock
import MPSLean.BasisNormal
import MPSLean.FundamentalTheoremMulti
import MPSLean.BlockPermutationMPS
import MPSLean.PiAlgebra.Construction
import MPSLean.PiAlgebra.FundamentalTheoremComplete
import MPSLean.PiAlgebra.BlockSeparation
