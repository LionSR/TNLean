/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWDimensionConstant.MarkovSpectrum
import TNLean.MPS.Structure.PrimitiveFixedPoint
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral
import QICLean.Algebra.MatrixAux

/-!
# The faithful primitive fixed point of the Markov example

The uniform density matrix is the stationary state of the doubly stochastic
matrix-unit tensor. Its one-site injectivity and transfer spectrum give the
complementary spectral gap required by the FNW estimates.
-/

open scoped ComplexOrder

namespace MPSTensor.FNWDimensionConstant

/-- The uniform density matrix on the four-dimensional auxiliary space. -/
noncomputable def markovDensity : Matrix (Fin 4) (Fin 4) ℂ := (1 / 4 : ℂ) • 1

/-- The stationary density is faithful. -/
theorem markovDensity_posDef : markovDensity.PosDef := by
  simpa [Matrix.faithfulDensity, markovDensity, one_div] using
    Matrix.faithfulDensity_posDef (Fin 4)

/-- The stationary density has trace one. -/
theorem markovDensity_trace : Matrix.trace markovDensity = 1 := by
  norm_num [markovDensity, Matrix.trace_smul]

/-- Double stochasticity fixes the uniform density. -/
theorem markovDensity_fixed : Kraus.transferMap markovTensor markovDensity = markovDensity := by
  simp only [markovDensity, map_smul, markovTensor_transferMap_one]

/-- The Markov tensor satisfies the faithful primitive fixed-point hypotheses
of the FNW projector estimate. -/
theorem markovTensor_isPrimitiveMPS : IsPrimitiveMPS markovTensor markovDensity := by
  have hne : markovDensity ≠ 0 := fun h ↦ by
    have := markovDensity_trace
    simp [h] at this
  have hfix := markovDensity_fixed
  have hprim : _root_.IsPrimitive (Kraus.transferMap markovTensor) :=
    isPrimitive_of_unique_norm_one _ markovDensity hfix hne fun ν hν hnorm ↦
      (eq_or_ne ν 1).resolve_right fun hν1 ↦ by
        simp only [markovTensor_fnwTransfer_eigenvalue_eq_zero
          (by simpa only [fnwTransferMap_eq_traceAdjointMap,
            Matrix.traceAdjointMap_hasEigenvalue_iff] using hν) hν1, norm_zero,
          zero_ne_one] at hnorm
  obtain ⟨htr, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap markovTensor)
      (Kraus.isChannel_mapLM markovTensor markovTensor_isTP)
      (Kraus.injective_implies_irreducibleCP markovTensor markovTensor_isInjective)
      hprim markovDensity markovDensity_posDef.posSemidef hne hfix
  exact ⟨markovTensor_isTP, hne, markovDensity_posDef.posSemidef, hfix, hgap⟩

end MPSTensor.FNWDimensionConstant
