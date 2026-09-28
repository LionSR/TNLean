/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWTransferConvention
import TNLean.MPS.ParentHamiltonian.FNWDimensionConstant.MarkovChannel

/-!
# Transfer eigenvalues of the nilpotent Markov example

A trace-preserving transfer map whose third power is the completely
depolarizing map has no eigenvalues other than zero and one.
-/

namespace MPSTensor.FNWDimensionConstant

private theorem eigenvalue_eq_zero_of_depolarizing_cube
    (E : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
    (htrace : ∀ X, Matrix.trace (E X) = Matrix.trace X)
    (hcube : ∀ X, E (E (E X)) = (Matrix.trace X / 4) • 1)
    {ν : ℂ} (hν : Module.End.HasEigenvalue E ν) (hν1 : ν ≠ 1) : ν = 0 := by
  obtain ⟨X, hX⟩ := hν.exists_hasEigenvector
  have htr : ν * Matrix.trace X = Matrix.trace X := by
    simpa only [hX.apply_eq_smul, Matrix.trace_smul, smul_eq_mul] using htrace X
  have htr0 : Matrix.trace X = 0 := by
    by_contra h
    exact hν1 ((mul_eq_right₀ h).mp htr)
  have hnil : ν ^ 3 • X = 0 := by
    simpa only [hX.apply_eq_smul, map_smul, smul_smul, htr0, zero_div, zero_smul,
      pow_succ, pow_zero, one_mul, mul_assoc] using hcube X
  exact (eq_or_ne ν 0).resolve_right fun h ↦
    (smul_ne_zero (pow_ne_zero 3 h) hX.2) hnil

/-- The only possible nonunit eigenvalue of the Markov example's FNW transfer
map is zero. Thus every positive rate below one is spectrally admissible in
Nachtergaele, Section 6, equation `boundAm`. -/
theorem markovTensor_fnwTransfer_eigenvalue_eq_zero {ν : ℂ}
    (hν : Module.End.HasEigenvalue (fnwTransferMap markovTensor) ν)
    (hν1 : ν ≠ 1) : ν = 0 := by
  apply eigenvalue_eq_zero_of_depolarizing_cube (Kraus.transferMap markovTensor)
    (Kraus.isTracePreservingMap_mapLM_of_isTP markovTensor markovTensor_isTP)
    markovTensor_transferMap_cube ?_ hν1
  simpa only [fnwTransferMap_eq_traceAdjointMap,
    Matrix.traceAdjointMap_hasEigenvalue_iff] using hν

end MPSTensor.FNWDimensionConstant
