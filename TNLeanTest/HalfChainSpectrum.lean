/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.HalfChainSpectrum

/-!
# Finite-size half-chain spectrum regression tests

The scalar tensor of weight two has squared ring norm sixteen at half-length
one, so its normalized density tests the actual finite-size normalization.
At length zero, the physical half has dimension one even when the boundary
space has dimension four. The reset channel has a singular trace-one fixed
point and tests the noninvertible case of the geometric-gap theorem.
-/

open MPSTensor Filter
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator Topology

private def scalarTwo : MPSTensor 1 1 := fun _ => !![2]

example : halfChainNormSq scalarTwo 1 = 16 := by
  norm_num [halfChainNormSq_eq_sum, scalarTwo, mpv_eq, coeff_eq,
    Kraus.evalWord, Matrix.trace, Matrix.mul_apply, Complex.normSq_apply,
    Fintype.sum_unique, List.ofFn_succ]

example : (normalizedHalfChainReducedMatrix scalarTwo 1).trace = 1 := by
  apply trace_normalizedHalfChainReducedMatrix
  norm_num [halfChainNormSq_eq_sum, scalarTwo, mpv_eq, coeff_eq,
    Kraus.evalWord, Matrix.trace, Matrix.mul_apply, Complex.normSq_apply,
    Fintype.sum_unique, List.ofFn_succ]

example (A : MPSTensor 2 2) : halfChainEigenvalues A 0 1 = 0 := by
  apply Matrix.IsHermitian.paddedEigenvalues_eq_zero
  simp [Cfg]

example (A : MPSTensor 2 2) (L : ℕ) : halfChainEigenvalues A L 4 = 0 :=
  halfChainEigenvalues_eq_zero A L 4 (by norm_num)

example (A : MPSTensor 2 2) :
    halfChainEigenvalues A 0 =
      (posSemidef_normalizedHalfChainSpectralMatrix A 0).isHermitian.paddedEigenvalues :=
  halfChainEigenvalues_eq_boundary A 0

private def resetTensor : MPSTensor 2 2 := fun i => Matrix.single 0 i 1

private def resetWeights : Fin 2 → ℝ := ![1, 0]

private theorem reset_transfer (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Kraus.transferMap resetTensor X = Matrix.trace X • Matrix.diagonal (fun a =>
      (resetWeights a : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kraus.transferMap, Kraus.mapLM_apply, resetTensor, resetWeights,
      Matrix.trace, Fin.sum_univ_two]

example : (Matrix.diagonal fun a => (resetWeights a : ℂ)).det = 0 := by
  norm_num [resetWeights, Matrix.det_fin_two]

private theorem reset_weights_nonneg (a : Fin 2) : 0 ≤ resetWeights a := by
  fin_cases a <;> norm_num [resetWeights]

example (k : ℕ) :
    Tendsto (fun L => halfChainEigenvalues resetTensor L k) atTop
      (𝓝 ((posSemidef_halfChainSpectrumLimit resetWeights
        reset_weights_nonneg).isHermitian.paddedEigenvalues k)) := by
  refine tendsto_halfChainEigenvalues resetTensor resetWeights reset_weights_nonneg
    (by norm_num [resetWeights, Fin.sum_univ_two]) ?_ ?_ ?_ k
  · intro X
    rw [reset_transfer, Matrix.trace_smul]
    norm_num [resetWeights, Matrix.trace_diagonal, Fin.sum_univ_two]
  · rw [reset_transfer]
    norm_num [resetWeights, Matrix.trace_diagonal, Fin.sum_univ_two]
  · have heq : Kraus.transferMap resetTensor =
        fixedPointProj (Matrix.diagonal fun a => (resetWeights a : ℂ))
          (by norm_num [resetWeights, Matrix.trace_diagonal, Fin.sum_univ_two]) := by
      ext X i j
      simp only [reset_transfer, fixedPointProj, LinearMap.coe_mk, AddHom.coe_mk]
      norm_num [resetWeights, Matrix.trace_diagonal, Fin.sum_univ_two]
    simp [heq]

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPSTensor.charpoly_normalizedHalfChainSpectralMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.charpoly_normalizedHalfChainSpectralMatrix

/-- info: 'MPSTensor.halfChainEigenvalues_eq_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.halfChainEigenvalues_eq_boundary

/-- info: 'MPSTensor.tendsto_halfChainEigenvalues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.tendsto_halfChainEigenvalues

/-- info: 'Matrix.IsHermitian.abs_eigenvalues₀_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.IsHermitian.abs_eigenvalues₀_sub_le

end AxiomChecks
