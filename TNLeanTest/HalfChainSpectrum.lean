/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.HalfChainSourceSpectrum

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

-- The fixed-point clause in the canonical hypotheses is essential:
-- peripheral uniqueness by itself does not exclude the identity channel.
example (μ : ℂ) (hμ : Module.End.HasEigenvalue
    (LinearMap.id : Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ)) μ) : μ = 1 := by
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have heq : X = μ • X := hX.apply_eq_smul
  have hz : (1 - μ) • X = 0 := by rw [sub_smul, one_smul, ← heq, sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hX.2)).symm

example : ¬(∀ X : Matrix (Fin 2) (Fin 2) ℂ,
    (LinearMap.id : Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ)) X = X →
      ∃ c : ℂ, X = c • 1) := by
  intro hscalar
  obtain ⟨c, hc⟩ := hscalar (Matrix.diagonal ![1, 0]) rfl
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  norm_num at h0 h1
  exact one_ne_zero (h0.trans h1.symm)

example {d D : ℕ} (A : MPSTensor d D) (lam : Fin D → ℝ)
    (hlam : ∀ a, 0 < lam a) (htr : ∑ a, lam a = 1)
    (hU : ∑ i, A i * (A i)ᴴ = 1)
    (hfix : ∑ i, (A i)ᴴ * (Matrix.diagonal fun a => (lam a : ℂ)) * A i =
      Matrix.diagonal fun a => (lam a : ℂ))
    (hscalar : ∀ X, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1)
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 → μ = 1) :
    IsNormalTensor A :=
  isNormalTensor_of_pgvwc07_canonical_c2 A lam hlam htr hU hfix hscalar hRadius hC2

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

/-- info: 'MPSTensor.tendsto_halfChainEigenvalues_unital' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.tendsto_halfChainEigenvalues_unital

/-- info: 'MPSTensor.isNormalTensor_of_pgvwc07_canonical_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.isNormalTensor_of_pgvwc07_canonical_c2

/-- info: 'MPSTensor.tendsto_halfChainEigenvalues_of_pgvwc07_canonical_c2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.tendsto_halfChainEigenvalues_of_pgvwc07_canonical_c2

end AxiomChecks
