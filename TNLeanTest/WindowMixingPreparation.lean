/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.WindowMixingPreparation

/-!
# Actual two-site window regression

Alternating a trace-zero unitary channel and a rank-one reset gives distinct singular
minorizers for the two window orientations. Three sites leave a nonempty remainder; one
site has a zero periodic target and no two-site window. The maximal minorization endpoint
is included without supplying a global mixing rate or a reference family.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" (scope of the example).
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace WindowMixingRegression

private def ρ (j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = j then 1 else 0)

private theorem hρ (j : Fin 2) : (ρ j).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp
  split_ifs <;> positivity

private theorem htr (j : Fin 2) : (ρ j).trace = 1 := by simp [ρ, Matrix.trace]

private def unitTensor : MPSTensor 2 2 := ![!![0, 1; 1, 0], 0]

private def resetTensor : MPSTensor 2 2 := ![!![1, 0; 0, 0], !![0, 1; 0, 0]]

private theorem unit_tp : IsTracePreservingMap (Kraus.transferMap unitTensor) := by
  intro X
  simp [unitTensor, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.conjTranspose_apply, Matrix.trace]
  ring

private theorem reset_map (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Kraus.transferMap resetTensor X = X.trace • ρ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resetTensor, ρ, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.conjTranspose_apply, Matrix.trace]

private theorem reset_tp : IsTracePreservingMap (Kraus.transferMap resetTensor) := by
  intro X
  rw [reset_map, Matrix.trace_smul, htr]
  simp

private theorem unit_reset_output : Kraus.transferMap unitTensor (ρ 0) = ρ 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitTensor, ρ, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply]

private def chain (N : ℕ) : MPSChainTensor 2 2 N := fun j =>
  if j.val % 2 = 0 then unitTensor else resetTensor

private theorem chain_tp (N : ℕ) (j : Fin N) :
    IsTracePreservingMap (Kraus.transferMap (chain N j)) := by
  dsimp [chain]
  split_ifs
  · exact unit_tp
  · exact reset_tp

private theorem window_reset (N a : ℕ) (ha : a + 2 ≤ N) :
    Kraus.transferMap (MPSChainTensor.blockTensor ((chain N).interval a 2 ha)) =
      Matrix.tracePrepareMap (α := Fin 2) (ρ (if a % 2 = 0 then 1 else 0)) := by
  by_cases he : a % 2 = 0
  · have hn : (a + 1) % 2 = 1 := by omega
    have hm : Kraus.transferMap (MPSChainTensor.blockTensor ((chain N).interval a 2 ha)) =
        Kraus.transferMap unitTensor * Kraus.transferMap resetTensor := by
      simp [MPSChainTensor.transferMap_blockTensor, MPSChainTensor.interval,
        chain, List.ofFn_succ, he, hn]
    rw [hm]
    ext X : 1
    change Kraus.transferMap unitTensor (Kraus.transferMap resetTensor X) = _
    rw [reset_map, map_smul, unit_reset_output]
    simp [he]
  · have hn : (a + 1) % 2 = 0 := by omega
    have hm : Kraus.transferMap (MPSChainTensor.blockTensor ((chain N).interval a 2 ha)) =
        Kraus.transferMap resetTensor * Kraus.transferMap unitTensor := by
      simp [MPSChainTensor.transferMap_blockTensor, MPSChainTensor.interval,
        chain, List.ofFn_succ, he, hn]
    rw [hm]
    ext X : 1
    change Kraus.transferMap resetTensor (Kraus.transferMap unitTensor X) = _
    rw [reset_map, unit_tp]
    simp [he]

private theorem window_minorization (N a : ℕ) (ha : a + 2 ≤ N) :
    ∃ τ : Matrix (Fin 2) (Fin 2) ℂ, τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.blockTensor ((chain N).interval a 2 ha))) ≥
          ((1 : ℂ) / 2) • (τ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨ρ (if a % 2 = 0 then 1 else 0), hρ _, htr _, ?_⟩
  rw [window_reset, Matrix.choiMatrix_tracePrepareMap]
  norm_num

example : ρ 0 ≠ ρ 1 := by
  intro h
  have he := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 0) h
  norm_num [ρ] at he

example (j : Fin 2) : (ρ j).det = 0 := by
  fin_cases j <;> norm_num [ρ, Matrix.det_fin_two]

example :
    ‖(physicalMatrix (MPSChainTensor.blockTensor (chain 3)))ᴴ *
        physicalMatrix (MPSChainTensor.blockTensor (chain 3)) -
      (Kraus.transferMap (MPSChainTensor.blockTensor (chain 3)) (ρ 0))ᵀ ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 0 := by
  have h := norm_gram_blockTensor_sub_transport_le_of_window_domination (chain 3) 2
    (by decide) 1 (chain_tp 3) (window_minorization 3) (ρ 0) (hρ 0) (htr 0)
  simpa using h

example : chainState (chain 1) = 0 := by
  ext t
  rw [chainState_apply]
  change MPSChainTensor.coeff (chain 1) t = 0
  rw [MPSChainTensor.coeff, MPSChainTensor.eval_succ, MPSChainTensor.eval_zero, Matrix.mul_one]
  have ht : t 0 = 0 ∨ t 0 = 1 := by omega
  rcases ht with ht | ht <;>
    simp [chain, unitTensor, ht, Matrix.trace, Fin.sum_univ_two]

example (a : ℕ) : ¬a + 2 ≤ 1 := by omega

example : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
    ∃ (ψ : MPVSpace 2 N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
      IsPreparedInDepth T (fun x => ψ x) ∧
      1 - ‖⟪ψ, (‖chainState (chain N)‖ : ℂ)⁻¹ • chainState (chain N)⟫_ℂ‖ ≤ ε :=
  exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_window_domination
    2 2 (by decide) chain 2 (by decide) (η := 1) zero_lt_one chain_tp
    (by simpa only [Complex.ofReal_one, Nat.cast_ofNat] using window_minorization)

end WindowMixingRegression

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPSPreparation.exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_window_domination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_window_domination

end AxiomChecks
