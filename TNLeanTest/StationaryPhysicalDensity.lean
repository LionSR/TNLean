/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.StationaryPhysicalDensity
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.Symmetry.StringOrderDefs
import QICLean.Analysis.SpectralRadius

/-!
# Stationary physical density regressions

The diagonal GHZ channel with the faithful boundary diag(3/4,1/4) satisfies
both canonical fixed-point equations. Its Pauli-X twisted transfer map has
spectral radius one, but its one-site physical density is not X-invariant.
The source purity hypothesis in the forward implication of Theorem 2
cannot be omitted merely because a faithful stationary boundary exists.

## References

* Pérez-García, Wolf, Sanz, Verstraete and Cirac, arXiv:0802.0447,
  Theorem 2, lines 297–323.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace

namespace MPSTensor.StationaryPhysicalDensityTest

/-- Scalar physical unitaries preserve every physical density; the fixed-twist
symmetry theorem must not impose nonscalarity. -/
example {d D : ℕ} (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ) (hμ : ‖μ‖ = 1) (N : ℕ) :
    blockKron N (μ • (1 : Matrix (Fin d) (Fin d) ℂ)) * stationaryBlockDensity A Λ N *
      (blockKron N (μ • (1 : Matrix (Fin d) (Fin d) ℂ)))ᴴ =
        stationaryBlockDensity A Λ N := by
  rw [← stationaryBlockDensity_rotatePhysical]
  apply stationaryBlockDensity_eq_of_unitary_gaugePhase A _ Λ 1 μ
    (by simp) hμ (by simp)
  intro i
  simp [rotatePhysical, Matrix.one_apply]

private noncomputable def unequalGHZBoundary : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![3 / 4, 1 / 4]

private theorem unequalGHZBoundary_posDef : unequalGHZBoundary.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num

private theorem unequalGHZBoundary_trace : Matrix.trace unequalGHZBoundary = 1 := by
  norm_num [unequalGHZBoundary, Matrix.trace, Fin.sum_univ_two]

private theorem ghz_unital : Kraus.transferMap ghzTensor 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Kraus.transferMap_apply, ghzTensor, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Pi.single_apply]

private theorem unequalGHZBoundary_stationary :
    Kraus.transferMap (fun i => (ghzTensor i)ᴴ) unequalGHZBoundary =
      unequalGHZBoundary := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Kraus.transferMap_apply, unequalGHZBoundary, ghzTensor,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply, Pi.single_apply]

private theorem pauliX_unitary : pauliX * pauliXᴴ = 1 := by
  have h : pauliXᴴ = pauliX := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pauliX, Matrix.conjTranspose_apply]
  rw [h, pauliX_sq]

private theorem ghz_twisted_entry (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    twistedTransferMap ghzTensor pauliX X i j = if i = j then 0 else X i j := by
  fin_cases i <;> fin_cases j <;>
    simp [twistedTransferMap_apply, ghzTensor, pauliX, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply, Pi.single_apply]

private theorem ghz_twisted_pauliX : twistedTransferMap ghzTensor pauliX pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

private theorem ghz_twisted_spectralRadius :
    spectralRadius ℂ (Module.End.toContinuousLinearMap (Matrix (Fin 2) (Fin 2) ℂ)
      (twistedTransferMap ghzTensor pauliX)) = 1 := by
  let Φ : Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ) :=
    Module.End.toContinuousLinearMap (Matrix (Fin 2) (Fin 2) ℂ)
  have hE : IsIdempotentElem (twistedTransferMap ghzTensor pauliX) := by
    ext X i j
    change twistedTransferMap ghzTensor pauliX
      (twistedTransferMap ghzTensor pauliX X) i j = _
    simp only [ghz_twisted_entry]
    split_ifs <;> rfl
  have hF : IsIdempotentElem (Φ (twistedTransferMap ghzTensor pauliX)) := by
    change Φ _ * Φ _ = Φ _
    rw [← map_mul, hE.eq]
  apply hF.spectralRadius_eq_one_of_ne_zero
  intro hzero
  have h := congrArg (fun F => F pauliX) hzero
  change twistedTransferMap ghzTensor pauliX pauliX = 0 at h
  rw [ghz_twisted_pauliX] at h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [pauliX] at h01

private theorem ghz_physical_one_not_invariant :
    blockKron 1 pauliX * stationaryBlockDensity ghzTensor unequalGHZBoundary 1 *
      (blockKron 1 pauliX)ᴴ ≠ stationaryBlockDensity ghzTensor unequalGHZBoundary 1 := by
  intro h
  have heq := (stationaryBlockDensity_rotatePhysical ghzTensor unequalGHZBoundary pauliX 1).trans h
  let z : Fin (blockPhysDim 2 1) := (decodeBlockEquiv 2 1).symm (fun _ => 0)
  have h00 := congrFun (congrFun heq z) z
  dsimp only [z] at h00
  rw [stationaryBlockDensity_word, stationaryBlockDensity_word] at h00
  norm_num [Kraus.evalWord, rotatePhysical, ghzTensor, pauliX, unequalGHZBoundary,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply, Pi.single_apply] at h00

/-- Faithfulness and stationarity alone do not imply physical symmetry from
twisted spectral radius one. The source pure-FCS assumption is essential. -/
example : unequalGHZBoundary.PosDef ∧ Matrix.trace unequalGHZBoundary = 1 ∧
    Kraus.transferMap ghzTensor 1 = 1 ∧
    Kraus.transferMap (fun i => (ghzTensor i)ᴴ) unequalGHZBoundary = unequalGHZBoundary ∧
    pauliX * pauliXᴴ = 1 ∧
    spectralRadius ℂ (Module.End.toContinuousLinearMap (Matrix (Fin 2) (Fin 2) ℂ)
      (twistedTransferMap ghzTensor pauliX)) = 1 ∧
    ¬ (∀ N, blockKron N pauliX * stationaryBlockDensity ghzTensor unequalGHZBoundary N *
      (blockKron N pauliX)ᴴ = stationaryBlockDensity ghzTensor unequalGHZBoundary N) := by
  exact ⟨unequalGHZBoundary_posDef, unequalGHZBoundary_trace, ghz_unital,
    unequalGHZBoundary_stationary, pauliX_unitary, ghz_twisted_spectralRadius,
    fun h => ghz_physical_one_not_invariant (h 1)⟩

end MPSTensor.StationaryPhysicalDensityTest
