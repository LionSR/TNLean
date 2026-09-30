/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.UnitaryPhaseClassGrouping
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Unitary matching with repeated periodic blocks

Grouping phase-equivalent blocks retains each original copy. Consequently,
the finite-order phases in the equal-case fundamental theorem can be pulled
back to a family in which repeated blocks have not been grouped.

Source: arXiv:1708.00029, Theorems 3.8 and 4.1, lines 643--690 and 752--765.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Equal periodic block families admit a unitary conjugation after multiplying
each source weight by a root of unity whose order divides its block period.
Repeated blocks are allowed. Source: arXiv:1708.00029, Theorems 3.8 and 4.1,
lines 643--690 and 752--765. -/
theorem exists_unitary_matching_of_periodic_block_families_sameMPV₂Pos
    {d r s : ℕ} {dim : Fin r → ℕ} {dim' : Fin s → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (B : (k : Fin s) → MPSTensor d (dim' k)) (ν : Fin s → ℂ) (hν : ∀ k, ν k ≠ 0)
    (periodA : Fin r → ℕ) (periodB : Fin s → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hSame : SameMPV₂Pos (toTensorFromBlocks μ A) (toTensorFromBlocks ν B)) :
    ∃ (c : Fin r → ℂ) (W : Matrix (Fin (∑ j, dim j)) (Fin (∑ k, dim' k)) ℂ),
      (∀ j, c j ^ periodA j = 1) ∧ W * Wᴴ = 1 ∧ Wᴴ * W = 1 ∧
      ∀ i, toTensorFromBlocks (fun j => c j * μ j) A i =
        W * toTensorFromBlocks ν B i * Wᴴ := by
  classical
  obtain ⟨P, eP, perP, hPerP, hNonRepP, _, hPeriodP, _, hGroupP⟩ :=
    exists_unitary_phaseClass_grouping A μ hμ periodA hPerA
  obtain ⟨Q, _, perQ, hPerQ, hNonRepQ, _, _, _, hGroupQ⟩ :=
    exists_unitary_phaseClass_grouping B ν hν periodB hPerB
  obtain ⟨G, _, hG, hP⟩ := hGroupP (fun _ => 1)
  obtain ⟨H, hHH, hH, hQ⟩ := hGroupQ (fun _ => 1)
  have hSameP : SameMPV₂Pos P.toTensor (toTensorFromBlocks μ A) := by
    apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Gᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hG)
    intro i
    simpa only [SectorDecomposition.toTensor, one_mul,
      Matrix.conjTranspose_conjTranspose] using hP i
  have hSameQ : SameMPV₂Pos Q.toTensor (toTensorFromBlocks ν B) := by
    apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Hᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hH)
    intro i
    simpa only [SectorDecomposition.toTensor, one_mul,
      Matrix.conjTranspose_conjTranspose] using hQ i
  obtain ⟨z, U, hz, hUU, hU, _, _, hMatch, _⟩ :=
    fundamentalTheorem_periodic_equalCase_unitary_global P Q perP perQ
      hPerP hPerQ hNonRepP hNonRepQ (hSameP.trans (hSame.trans hSameQ.symm))
      0 (fun _ => dvd_zero _)
  obtain ⟨V, hVV, hV, hPhase⟩ := hGroupP (P.flatCopyScalar z)
  let c := fun j => P.flatCopyScalar z (eP.symm j)
  let W := Vᴴ * U * H
  have hWU : Matrix.IsUnitaryBetween W :=
    Matrix.IsUnitaryBetween.mul (Vᴴ * U) H
      (Matrix.IsUnitaryBetween.mul Vᴴ U
        (Matrix.IsUnitaryBetween.conjTranspose V ⟨hV, hVV⟩) ⟨hU, hUU⟩) ⟨hH, hHH⟩
  refine ⟨c, W, ?_, hWU.2, hWU.1, ?_⟩
  · intro j
    have hp := hPeriodP (eP.symm j)
    rw [Equiv.apply_symm_apply] at hp
    change P.flatCopyScalar z (eP.symm j) ^ periodA j = 1
    rw [← hp]
    exact hz _ _
  · intro i
    have h := hMatch i
    rw [SectorDecomposition.toTensor, blockScalarMatrix_mul_toTensorFromBlocks,
      hPhase i] at h
    have hQi : Q.toTensor i = H * toTensorFromBlocks ν B i * Hᴴ := by
      simpa only [SectorDecomposition.toTensor, one_mul] using hQ i
    rw [hQi] at h
    have hc := congrArg (fun M => Vᴴ * M * V) h
    simpa only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc V Vᴴ, hVV, Matrix.one_mul,
      ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, Matrix.mul_one] using hc

end MPSTensor
