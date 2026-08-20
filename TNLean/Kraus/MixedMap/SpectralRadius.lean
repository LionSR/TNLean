/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.SpectralRadius
import TNLean.Kraus.MixedMap

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Spectral radius of mixed finite-family maps

For two trace-preserving finite matrix families, every eigenvalue of their rectangular mixed map
has norm at most one. The proof embeds the mixed map into the upper-right corner of the Kraus map
of the block-diagonal family $A_i \oplus B_i$ and applies the spectral bound for
trace-preserving Kraus maps.

## Main declarations

* `Kraus.mixedMapSpectralRadius` — spectral radius of a rectangular mixed map.
* `Kraus.eigenvalue_norm_le_one_mixedMapLM_of_isTP` — mixed-map eigenvalue bound.
* `Kraus.mixedMapSpectralRadius_le_one_of_isTP` — mixed-map spectral-radius bound.

## References

* M. M. Wolf, *Quantum Channels & Operations*, Proposition 6.1.
-/

open scoped Matrix TNOperatorSpace

namespace Kraus

variable {d D₁ D₂ : ℕ}

/-- The spectral radius of the mixed map of two finite matrix families. -/
noncomputable def mixedMapSpectralRadius
    (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) : ENNReal :=
  spectralRadius ℂ
    (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ) (mixedMapLM A B))

private noncomputable def sumFinReindexAlgEquiv :
    Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ ≃ₐ[ℂ]
      Matrix (Fin (D₁ + D₂)) (Fin (D₁ + D₂)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv

private theorem sumFinReindexAlgEquiv_conjTranspose
    (M : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ) :
    (sumFinReindexAlgEquiv M)ᴴ = sumFinReindexAlgEquiv Mᴴ := by
  simp [sumFinReindexAlgEquiv]

private noncomputable def fromBlocksTopLeftLM :
    Matrix (Fin D₁) (Fin D₁) ℂ →ₗ[ℂ]
      Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ where
  toFun X := Matrix.fromBlocks X 0 0 0
  map_add' X Y := by ext (i | i) (j | j) <;> simp
  map_smul' c X := by ext (i | i) (j | j) <;> simp

private noncomputable def fromBlocksBottomRightLM :
    Matrix (Fin D₂) (Fin D₂) ℂ →ₗ[ℂ]
      Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ where
  toFun X := Matrix.fromBlocks 0 0 0 X
  map_add' X Y := by ext (i | i) (j | j) <;> simp
  map_smul' c X := by ext (i | i) (j | j) <;> simp

private noncomputable def fromBlocksUpperRightLM :
    Matrix (Fin D₁) (Fin D₂) ℂ →ₗ[ℂ]
      Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ where
  toFun X := Matrix.fromBlocks 0 X 0 0
  map_add' X Y := by ext (i | i) (j | j) <;> simp
  map_smul' c X := by ext (i | i) (j | j) <;> simp

private noncomputable def blockDiagonalFamily
    (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) :
    Fin d → Matrix (Fin (D₁ + D₂)) (Fin (D₁ + D₂)) ℂ :=
  fun i ↦ sumFinReindexAlgEquiv (Matrix.fromBlocks (A i) 0 0 (B i))

private theorem blockDiagonalFamily_isTP
    (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ)
    (hA : IsTP A) (hB : IsTP B) :
    IsTP (blockDiagonalFamily A B) := by
  classical
  rw [IsTP]
  have hTerm (i : Fin d) :
      (blockDiagonalFamily A B i)ᴴ * blockDiagonalFamily A B i =
        sumFinReindexAlgEquiv
          (Matrix.fromBlocks ((A i)ᴴ * A i) 0 0 ((B i)ᴴ * B i)) := by
    rw [blockDiagonalFamily, sumFinReindexAlgEquiv_conjTranspose,
      ← map_mul]
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp_rw [hTerm]
  rw [← map_sum, ← map_one (sumFinReindexAlgEquiv (D₁ := D₁) (D₂ := D₂))]
  have hBlocks :
      (∑ i, Matrix.fromBlocks ((A i)ᴴ * A i) 0 0 ((B i)ᴴ * B i)) = 1 := by
    calc
      _ = ∑ i, (fromBlocksTopLeftLM ((A i)ᴴ * A i) +
          fromBlocksBottomRightLM ((B i)ᴴ * B i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ext (r | r) (c | c) <;>
          simp [fromBlocksTopLeftLM, fromBlocksBottomRightLM]
      _ = (∑ i, fromBlocksTopLeftLM ((A i)ᴴ * A i)) +
          ∑ i, fromBlocksBottomRightLM ((B i)ᴴ * B i) := Finset.sum_add_distrib
      _ = fromBlocksTopLeftLM (∑ i, (A i)ᴴ * A i) +
          fromBlocksBottomRightLM (∑ i, (B i)ᴴ * B i) := by rw [map_sum, map_sum]
      _ = 1 := by
        rw [show (∑ i, (A i)ᴴ * A i) = 1 from hA,
          show (∑ i, (B i)ᴴ * B i) = 1 from hB]
        ext (r | r) (c | c) <;>
          simp [fromBlocksTopLeftLM, fromBlocksBottomRightLM, Matrix.one_apply]
  exact congrArg (sumFinReindexAlgEquiv (D₁ := D₁) (D₂ := D₂)) hBlocks

private noncomputable def upperRightBlock
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) :
    Matrix (Fin (D₁ + D₂)) (Fin (D₁ + D₂)) ℂ :=
  sumFinReindexAlgEquiv (fromBlocksUpperRightLM X)

private theorem upperRightBlock_ne_zero
    {X : Matrix (Fin D₁) (Fin D₂) ℂ} (hX : X ≠ 0) :
    upperRightBlock X ≠ 0 := by
  intro h
  apply hX
  have hBlock : Matrix.fromBlocks (0 : Matrix (Fin D₁) (Fin D₁) ℂ) X
      (0 : Matrix (Fin D₂) (Fin D₁) ℂ) (0 : Matrix (Fin D₂) (Fin D₂) ℂ) = 0 := by
    apply (sumFinReindexAlgEquiv (D₁ := D₁) (D₂ := D₂)).injective
    simpa [upperRightBlock, fromBlocksUpperRightLM] using h
  have hBlock₁₂ := congrArg Matrix.toBlocks₁₂ hBlock
  rw [Matrix.toBlocks_fromBlocks₁₂] at hBlock₁₂
  exact hBlock₁₂.trans rfl

private theorem mapLM_blockDiagonalFamily_upperRightBlock
    (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) :
    mapLM (blockDiagonalFamily A B) (upperRightBlock X) =
      upperRightBlock (mixedMapLM A B X) := by
  classical
  rw [mapLM_apply, map_apply]
  have hTerm (i : Fin d) :
      blockDiagonalFamily A B i * upperRightBlock X *
          (blockDiagonalFamily A B i)ᴴ =
        sumFinReindexAlgEquiv
          (Matrix.fromBlocks 0 (A i * X * (B i)ᴴ) 0 0) := by
    rw [blockDiagonalFamily, upperRightBlock, fromBlocksUpperRightLM,
      sumFinReindexAlgEquiv_conjTranspose, ← map_mul, ← map_mul]
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp_rw [hTerm]
  rw [upperRightBlock, ← map_sum]
  refine congrArg (sumFinReindexAlgEquiv (D₁ := D₁) (D₂ := D₂)) ?_
  change ∑ i, fromBlocksUpperRightLM (A i * X * (B i)ᴴ) =
    fromBlocksUpperRightLM (mixedMapLM A B X)
  rw [mixedMapLM_apply, map_sum]

/-- Every eigenvalue of the mixed map of two trace-preserving finite matrix families has norm at
most one. -/
theorem eigenvalue_norm_le_one_mixedMapLM_of_isTP
    (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ)
    (hA : IsTP A) (hB : IsTP B)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedMapLM A B) μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hLift : Module.End.HasEigenvector
      (mapLM (blockDiagonalFamily A B)) μ (upperRightBlock X) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, upperRightBlock_ne_zero hX.2⟩
    rw [mapLM_blockDiagonalFamily_upperRightBlock, hX.apply_eq_smul]
    change sumFinReindexAlgEquiv (fromBlocksUpperRightLM (μ • X)) =
      μ • sumFinReindexAlgEquiv (fromBlocksUpperRightLM X)
    rw [(fromBlocksUpperRightLM (D₁ := D₁) (D₂ := D₂)).map_smul]
    exact (sumFinReindexAlgEquiv (D₁ := D₁) (D₂ := D₂)).toLinearMap.map_smul μ
      (fromBlocksUpperRightLM X)
  exact eigenvalue_norm_le_one_of_isTP (blockDiagonalFamily A B)
    (blockDiagonalFamily_isTP A B hA hB) μ
    (Module.End.hasEigenvalue_of_hasEigenvector hLift)

/-- The mixed map of two trace-preserving finite matrix families has spectral radius at most one. -/
theorem mixedMapSpectralRadius_le_one_of_isTP
    (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ)
    (hA : IsTP A) (hB : IsTP B) :
    mixedMapSpectralRadius A B ≤ 1 := by
  exact spectralRadius_le_one_of_forall_eigenvalue_norm_le_one (mixedMapLM A B)
    (eigenvalue_norm_le_one_mixedMapLM_of_isTP A B hA hB)

end Kraus
