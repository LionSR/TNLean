/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceCuts
import Mathlib.Topology.Instances.Matrix

/-!
# Virtual sandwiching of an MPO tensor

This module studies the pointwise transformation
$$
  U^{ij} \longmapsto A U^{ij} B
$$
of an MPO tensor. Both raw source cuts are multiplied on the left by
$A \otimes I_d$ and on the right by $I_d \otimes B$. Consequently, invertible
$A$ and $B$ preserve both source-cut ranks.

This is the rank-preservation step in
[Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188],
Proposition IV.5, lines 786--804.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- Sandwich every virtual matrix of an MPO tensor between two fixed matrices:
$\widehat U^{ij}=A U^{ij}B$.

Source: arXiv:1703.09188, Proposition IV.5, lines 786--804. -/
def virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin D) ℂ) : MPOTensor d D :=
  fun i j ↦ A * U i j * B

@[simp] theorem virtualSandwich_apply (A : Matrix (Fin D) (Fin D) ℂ)
    (U : MPOTensor d D) (B : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d) :
    virtualSandwich A U B i j = A * U i j * B :=
  rfl

/-- Continuous families of virtual matrices and MPO tensors give a continuous
family after virtual sandwiching.

Source: arXiv:1703.09188, Proposition IV.5, lines 786--804. -/
theorem continuous_virtualSandwich {X : Type*} [TopologicalSpace X]
    {A : X → Matrix (Fin D) (Fin D) ℂ} {U : X → MPOTensor d D}
    {B : X → Matrix (Fin D) (Fin D) ℂ} (hA : Continuous A)
    (hU : Continuous U) (hB : Continuous B) :
    Continuous fun x ↦ virtualSandwich (A x) (U x) (B x) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  have hUij : Continuous fun x ↦ U x i j :=
    (continuous_apply j).comp ((continuous_apply i).comp hU)
  simpa [virtualSandwich] using (hA.matrix_mul hUij).matrix_mul hB

/-- The first raw source cut of a virtual sandwich is
$(A\otimes I_d)M_1(U)(I_d\otimes B)$, with no transpose or conjugation.

Source: arXiv:1703.09188, Proposition IV.5, lines 786--804. -/
theorem sourceCutM₁_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ)
    (U : MPOTensor d D) (B : Matrix (Fin D) (Fin D) ℂ) :
    sourceCutM₁ (virtualSandwich A U B) =
      (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * sourceCutM₁ U *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B) := by
  ext ⟨α, j⟩ ⟨i, β⟩
  simp [virtualSandwich, sourceCutM₁, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

/-- The second raw source cut of a virtual sandwich is
$(A\otimes I_d)M_2(U)(I_d\otimes B)$, with no transpose or conjugation.

Source: arXiv:1703.09188, Proposition IV.5, lines 786--804. -/
theorem sourceCutM₂_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ)
    (U : MPOTensor d D) (B : Matrix (Fin D) (Fin D) ℂ) :
    sourceCutM₂ (virtualSandwich A U B) =
      (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * sourceCutM₂ U *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B) := by
  ext ⟨α, i⟩ ⟨j, β⟩
  simp [virtualSandwich, sourceCutM₂, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

private lemma isUnit_det_kronecker_one (A : Matrix (Fin D) (Fin D) ℂ)
    (hA : IsUnit A) :
    IsUnit (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).det := by
  rw [Matrix.det_kronecker]
  simpa using ((Matrix.isUnit_iff_isUnit_det A).mp hA).pow d

private lemma isUnit_det_one_kronecker (B : Matrix (Fin D) (Fin D) ℂ)
    (hB : IsUnit B) :
    IsUnit ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B).det := by
  rw [Matrix.det_kronecker]
  simpa using ((Matrix.isUnit_iff_isUnit_det B).mp hB).pow d

/-- Invertible virtual matrices preserve the right source rank.

Source: arXiv:1703.09188, Proposition IV.5, lines 786--804. -/
theorem rightRank_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ)
    (U : MPOTensor d D) (B : Matrix (Fin D) (Fin D) ℂ)
    (hA : IsUnit A) (hB : IsUnit B) :
    r[virtualSandwich A U B] = r[U] := by
  rw [rightRank, sourceCutM₁_virtualSandwich]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_one_kronecker B hB)]
  exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_kronecker_one A hA)

/-- Invertible virtual matrices preserve the left source rank.

Source: arXiv:1703.09188, Proposition IV.5, lines 786--804. -/
theorem leftRank_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ)
    (U : MPOTensor d D) (B : Matrix (Fin D) (Fin D) ℂ)
    (hA : IsUnit A) (hB : IsUnit B) :
    ℓ[virtualSandwich A U B] = ℓ[U] := by
  rw [leftRank, sourceCutM₂_virtualSandwich]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_one_kronecker B hB)]
  exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_kronecker_one A hA)

end MPOTensor
