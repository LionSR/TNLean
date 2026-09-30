/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions

/-!
# Single-block canonical form II

A normal left-canonical tensor with a positive definite diagonal fixed matrix
is in canonical form II, with one block of weight one and no omitted bond
coordinates.

Source: arXiv:1606.00608, Appendix A, lines 1054–1077.
-/

open scoped Matrix BigOperators ComplexOrder Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- A normal left-canonical tensor with a diagonal positive fixed matrix is
already in one-block canonical form II in its given bond coordinates.

Source: arXiv:1606.00608, Appendix A, lines 1054–1077. -/
noncomputable def CPSVCanonicalFormIIData.ofNormalLeftCanonical {A : MPSTensor d D}
    [NeZero D] (hNormal : MPSTensor.IsNormalTensor A)
    (hLeft : MPSTensor.IsLeftCanonical A)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρfix : Kraus.transferMap A ρ = ρ) :
    MPSTensor.CPSVCanonicalFormIIData A := by
  classical
  refine {
    r := 1
    dim := fun _ => D
    dim_pos := fun _ => NeZero.pos D
    weights := fun _ => 1
    weights_ne_zero := fun _ => one_ne_zero
    blocks := fun _ => A
    blocks_normal := fun _ => hNormal
    total_dim_le := by simp
    ambient_coisometry := MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    coisometric := ?_
    reconstruct := ?_
    blocks_left_canonical := fun _ => hLeft
    blocks_fixed_point := fun _ => ⟨ρ, hρpd, hρdiag, hρfix⟩ }
  · let V : Matrix (Fin (∑ _ : Fin 1, D)) (Fin D) ℂ :=
      MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    have hV : (Vᴴ * V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
      MPSTensor.blockInclusion_conjTranspose_mul_self _ _
    have hcard : Fintype.card (Fin D) = Fintype.card (Fin (∑ _ : Fin 1, D)) := by simp
    exact (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ
      (A := (Vᴴ : Matrix (Fin D) (Fin (∑ _ : Fin 1, D)) ℂ))
      (B := V) hcard).mp hV
  · intro i
    let V : Matrix (Fin (∑ _ : Fin 1, D)) (Fin D) ℂ :=
      MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    have hV : (Vᴴ * V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
      MPSTensor.blockInclusion_conjTranspose_mul_self _ _
    have hmul := MPSTensor.toTensorFromBlocks_mul_blockInclusion
      (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) 0 i
    have hmul' : MPSTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => A) i * V = V * A i := by
      simpa only [one_smul] using hmul
    calc
      A i = (Vᴴ * V) * A i := by rw [hV, Matrix.one_mul]
      _ = Vᴴ * (MPSTensor.toTensorFromBlocks
            (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) i * V) := by
              rw [hmul', Matrix.mul_assoc]
      _ = (Vᴴ * MPSTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
            (fun _ : Fin 1 => A) i) * V := by
              exact (Matrix.mul_assoc Vᴴ _ V).symm

end MPSTensor
