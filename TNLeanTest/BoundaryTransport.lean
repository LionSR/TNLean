/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryClosedness

/-!
# Arbitrary-boundary transport tests

The signatures retain arbitrary boundaries, positive-length quantifier order,
and a separate empty-word completeness hypothesis. A decomposition with no
summands illustrates why ambient completeness cannot be omitted at length zero.
-/

open scoped Matrix BigOperators

namespace BoundaryTransportTest

variable {d D D₁ D₂ : ℕ}

example (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) (Y : Matrix (Fin D₂) (Fin D₂) ℂ) :
    MPOTensor.mpoWithBoundary (MPOTensor.mulTensor M N)
        (MPOTensor.productBoundary X Y) 0 =
      MPOTensor.mpoWithBoundary M X 0 * MPOTensor.mpoWithBoundary N Y 0 :=
  MPOTensor.mpoWithBoundary_mulTensor M N X Y 0

example (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) (Y : Matrix (Fin D₂) (Fin D₂) ℂ) (L : ℕ) :
    MPOTensor.mpoWithBoundary T X L *ᵥ MPSTensor.mpvWithBoundary A Y =
      MPSTensor.mpvWithBoundary (MPOTensor.actTensor T A)
        (MPOTensor.productBoundary X Y) :=
  MPOTensor.mpoWithBoundary_mulVec_mpvWithBoundary T A X Y L

example (T : MPOTensor d D) (h : MPOTensor.IsBoundaryClosed T)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Z : Matrix (Fin D) (Fin D) ℂ, ∀ L : ℕ, 0 < L →
      MPOTensor.mpoWithBoundary T X L * MPOTensor.mpoWithBoundary T Y L =
        MPOTensor.mpoWithBoundary T Z L :=
  h X Y

example (T : MPOTensor d D) (h : MPOTensor.IsBoundaryClosed T) :
    ∃ b : Matrix (Fin (D * D)) (Fin (D * D)) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      ∀ L : ℕ, 0 < L → ∀ C : Matrix (Fin (D * D)) (Fin (D * D)) ℂ,
        MPOTensor.mpoWithBoundary (MPOTensor.mulTensor T T) C L =
          MPOTensor.mpoWithBoundary T (b C) L :=
  (MPOTensor.isBoundaryClosed_iff_exists_linearMap T).mp h

-- A bond-one tensor with an idempotent local operator gives a closed family.
-- Only a local tensor equality is supplied, never a global closure hypothesis.
example (T : MPOTensor d 1) (hT : MPOTensor.mulTensor T T = T) :
    MPOTensor.IsBoundaryClosed T := by
  apply MPOTensor.isBoundaryClosed_of_biorthogonalDecomposition T
    (fun _ : Unit ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ : Unit ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ))
  refine ⟨fun _ ↦ by simp, fun c b h ↦ (h (Subsingleton.elim c b)).elim, ?_⟩
  intro i
  rw [hT]
  simp

private theorem identityDecomposition (A : MPSTensor d D) :
    MPSTensor.IsBiorthogonalDecomposition A (fun _ : Unit ↦ A)
      (fun _ : Unit ↦ (1 : Matrix (Fin D) (Fin D) ℂ))
      (fun _ : Unit ↦ (1 : Matrix (Fin D) (Fin D) ℂ)) where
  retract _ := by simp
  orthogonal c b h := (h (Subsingleton.elim c b)).elim
  letter _ := by simp

example (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    {L : ℕ} (hL : 0 < L) (σ : Fin L → Fin d) :
    MPSTensor.mpvWithBoundary A X σ =
      ∑ _ : Unit, MPSTensor.mpvWithBoundary A (1 * X * 1) σ :=
  (identityDecomposition A).mpvWithBoundary X hL σ

private theorem emptyDecomposition :
    MPSTensor.IsBiorthogonalDecomposition
      (fun _ : Fin 1 ↦ (0 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun _ : Fin 0 ↦ (fun _ : Fin 1 ↦ (0 : Matrix (Fin 1) (Fin 1) ℂ)))
      (fun _ : Fin 0 ↦ (0 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun _ : Fin 0 ↦ (0 : Matrix (Fin 1) (Fin 1) ℂ)) where
  retract c := Fin.elim0 c
  orthogonal c := Fin.elim0 c
  letter _ := by simp

example (w : List (Fin 1)) (hw : w ≠ []) :
    Kraus.evalWord (fun _ : Fin 1 ↦ (0 : Matrix (Fin 1) (Fin 1) ℂ)) w = 0 := by
  simpa using emptyDecomposition.evalWord w hw

example :
    Kraus.evalWord (fun _ : Fin 1 ↦ (0 : Matrix (Fin 1) (Fin 1) ℂ)) [] ≠
      ∑ _ : Fin 0, (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp

end BoundaryTransportTest
