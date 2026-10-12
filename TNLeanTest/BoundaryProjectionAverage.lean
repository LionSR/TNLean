/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BoundaryProjectionAverage

/-!
# Boundary projection averaging regression tests

The averaged projection is the actual canonical ground-space projection.
Only the product normalization of the actual boundary families is supplied;
commutation and unit support are derived. The tests retain a target shorter
than the calibration length, empty finite families, and zero dimensions.
The literal parent average is kept distinct from ambient completion.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace BoundaryProjectionAverageTest

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

variable {d D₁ D₂ L n : ℕ} {ι : Type*} [Fintype ι]

section General

variable (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (h : MPOTensor.IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) (U : Matrix (Fin D₁) (Fin D₁) ℂ)
    (hU : MPOTensor.mpoWithBoundary T U L = 1) (hn : 0 < n)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (MPOTensor.mpoWithBoundary T X n)ᴴ = MPOTensor.mpoWithBoundary T Y n)
    (X Y : ι → Matrix (Fin D₁) (Fin D₁) ℂ)
    (hXY : ∑ i, MPOTensor.mpoWithBoundary T (X i) n *
      MPOTensor.mpoWithBoundary T (Y i) n = MPOTensor.mpoWithBoundary T U n)

-- No chosen projector, fixed-support premise, or averaged-projector premise is supplied.
example :
    (∑ i, Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (X i) n) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (Y i) n)) =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap :=
  h.sum_mpoWithBoundary_groundSpaceES_starProjection hInj hL hU hn hstar X Y hXY

-- Averaging the parent retains the actual boundary unit, rather than an ambient identity.
example :
    (∑ i, Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (X i) n) *
        MPSTensor.parentInteractionES A n *
        Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (Y i) n)) =
      Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T U n) -
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap :=
  h.sum_mpoWithBoundary_parentInteractionES hInj hL hU hn hstar X Y hXY

-- Ambient completion is exactly the existing canonical interaction.
example :
    1 - (∑ i, Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (X i) n) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (Y i) n)) =
      MPSTensor.parentInteractionES A n :=
  h.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection hInj hL hU hn hstar X Y hXY

-- The dimension criterion belongs to the ambient complement.
example (hDim : d ^ n > D₂ ^ 2) :
    1 - (∑ i, Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (X i) n) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (Y i) n)) ≠ 0 :=
  h.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection_ne_zero
    hInj hL hU hn hstar X Y hXY hDim

-- When Qₙ = Pₙ, the literal average vanishes. This is not ruled out by normalization.
example (hQ : Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T U n) =
    (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) :
    (∑ i, Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (X i) n) *
      MPSTensor.parentInteractionES A n *
      Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (Y i) n)) = 0 := by
  rw [h.sum_mpoWithBoundary_parentInteractionES hInj hL hU hn hstar X Y hXY,
    hQ, sub_self]

end General

-- The target need not be at least the positive calibration/injectivity length.
example (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (h : MPOTensor.IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A 3)
    (U : Matrix (Fin D₁) (Fin D₁) ℂ) (hU : MPOTensor.mpoWithBoundary T U 3 = 1)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (MPOTensor.mpoWithBoundary T X 1)ᴴ = MPOTensor.mpoWithBoundary T Y 1)
    (X Y : ι → Matrix (Fin D₁) (Fin D₁) ℂ)
    (hXY : ∑ i, MPOTensor.mpoWithBoundary T (X i) 1 *
      MPOTensor.mpoWithBoundary T (Y i) 1 = MPOTensor.mpoWithBoundary T U 1) :
    (∑ i, Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (X i) 1) *
        (MPSTensor.groundSpaceES A 1).starProjection.toLinearMap *
        Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (Y i) 1)) =
      (MPSTensor.groundSpaceES A 1).starProjection.toLinearMap :=
  h.sum_mpoWithBoundary_groundSpaceES_starProjection
    hInj (by omega) hU Nat.one_pos hstar X Y hXY

-- A zero state-bond dimension requires no additional nontriviality instance.
example (T : MPOTensor d D₁) (A : MPSTensor d 0)
    (h : MPOTensor.IsBoundaryCompatible T A)
    (U : Matrix (Fin D₁) (Fin D₁) ℂ) (hU : MPOTensor.mpoWithBoundary T U 1 = 1)
    (hn : 0 < n)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (MPOTensor.mpoWithBoundary T X n)ᴴ = MPOTensor.mpoWithBoundary T Y n)
    (X Y : ι → Matrix (Fin D₁) (Fin D₁) ℂ)
    (hXY : ∑ i, MPOTensor.mpoWithBoundary T (X i) n *
      MPOTensor.mpoWithBoundary T (Y i) n = MPOTensor.mpoWithBoundary T U n) :
    (∑ i, Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (X i) n) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary T (Y i) n)) =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  have hInj : Kraus.IsInjective A := Subsingleton.elim _ _
  exact h.sum_mpoWithBoundary_groundSpaceES_starProjection
    (Kraus.isNBlkInjective_one_of_isInjective hInj) Nat.one_pos hU hn hstar X Y hXY

-- Empty averaging families and zero physical/virtual dimensions are simultaneously valid.
example (T : MPOTensor 0 0) (A : MPSTensor 0 0) (hn : 0 < n) :
    (MPSTensor.groundSpaceES A n).starProjection.toLinearMap = 0 := by
  have h : MPOTensor.IsBoundaryCompatible T A := by
    intro U X
    refine ⟨X, fun k hk ↦ ?_⟩
    funext σ
    exact Fin.elim0 (σ ⟨0, hk⟩)
  have hInj : Kraus.IsInjective A := Subsingleton.elim _ _
  have hU : MPOTensor.mpoWithBoundary T 0 1 = 1 := by
    ext σ τ
    exact Fin.elim0 (σ 0)
  have hstar : ∀ X : Matrix (Fin 0) (Fin 0) ℂ,
      ∃ Y : Matrix (Fin 0) (Fin 0) ℂ,
        (MPOTensor.mpoWithBoundary T X n)ᴴ = MPOTensor.mpoWithBoundary T Y n := by
    intro X
    refine ⟨0, ?_⟩
    ext σ τ
    exact Fin.elim0 (σ ⟨0, hn⟩)
  have hXY : (∑ _i : Fin 0, MPOTensor.mpoWithBoundary T 0 n *
      MPOTensor.mpoWithBoundary T 0 n) = MPOTensor.mpoWithBoundary T 0 n := by
    ext σ τ
    exact Fin.elim0 (σ ⟨0, hn⟩)
  simpa using (h.sum_mpoWithBoundary_groundSpaceES_starProjection
    (Kraus.isNBlkInjective_one_of_isInjective hInj) Nat.one_pos hU hn hstar
    (fun _ : Fin 0 ↦ 0) (fun _ : Fin 0 ↦ 0) hXY).symm

end BoundaryProjectionAverageTest

/-- info: 'MPOTensor.IsBoundaryCompatible.groundSpaceES_starProjection_commute_mpoWithBoundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.groundSpaceES_starProjection_commute_mpoWithBoundary

/-- info: 'MPOTensor.IsBoundaryCompatible.sum_mpoWithBoundary_groundSpaceES_starProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.sum_mpoWithBoundary_groundSpaceES_starProjection

/-- info: 'MPOTensor.IsBoundaryCompatible.sum_mpoWithBoundary_parentInteractionES' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.sum_mpoWithBoundary_parentInteractionES

/-- info: 'MPOTensor.IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection

/-- info: 'MPOTensor.IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection_ne_zero
