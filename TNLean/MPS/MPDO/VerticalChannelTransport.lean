/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.VerticalBoundaryContraction

/-!
# Physical maps in vertical canonical coordinates

Appendix C.4 of arXiv:1606.00608 places the one-site tensor and its two-site
blocking in vertical canonical form, then absorbs the two changes of physical
coordinates into the refinement and coarse-graining maps `T` and `S`.  This
file defines those coordinate transports and proves their action on the
bond-matrix contractions of the two vertical canonical forms.

These transported physical maps precede the normalized sector maps
\(R_1,R_2,\widetilde R_1,\widetilde R_2\) in the definitions of
\(\widetilde T\) and \(\widetilde S\).  No fixed-point, sector relabelling, or
unitary block-identification conclusion is assumed here.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1974--1979.
-/

open scoped Matrix

noncomputable section

namespace MPOTensor

variable {d D R₁ R₂ : ℕ}

/-- Transport the refinement map `T` from the original one-site and two-site
physical coordinates to the corresponding retained vertical coordinates.

The two-site output is first relabelled from a pair of one-site indices to the
physical index of `blockTwo M`.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1979. -/
def transportTToVerticalCoordinates
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin R₁) (Fin R₁) ℂ →ₗ[ℂ] Matrix (Fin R₂) (Fin R₂) ℂ :=
  singleKrausMap U₂ ∘ₗ
    Matrix.equivReindexMap (blockedIndexEquiv d).symm ∘ₗ
      T ∘ₗ singleKrausMap U₁ᴴ

/-- Transport the coarse-graining map `S` from the original two-site and
one-site physical coordinates to the corresponding retained vertical
coordinates.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1979. -/
def transportSToVerticalCoordinates
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin R₂) (Fin R₂) ℂ →ₗ[ℂ] Matrix (Fin R₁) (Fin R₁) ℂ :=
  singleKrausMap U₁ ∘ₗ S ∘ₗ
    Matrix.equivReindexMap (blockedIndexEquiv d) ∘ₗ singleKrausMap U₂ᴴ

/-- Relabelling the two-site physical closure as one blocked physical index
gives the one-site closure of `blockTwo M`.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1979. -/
theorem reindex_physClose2_eq_physClose1_blockTwo
    (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.equivReindexMap (blockedIndexEquiv d).symm (physClose2 M X) =
      physClose1 (blockTwo M) X := by
  ext i j
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
    blockedIndexEquiv, blockTwo, Matrix.mul_assoc]

/-- After the vertical coordinate changes have been absorbed into `T`, the
refinement identity sends the contracted one-site vertical canonical form to
the contracted two-site vertical canonical form.

After composing with the normalized sector embedding and the sector partial
trace, this is the physical-coordinate identity used to obtain the displayed
formula for \(\widetilde T\).  Those sector maps have not yet been composed
with the transported physical map here.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1979. -/
theorem transportTToVerticalCoordinates_contractBondMatrix
    (M : MPOTensor d D)
    (B₁ : MPSTensor (D * D) R₁) (B₂ : MPSTensor (D * D) R₂)
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab = U₁ᴴ * B₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ = B₂ ab)
    (hT : ∀ X, T (physClose1 M X) = physClose2 M X)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    transportTToVerticalCoordinates U₁ U₂ T
        (MPSTensor.contractBondMatrix B₁ X) =
      MPSTensor.contractBondMatrix B₂ X := by
  simp only [transportTToVerticalCoordinates, LinearMap.comp_apply,
    singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  rw [← physClose1_eq_of_vertical_reconstruction M B₁ U₁ hReconstruct₁ X]
  rw [hT X]
  rw [reindex_physClose2_eq_physClose1_blockTwo]
  exact mul_physClose1_mul_conjTranspose_of_vertical_forward
    (blockTwo M) B₂ U₂ hForward₂ X

/-- After the vertical coordinate changes have been absorbed into `S`, the
coarse-graining identity sends the contracted two-site vertical canonical
form to the contracted one-site vertical canonical form.

After composing with the normalized sector embedding and the sector partial
trace, this is the physical-coordinate identity used to obtain the displayed
formula for \(\widetilde S\).  Those sector maps have not yet been composed
with the transported physical map here.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1979. -/
theorem transportSToVerticalCoordinates_contractBondMatrix
    (M : MPOTensor d D)
    (B₁ : MPSTensor (D * D) R₁) (B₂ : MPSTensor (D * D) R₂)
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ = B₁ ab)
    (hReconstruct₂ : ∀ ab,
      verticalTensor (blockTwo M) ab = U₂ᴴ * B₂ ab * U₂)
    (hS : ∀ X, S (physClose2 M X) = physClose1 M X)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    transportSToVerticalCoordinates U₁ U₂ S
        (MPSTensor.contractBondMatrix B₂ X) =
      MPSTensor.contractBondMatrix B₁ X := by
  simp only [transportSToVerticalCoordinates, LinearMap.comp_apply,
    singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  rw [← physClose1_eq_of_vertical_reconstruction
    (blockTwo M) B₂ U₂ hReconstruct₂ X]
  rw [show Matrix.equivReindexMap (blockedIndexEquiv d)
      (physClose1 (blockTwo M) X) = physClose2 M X by
    simpa [Matrix.equivReindexMap] using
      LinearMap.congr_fun (physClose1_blockTwo_eq_physClose2 M) X]
  rw [hS X]
  exact mul_physClose1_mul_conjTranspose_of_vertical_forward
    M B₁ U₁ hForward₁ X

end MPOTensor
