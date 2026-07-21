/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTFusionIsometries

/-!
# Fusion coisometries onto the active product sectors

The product of two vertically read normal sectors may have a common zero
corner. The fusion map of arXiv:1606.00608, Theorem 4.14(iii), is therefore a
coisometry from the product bond space onto the direct sum of its nonzero
canonical sectors. The forward conjugation identity describes the retained
part, while the reverse identity states that the omitted corner is zero.

The structure below records these three properties separately:
\[
  UU^\dagger=1,\qquad
  U P^{ij}U^\dagger=D^{ij},\qquad
  P^{ij}=U^\dagger D^{ij}U.
\]
It permits an empty retained sum when the product tensor is zero.

## Main definitions

* `MPOTensor.BNTFusionCoisometryFamily`: positive weighted fusion of labelled
  tensors onto their active product sectors.

## Main results

* `BNTFusionCoisometryFamily.fusionCoisometry_mul_mulTensor`: the left zipper
  identity.
* `BNTFusionCoisometryFamily.mulTensor_mul_fusionCoisometry_conjTranspose`:
  the right zipper identity.
* `BNTFusionCoisometryFamily.toBNTFusionIsometryFamily_of_fullSupport`: passage
  to the stronger column-isometry structure under an explicit full-support
  identity.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(iii), lines 986--993, and Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor

/-- A positive weighted fusion decomposition onto the active product sectors.

For each pair of labels, the map is a coisometry from the product bond space
onto the retained direct sum. Both the forward conjugation and reverse
reconstruction identities are included, so a common zero corner may be
discarded but no nonzero part may be lost.

Source: arXiv:1606.00608, Theorem 4.14(iii), lines 986--993, and Appendix C.4,
lines 2020--2029 of `Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Local fix (Figure-11 fusion coisometry):** The source uses the retained-row
orientation of Proposition 4.13. Thus its fusion map satisfies
$UU^\dagger=1$, while $U^\dagger U$ is the active-support projection.
Documented in `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
structure BNTFusionCoisometryFamily (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (p : ℕ) where
  /-- Bond dimension of the tensor carrying each label. -/
  bondDim : Λ → ℕ
  /-- The labelled tensors, with common physical dimension `p`. -/
  tensor : ∀ γ : Λ, MPOTensor p (bondDim γ)
  /-- The positive diagonal multiplicity matrices. -/
  chi : DiagonalChiFamily Λ
  /-- Every retained diagonal entry is positive. Empty multiplicity spaces are
  permitted. -/
  posEntries : chi.PosEntries
  /-- The map from a product bond space onto its retained direct sum. -/
  fusionCoisometry : ∀ α β : Λ,
    Matrix ((γ : Λ) × (Fin (chi.dim α β γ) × Fin (bondDim γ)))
      (Fin (bondDim α * bondDim β)) ℂ
  /-- Each fusion map is a coisometry onto the retained direct sum. -/
  coisometry : ∀ α β : Λ,
    fusionCoisometry α β * (fusionCoisometry α β)ᴴ = 1
  /-- Conjugation onto the retained space gives the positive weighted direct
  sum, letter by letter. -/
  fusion : ∀ (α β : Λ) (i j : Fin p),
    fusionCoisometry α β * (mulTensor (tensor α) (tensor β)) i j *
        (fusionCoisometry α β)ᴴ =
      Matrix.blockDiagonal' fun γ => chi.matrix α β γ ⊗ₖ tensor γ i j
  /-- The retained direct sum reconstructs every product letter; equivalently,
  the omitted common corner is zero. -/
  reconstruction : ∀ (α β : Λ) (i j : Fin p),
    (mulTensor (tensor α) (tensor β)) i j =
      (fusionCoisometry α β)ᴴ *
        (Matrix.blockDiagonal' fun γ => chi.matrix α β γ ⊗ₖ tensor γ i j) *
        fusionCoisometry α β

namespace BNTFusionCoisometryFamily

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionCoisometryFamily Λ p)

/-- The fusion coisometry carries every product letter to its retained
weighted direct sum. -/
theorem fusionCoisometry_mul_mulTensor (α β : Λ) (i j : Fin p) :
    Fam.fusionCoisometry α β * mulTensor (Fam.tensor α) (Fam.tensor β) i j =
      (Matrix.blockDiagonal' fun γ =>
        Fam.chi.matrix α β γ ⊗ₖ Fam.tensor γ i j) *
        Fam.fusionCoisometry α β := by
  rw [Fam.reconstruction]
  simp only [← Matrix.mul_assoc, Fam.coisometry, Matrix.one_mul]

/-- Every product letter carries the adjoint fusion coisometry to its retained
weighted direct sum. -/
theorem mulTensor_mul_fusionCoisometry_conjTranspose
    (α β : Λ) (i j : Fin p) :
    mulTensor (Fam.tensor α) (Fam.tensor β) i j *
        (Fam.fusionCoisometry α β)ᴴ =
      (Fam.fusionCoisometry α β)ᴴ *
        Matrix.blockDiagonal' fun γ =>
          Fam.chi.matrix α β γ ⊗ₖ Fam.tensor γ i j := by
  rw [Fam.reconstruction]
  simp only [Matrix.mul_assoc, Fam.coisometry, Matrix.mul_one]

/-- Under the additional assertion that every active-support projection is the
identity, an active fusion coisometry gives the stronger full-support fusion
family. -/
noncomputable def toBNTFusionIsometryFamily_of_fullSupport
    (hfull : ∀ α β : Λ,
      (Fam.fusionCoisometry α β)ᴴ * Fam.fusionCoisometry α β = 1) :
    BNTFusionIsometryFamily Λ p where
  bondDim := Fam.bondDim
  tensor := Fam.tensor
  chi := Fam.chi
  posEntries := Fam.posEntries
  fusionIsometry := Fam.fusionCoisometry
  isometry := hfull
  fusion := Fam.fusion

end BNTFusionCoisometryFamily

end MPOTensor
