/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTLeftTripleFusion
import TNLean.MPS.MPDO.BNTRightTripleFusion
import TNLean.Algebra.ScalarCommutant

/-!
# Final-sector restrictions of triple fusion

The two bracketings of a triple product give decompositions indexed by an intermediate label and
a final label.  This file restricts both fusion maps to a fixed final label `ε` and proves their
conjugation identities.  In each case the remaining bond-space factor carries the same
single-label tensor `tensor ε`.

The adjoints of these restrictions have the bracketing and orientation of the maps compared by
the $F$-move of arXiv:1511.08090, after reindexing the triple bond space by the canonical
associator.  No identification of the positive diagonal chi indices with the fusion
multiplicities of that source is asserted here.  Such a comparison first requires the
length-independent integer specialization and injectivity of `tensor ε`.

The final result below isolates the part of the comparison that follows from injectivity.  If a
matrix between the two fixed-final-sector spaces already intertwines the amplified letters of
`tensor ε`, then it acts trivially on the bond factor, up to a matrix between the two
multiplicity spaces.  The result does not construct this intertwiner, prove that it is
invertible, or identify the chi dimensions with fusion multiplicities.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, lines 995--999
* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, equation (Fmove) and lines 237--280 of the source
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

/-- The multiplicity space for the left bracketing with final label `ε`.

This is the positive-diagonal weighted analogue of the `e, μ, ν` index space in equation
(Fmove) of arXiv:1511.08090; no equality with the fusion multiplicities of that source is
asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999. -/
abbrev LeftFinalMultiplicity (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε)

/-- The multiplicity space for the right bracketing with final label `ε`.

This is the positive-diagonal weighted analogue of the `f, λ, σ` index space in equation
(Fmove) of arXiv:1511.08090; no equality with the fusion multiplicities of that source is
asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999. -/
abbrev RightFinalMultiplicity (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim β γ δ) × Fin (Fam.chi.dim α δ ε)

/-- The left-associated fixed-final-sector index, including the bond index of `tensor ε`.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999. -/
abbrev LeftFinalIndex (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε) ×
    Fin (Fam.bondDim ε)

/-- The right-associated fixed-final-sector index, including the bond index of `tensor ε`.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999. -/
abbrev RightFinalIndex (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim β γ δ) × Fin (Fam.chi.dim α δ ε) ×
    Fin (Fam.bondDim ε)

/-- The canonical identification of the left fixed-final-sector index with the product of its
multiplicity space and the bond space of `tensor ε`.

Source: arXiv:1606.00608, Theorem IV.13(iii), label `Ualphabeta`, and the associativity remark
immediately following it; arXiv:1511.08090, equation (Fmove), left multiplicity indices
`(e, μ, ν)`. -/
def leftFinalIndexEquiv (α β γ ε : Λ) :
    Fam.LeftFinalIndex α β γ ε ≃
      Fam.LeftFinalMultiplicity α β γ ε × Fin (Fam.bondDim ε) :=
  (Equiv.sigmaCongrRight fun δ =>
    (Equiv.prodAssoc (Fin (Fam.chi.dim α β δ)) (Fin (Fam.chi.dim δ γ ε))
      (Fin (Fam.bondDim ε))).symm).trans
    (Equiv.sigmaProdDistrib
      (fun δ => Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε))
      (Fin (Fam.bondDim ε))).symm

/-- The canonical identification of the right fixed-final-sector index with the product of its
multiplicity space and the bond space of `tensor ε`.

Source: arXiv:1606.00608, Theorem IV.13(iii), label `Ualphabeta`, and the associativity remark
immediately following it; arXiv:1511.08090, equation (Fmove), right multiplicity indices
`(f, λ, σ)`. -/
def rightFinalIndexEquiv (α β γ ε : Λ) :
    Fam.RightFinalIndex α β γ ε ≃
      Fam.RightFinalMultiplicity α β γ ε × Fin (Fam.bondDim ε) :=
  (Equiv.sigmaCongrRight fun δ =>
    (Equiv.prodAssoc (Fin (Fam.chi.dim β γ δ)) (Fin (Fam.chi.dim α δ ε))
      (Fin (Fam.bondDim ε))).symm).trans
    (Equiv.sigmaProdDistrib
      (fun δ => Fin (Fam.chi.dim β γ δ) × Fin (Fam.chi.dim α δ ε))
      (Fin (Fam.bondDim ε))).symm

/-- The row inclusion selecting the block with final label `ε` in the left-associated
decomposition.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999. -/
def leftFinalRow (α β γ ε : Λ) :
    Fam.LeftFinalIndex α β γ ε →
      (δ : Λ) × (ε' : Λ) × Fin (Fam.chi.dim α β δ) ×
        Fin (Fam.chi.dim δ γ ε') × Fin (Fam.bondDim ε')
  | ⟨δ, μ, ν, b⟩ => ⟨δ, ε, μ, ν, b⟩

/-- The row inclusion selecting the block with final label `ε` in the right-associated
decomposition.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999. -/
def rightFinalRow (α β γ ε : Λ) :
    Fam.RightFinalIndex α β γ ε →
      (δ : Λ) × (ε' : Λ) × Fin (Fam.chi.dim β γ δ) ×
        Fin (Fam.chi.dim α δ ε') × Fin (Fam.bondDim ε')
  | ⟨δ, μ, ν, b⟩ => ⟨δ, ε, μ, ν, b⟩

/-- The left-associated triple-fusion map restricted to a fixed final label `ε`.

Its adjoint has the orientation and bracketing pattern of the weighted analogue of the left-hand
composite in equation (Fmove) of arXiv:1511.08090.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999, with the bracketing and index
pattern of arXiv:1511.08090, lines 237--251. -/
noncomputable def leftFinalFusionMap (α β γ ε : Λ) :
    Matrix (Fam.LeftFinalIndex α β γ ε)
      (Fin (Fam.bondDim α * Fam.bondDim β * Fam.bondDim γ)) ℂ :=
  (Fam.leftFusionIsometry α β γ).submatrix (Fam.leftFinalRow α β γ ε) id

/-- The right-associated triple-fusion map restricted to a fixed final label `ε`.

Its adjoint has the orientation and bracketing pattern of the weighted analogue of the right-hand
composite in equation (Fmove) of arXiv:1511.08090, after the canonical reassociation of the
triple bond space.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999, with the bracketing and index
pattern of arXiv:1511.08090, lines 237--251. -/
noncomputable def rightFinalFusionMap (α β γ ε : Λ) :
    Matrix (Fam.RightFinalIndex α β γ ε)
      (Fin (Fam.bondDim α * (Fam.bondDim β * Fam.bondDim γ))) ℂ :=
  (Fam.rightFusionIsometry α β γ).submatrix (Fam.rightFinalRow α β γ ε) id

/-- Restricting the left-associated triple-fusion identity to the final block `ε` leaves a
block diagonal matrix over the intermediate label `δ`, with the same tensor `tensor ε` in every
block.

This is the positive-diagonal weighted form obtained from the fusion identity; arXiv:1511.08090
uses identity multiplicity weights in the corresponding fixed-channel equation.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999, with the fixed-final-label
decomposition pattern of arXiv:1511.08090, lines 237--251. -/
theorem leftFinalFusion_apply (α β γ ε : Λ) (i k : Fin p) :
    Fam.leftFinalFusionMap α β γ ε *
        (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k *
        (Fam.leftFinalFusionMap α β γ ε)ᴴ =
      Matrix.blockDiagonal' fun δ =>
        Fam.chi.matrix α β δ ⊗ₖ (Fam.chi.matrix δ γ ε ⊗ₖ Fam.tensor ε i k) := by
  unfold leftFinalFusionMap
  let U := Fam.leftFusionIsometry α β γ
  let r := Fam.leftFinalRow α β γ ε
  let X := (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k
  change U.submatrix r id * X * (U.submatrix r id)ᴴ = _
  have step1 : U.submatrix r id * X = (U * X).submatrix r id :=
    (Matrix.submatrix_mul U X r id id Function.bijective_id).symm
  rw [step1]
  have step2 : (U * X).submatrix r id * (U.submatrix r id)ᴴ =
      (U * X * Uᴴ).submatrix r r := by
    rw [Matrix.conjTranspose_submatrix]
    exact (Matrix.submatrix_mul (U * X) Uᴴ r id r Function.bijective_id).symm
  rw [step2]
  dsimp only [U, X]
  rw [Fam.leftFusion_apply]
  ext ⟨δ, μ, ν, b⟩ ⟨δ', μ', ν', b'⟩
  simp only [Matrix.submatrix_apply, r, leftFinalRow]
  by_cases hδ : δ = δ'
  · subst δ'
    simp
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hδ]

/-- Restricting the right-associated triple-fusion identity to the final block `ε` leaves a
block diagonal matrix over the intermediate label `δ`, with the same tensor `tensor ε` in every
block.

This is the positive-diagonal weighted form obtained from the fusion identity; arXiv:1511.08090
uses identity multiplicity weights in the corresponding fixed-channel equation.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999, with the fixed-final-label
decomposition pattern of arXiv:1511.08090, lines 237--251. -/
theorem rightFinalFusion_apply (α β γ ε : Λ) (i k : Fin p) :
    Fam.rightFinalFusionMap α β γ ε *
        (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k *
        (Fam.rightFinalFusionMap α β γ ε)ᴴ =
      Matrix.blockDiagonal' fun δ =>
        Fam.chi.matrix β γ δ ⊗ₖ (Fam.chi.matrix α δ ε ⊗ₖ Fam.tensor ε i k) := by
  unfold rightFinalFusionMap
  let U := Fam.rightFusionIsometry α β γ
  let r := Fam.rightFinalRow α β γ ε
  let X := (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k
  change U.submatrix r id * X * (U.submatrix r id)ᴴ = _
  have step1 : U.submatrix r id * X = (U * X).submatrix r id :=
    (Matrix.submatrix_mul U X r id id Function.bijective_id).symm
  rw [step1]
  have step2 : (U * X).submatrix r id * (U.submatrix r id)ᴴ =
      (U * X * Uᴴ).submatrix r r := by
    rw [Matrix.conjTranspose_submatrix]
    exact (Matrix.submatrix_mul (U * X) Uᴴ r id r Function.bijective_id).symm
  rw [step2]
  dsimp only [U, X]
  rw [Fam.rightFusion_apply]
  ext ⟨δ, μ, ν, b⟩ ⟨δ', μ', ν', b'⟩
  simp only [Matrix.submatrix_apply, r, rightFinalRow]
  by_cases hδ : δ = δ'
  · subst δ'
    simp
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hδ]

/-- An intertwiner between the two fixed-final-sector spaces of an injective final tensor is a
matrix on the multiplicity spaces tensored with the identity on the final bond space.

The matrix `C` is only assumed here.  After the two canonical reindexings, the hypothesis says
that `C` intertwines the two identity amplifications of every letter of `tensor ε`.  Injectivity
then forces every rectangular bond-space block of `C` to be scalar.  Thus the bond-space action
is the identity and all remaining information lies in the rectangular matrix `F` between the
left and right multiplicity spaces.

This is the injective-sector uniqueness step in the derivation of an $F$-move.  It does not
construct `C`, prove that either `C` or `F` is invertible, or identify the dimensions of the
positive diagonal chi matrices with the fusion multiplicities of arXiv:1511.08090.

Source: arXiv:1606.00608, Theorem IV.13(iii), label `Ualphabeta`, and the associativity remark
immediately following it; arXiv:1511.08090, Section "Fusion tensors", uniqueness paragraph
preceding equation (zippercondition2), and Section "Associativity and the pentagon equation",
the injectivity argument following equation (pentagon3). -/
theorem exists_reindexed_intertwiner_eq_kronecker_one_of_isInjective
    (α β γ ε : Λ)
    (hε : MPSTensor.IsInjective (Fam.tensor ε).toMPSTensor)
    (C : Matrix (Fam.LeftFinalIndex α β γ ε)
      (Fam.RightFinalIndex α β γ ε) ℂ)
    (hC : ∀ ij : Fin (p * p),
      ((1 : Matrix (Fam.LeftFinalMultiplicity α β γ ε)
          (Fam.LeftFinalMultiplicity α β γ ε) ℂ) ⊗ₖ
          (Fam.tensor ε).toMPSTensor ij) *
          C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm =
        C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm *
          ((1 : Matrix (Fam.RightFinalMultiplicity α β γ ε)
            (Fam.RightFinalMultiplicity α β γ ε) ℂ) ⊗ₖ
            (Fam.tensor ε).toMPSTensor ij)) :
    ∃ F : Matrix (Fam.LeftFinalMultiplicity α β γ ε)
        (Fam.RightFinalMultiplicity α β γ ε) ℂ,
      C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
          (Fam.rightFinalIndexEquiv α β γ ε).symm =
        F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ) := by
  exact Matrix.exists_eq_kronecker_one_of_intertwines_span_eq_top
    (Fam.tensor ε).toMPSTensor
    (C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
      (Fam.rightFinalIndexEquiv α β γ ε).symm)
    hε.span_eq_top hC

end MPOTensor.BNTFusionIsometryFamily
