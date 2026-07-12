/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTLeftTripleFusion
import TNLean.MPS.MPDO.BNTRightTripleFusion

/-!
# Final-sector restrictions of triple fusion

The two bracketings of a triple product give decompositions indexed by an intermediate label and
a final label.  Fixing the final label `ε` gives the two families of fusion maps which are compared
by the $F$-move of arXiv:1511.08090, equation (Fmove).  This file defines those restrictions and
proves their conjugation identities.  In each case the remaining bond-space factor carries the
same single-label tensor `tensor ε`.

The existence of the change of basis between the two multiplicity spaces is not asserted here.
That step also uses injectivity of `tensor ε`, as explained after equation (pentagon3) in
arXiv:1511.08090.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, lines 995--999
* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, equation (Fmove) and lines 237--280 of
  `References/1511.08090/AnyonsPEPS.tex`
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

/-- The multiplicity space for the left bracketing with final label `ε`.

Source: arXiv:1511.08090, equation (Fmove), left-hand indices `e, μ, ν`. -/
abbrev LeftFinalMultiplicity (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε)

/-- The multiplicity space for the right bracketing with final label `ε`.

Source: arXiv:1511.08090, equation (Fmove), right-hand indices `f, λ, σ`. -/
abbrev RightFinalMultiplicity (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim β γ δ) × Fin (Fam.chi.dim α δ ε)

/-- The left-associated fixed-final-sector index, including the bond index of `tensor ε`. -/
abbrev LeftFinalIndex (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε) ×
    Fin (Fam.bondDim ε)

/-- The right-associated fixed-final-sector index, including the bond index of `tensor ε`. -/
abbrev RightFinalIndex (α β γ ε : Λ) : Type u :=
  (δ : Λ) × Fin (Fam.chi.dim β γ δ) × Fin (Fam.chi.dim α δ ε) ×
    Fin (Fam.bondDim ε)

/-- The row inclusion selecting the block with final label `ε` in the left-associated
decomposition.

Source: arXiv:1511.08090, equations preceding (Fmove), lines 237--251. -/
def leftFinalRow (α β γ ε : Λ) :
    Fam.LeftFinalIndex α β γ ε →
      (δ : Λ) × (ε' : Λ) × Fin (Fam.chi.dim α β δ) ×
        Fin (Fam.chi.dim δ γ ε') × Fin (Fam.bondDim ε')
  | ⟨δ, μ, ν, b⟩ => ⟨δ, ε, μ, ν, b⟩

/-- The row inclusion selecting the block with final label `ε` in the right-associated
decomposition.

Source: arXiv:1511.08090, equations preceding (Fmove), lines 237--251. -/
def rightFinalRow (α β γ ε : Λ) :
    Fam.RightFinalIndex α β γ ε →
      (δ : Λ) × (ε' : Λ) × Fin (Fam.chi.dim β γ δ) ×
        Fin (Fam.chi.dim α δ ε') × Fin (Fam.bondDim ε')
  | ⟨δ, μ, ν, b⟩ => ⟨δ, ε, μ, ν, b⟩

/-- The left-associated triple-fusion map restricted to a fixed final label `ε`.

Source: arXiv:1511.08090, left-hand side of equation (Fmove). -/
noncomputable def leftFinalFusionIsometry (α β γ ε : Λ) :
    Matrix (Fam.LeftFinalIndex α β γ ε)
      (Fin (Fam.bondDim α * Fam.bondDim β * Fam.bondDim γ)) ℂ :=
  (Fam.leftFusionIsometry α β γ).submatrix (Fam.leftFinalRow α β γ ε) id

/-- The right-associated triple-fusion map restricted to a fixed final label `ε`.

Source: arXiv:1511.08090, right-hand side of equation (Fmove). -/
noncomputable def rightFinalFusionIsometry (α β γ ε : Λ) :
    Matrix (Fam.RightFinalIndex α β γ ε)
      (Fin (Fam.bondDim α * (Fam.bondDim β * Fam.bondDim γ))) ℂ :=
  (Fam.rightFusionIsometry α β γ).submatrix (Fam.rightFinalRow α β γ ε) id

/-- Restricting the left-associated triple-fusion identity to the final block `ε` leaves a
block diagonal matrix over the intermediate label `δ`, with the same tensor `tensor ε` in every
block.

Source: arXiv:1511.08090, first equation preceding (Fmove), lines 237--251. -/
theorem leftFinalFusion_apply (α β γ ε : Λ) (i k : Fin p) :
    Fam.leftFinalFusionIsometry α β γ ε *
        (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k *
        (Fam.leftFinalFusionIsometry α β γ ε)ᴴ =
      Matrix.blockDiagonal' fun δ =>
        Fam.chi.matrix α β δ ⊗ₖ (Fam.chi.matrix δ γ ε ⊗ₖ Fam.tensor ε i k) := by
  unfold leftFinalFusionIsometry
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

Source: arXiv:1511.08090, second equation preceding (Fmove), lines 237--251. -/
theorem rightFinalFusion_apply (α β γ ε : Λ) (i k : Fin p) :
    Fam.rightFinalFusionIsometry α β γ ε *
        (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k *
        (Fam.rightFinalFusionIsometry α β γ ε)ᴴ =
      Matrix.blockDiagonal' fun δ =>
        Fam.chi.matrix β γ δ ⊗ₖ (Fam.chi.matrix α δ ε ⊗ₖ Fam.tensor ε i k) := by
  unfold rightFinalFusionIsometry
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

end MPOTensor.BNTFusionIsometryFamily
