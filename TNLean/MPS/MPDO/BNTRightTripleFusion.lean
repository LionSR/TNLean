/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.MPDO.BNTFusionIsometries

/-!
# Right iterated fusion of a triple product tensor

The associativity discussion following Theorem IV.13 of arXiv:1606.00608 says that the two
ways of applying the fusion isometries to a triple product are related by a pentagon-like
equation. The source attributes this relation to arXiv:1511.08090. In the notation of the
associativity section of that paper, the right-bracketed fusion tensor is
`(1 ⊗ X_{βγ}^{δ}) X_{αδ}^{ε}`. Taking adjoints gives the decomposition route that first
fuses `β, γ` and then fuses `α` with the intermediate label `δ`.

This file records the corresponding construction for `BNTFusionIsometryFamily`: first fuse the
last two factors of `M_α (M_β M_γ)` with `fusionIsometry β γ`, then fuse `M_α` with each
intermediate tensor using `fusionIsometry α δ`. The resulting isometry conjugates the triple
product tensor onto the doubly weighted direct sum with blocks
`χ_{β,γ,δ} ⊗ (χ_{α,δ,ε} ⊗ M_ε)`. No comparison with the left parenthesization, and
hence no F-move or pentagon equation, is asserted here.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Theorem IV.13(iii),
  lines 986--999 of `Papers/1606.00608/MPDO-22-12-17-2.tex`
* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, Section "Associativity and the pentagon equation", source lines 237--251
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor

/-- A sum of Kronecker products with a fixed multiplicity factor can be regrouped as that
factor tensored with a letter of the product tensor. The equivalence records the exchange of
the multiplicity and first bond factors.

Source: bookkeeping for the right parenthesization in arXiv:1511.08090, source lines 237--251,
and arXiv:1606.00608, lines 986--999. -/
private theorem kronecker_sum_mulTensor_right {p a bd1 bd2 : ℕ}
    (X : Matrix (Fin a) (Fin a) ℂ) (Y : MPOTensor p bd1) (Z : MPOTensor p bd2)
    (i k : Fin p) (E : Fin a × Fin (bd1 * bd2) ≃ Fin bd1 × (Fin a × Fin bd2))
    (hE : E = ((Equiv.prodCongr (Equiv.refl (Fin a)) finProdFinEquiv.symm).trans
        (Equiv.prodAssoc (Fin a) (Fin bd1) (Fin bd2)).symm).trans
      ((Equiv.prodCongr (Equiv.prodComm (Fin a) (Fin bd1)) (Equiv.refl (Fin bd2))).trans
        (Equiv.prodAssoc (Fin bd1) (Fin a) (Fin bd2)))) :
    (∑ j : Fin p, Y i j ⊗ₖ (X ⊗ₖ Z j k)) =
      (X ⊗ₖ mulTensor Y Z i k).submatrix E.symm E.symm := by
  subst hE
  rw [mulTensor_apply]
  ext ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩
  simp only [Matrix.submatrix_apply, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.symm_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_symm,
    Equiv.coe_refl, id_eq, Equiv.prodAssoc_apply, Matrix.sum_apply,
    Matrix.kronecker_apply, Equiv.symm_apply_apply]
  simp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    Fintype.sum_mul_mul_eq_mul_sum_mul (X x2 y2)
      (fun j => Y i j x1 y1) (fun j => Z j k x3 y3)

namespace BNTFusionIsometryFamily

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

/-- The row-space reindexing that distributes the bond space of `M_α` over the direct sum
produced by fusing `M_β` with `M_γ`.

Source: bookkeeping for arXiv:1511.08090, source lines 237--251. -/
private def lastPairBondEquiv (α β γ : Λ) :
    Fin (Fam.bondDim α) ×
        ((δ : Λ) × Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim δ)) ≃
      (δ : Λ) × Fin (Fam.bondDim α) ×
        (Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim δ)) :=
  (Equiv.prodComm _ _).trans
    ((Equiv.sigmaProdDistrib
      (fun δ => Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim δ))
      (Fin (Fam.bondDim α))).trans
    (Equiv.sigmaCongrRight fun δ =>
      Equiv.prodComm (Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim δ))
        (Fin (Fam.bondDim α))))

/-- The column-space reindexing that places the multiplicity of the first fusion outside the
bond space on which the second fusion isometry acts.

Source: bookkeeping for arXiv:1511.08090, source lines 237--251. -/
private def rightTripleMultEquiv (α β γ δ : Λ) :
    Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim α * Fam.bondDim δ) ≃
      Fin (Fam.bondDim α) ×
        (Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim δ)) :=
  ((Equiv.prodCongr (Equiv.refl (Fin (Fam.chi.dim β γ δ))) finProdFinEquiv.symm).trans
    (Equiv.prodAssoc (Fin (Fam.chi.dim β γ δ)) (Fin (Fam.bondDim α))
      (Fin (Fam.bondDim δ))).symm).trans
    ((Equiv.prodCongr
      (Equiv.prodComm (Fin (Fam.chi.dim β γ δ)) (Fin (Fam.bondDim α)))
      (Equiv.refl (Fin (Fam.bondDim δ)))).trans
    (Equiv.prodAssoc (Fin (Fam.bondDim α)) (Fin (Fam.chi.dim β γ δ))
      (Fin (Fam.bondDim δ))))

/-- The equivalence flattening the nested direct sums of the right iterated fusion into a pair
of labels and their two multiplicity indices.

Source: bookkeeping for arXiv:1511.08090, source lines 237--251. -/
private def rightTripleFlattenEquiv (α β γ : Λ) :
    (δ : Λ) × Fin (Fam.chi.dim β γ δ) ×
        (ε : Λ) × Fin (Fam.chi.dim α δ ε) × Fin (Fam.bondDim ε) ≃
      (δ : Λ) × (ε : Λ) × Fin (Fam.chi.dim β γ δ) ×
        Fin (Fam.chi.dim α δ ε) × Fin (Fam.bondDim ε) :=
  Equiv.sigmaCongrRight fun δ =>
    (Equiv.prodComm (Fin (Fam.chi.dim β γ δ))
        ((ε : Λ) × Fin (Fam.chi.dim α δ ε) × Fin (Fam.bondDim ε))).trans
      ((Equiv.sigmaProdDistrib
        (fun ε => Fin (Fam.chi.dim α δ ε) × Fin (Fam.bondDim ε))
        (Fin (Fam.chi.dim β γ δ))).trans
      (Equiv.sigmaCongrRight fun ε =>
        Equiv.prodComm (Fin (Fam.chi.dim α δ ε) × Fin (Fam.bondDim ε))
          (Fin (Fam.chi.dim β γ δ))))

/-- The first stage of the right iterated fusion: the identity on the bond space of `M_α`
tensored with `fusionIsometry β γ`.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999, and arXiv:1511.08090,
source lines 237--251. -/
private noncomputable def fuseLastTwoStep (α β γ : Λ) :
    Matrix ((δ : Λ) × Fin (Fam.bondDim α) ×
        (Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim δ)))
      (Fin (Fam.bondDim α * (Fam.bondDim β * Fam.bondDim γ))) ℂ :=
  ((1 : Matrix (Fin (Fam.bondDim α)) (Fin (Fam.bondDim α)) ℂ) ⊗ₖ
      Fam.fusionIsometry β γ).submatrix
    (Fam.lastPairBondEquiv α β γ).symm finProdFinEquiv.symm

private theorem fuseLastTwoStep_isometry (α β γ : Λ) :
    (Fam.fuseLastTwoStep α β γ)ᴴ * Fam.fuseLastTwoStep α β γ = 1 := by
  unfold fuseLastTwoStep
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.lastPairBondEquiv α β γ).symm _,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Fam.isometry,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

private theorem fuseLastTwoStep_apply (α β γ : Λ) (i k : Fin p) :
    Fam.fuseLastTwoStep α β γ *
        (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k *
        (Fam.fuseLastTwoStep α β γ)ᴴ =
      (∑ j : Fin p, Fam.tensor α i j ⊗ₖ
        (Matrix.blockDiagonal' fun δ =>
          Fam.chi.matrix β γ δ ⊗ₖ Fam.tensor δ j k)).submatrix
        (Fam.lastPairBondEquiv α β γ).symm (Fam.lastPairBondEquiv α β γ).symm := by
  unfold fuseLastTwoStep
  rw [mulTensor_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, Fam.fusion]

/-- The second-stage map in the intermediate sector `δ`: the first multiplicity factor is
unchanged while `fusionIsometry α δ` acts on the remaining bond factors.

Source: arXiv:1511.08090, source lines 237--251. -/
private noncomputable def rightBlockPiece (α β γ δ : Λ) :
    Matrix (Fin (Fam.chi.dim β γ δ) ×
        ((ε : Λ) × Fin (Fam.chi.dim α δ ε) × Fin (Fam.bondDim ε)))
      (Fin (Fam.bondDim α) ×
        (Fin (Fam.chi.dim β γ δ) × Fin (Fam.bondDim δ))) ℂ :=
  ((1 : Matrix (Fin (Fam.chi.dim β γ δ)) (Fin (Fam.chi.dim β γ δ)) ℂ) ⊗ₖ
      Fam.fusionIsometry α δ).submatrix (Equiv.refl _)
    (Fam.rightTripleMultEquiv α β γ δ).symm

private theorem rightBlockPiece_isometry (α β γ δ : Λ) :
    (Fam.rightBlockPiece α β γ δ)ᴴ * Fam.rightBlockPiece α β γ δ = 1 := by
  unfold rightBlockPiece
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Fam.isometry,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

private theorem rightBlockPiece_apply (α β γ δ : Λ) (i k : Fin p) :
    Fam.rightBlockPiece α β γ δ *
        (∑ j : Fin p, Fam.tensor α i j ⊗ₖ
          (Fam.chi.matrix β γ δ ⊗ₖ Fam.tensor δ j k)) *
        (Fam.rightBlockPiece α β γ δ)ᴴ =
      Fam.chi.matrix β γ δ ⊗ₖ
        Matrix.blockDiagonal' fun ε => Fam.chi.matrix α δ ε ⊗ₖ Fam.tensor ε i k := by
  rw [kronecker_sum_mulTensor_right _ _ _ _ _
    (Fam.rightTripleMultEquiv α β γ δ) rfl]
  unfold rightBlockPiece
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.rightTripleMultEquiv α β γ δ).symm _,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.rightTripleMultEquiv α β γ δ).symm _,
    Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.conjTranspose_one, Matrix.mul_one, Fam.fusion]

private theorem lastPair_sum_blockDiagonal (α β γ : Λ) (i k : Fin p) :
    (∑ j : Fin p, Fam.tensor α i j ⊗ₖ
        (Matrix.blockDiagonal' fun δ =>
          Fam.chi.matrix β γ δ ⊗ₖ Fam.tensor δ j k)).submatrix
        (Fam.lastPairBondEquiv α β γ).symm (Fam.lastPairBondEquiv α β γ).symm =
      Matrix.blockDiagonal' fun δ =>
        ∑ j : Fin p, Fam.tensor α i j ⊗ₖ
          (Fam.chi.matrix β γ δ ⊗ₖ Fam.tensor δ j k) := by
  ext ⟨δ, a, m, b⟩ ⟨δ', a', m', b'⟩
  simp only [Matrix.submatrix_apply, lastPairBondEquiv, Equiv.symm_trans_apply,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Equiv.sigmaProdDistrib_symm_apply, Matrix.sum_apply,
    Matrix.blockDiagonal'_apply]
  by_cases hδ : δ = δ'
  · subst hδ; simp
  · simp only [Prod.swap_prod_mk, Matrix.kronecker_apply]
    rw [dif_neg hδ]
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hδ, mul_zero,
      Finset.sum_const_zero]

private theorem rightTripleFlatten_blockDiagonal' (α β γ : Λ)
    (X : ∀ δ, Matrix (Fin (Fam.chi.dim β γ δ)) (Fin (Fam.chi.dim β γ δ)) ℂ)
    (Y : ∀ δ ε, Matrix (Fin (Fam.chi.dim α δ ε)) (Fin (Fam.chi.dim α δ ε)) ℂ)
    (T : ∀ ε, Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ) :
    (Matrix.blockDiagonal' fun δ =>
        X δ ⊗ₖ Matrix.blockDiagonal' fun ε => Y δ ε ⊗ₖ T ε).submatrix
        (Fam.rightTripleFlattenEquiv α β γ).symm (Fam.rightTripleFlattenEquiv α β γ).symm =
      Matrix.blockDiagonal' fun δ =>
        Matrix.blockDiagonal' fun ε => X δ ⊗ₖ (Y δ ε ⊗ₖ T ε) := by
  ext ⟨δ, ε, m1, m2, b⟩ ⟨δ', ε', m1', m2', b'⟩
  simp only [Matrix.submatrix_apply, rightTripleFlattenEquiv, Equiv.symm_trans_apply,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Equiv.sigmaProdDistrib_symm_apply]
  by_cases hδ : δ = δ'
  · subst hδ
    by_cases hε : ε = ε'
    · subst hε; simp
    · simp [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_ne _ _ _ hε]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hδ]

private theorem blockDiagonal'_rightBlockPiece_isometry (α β γ : Λ) :
    (Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ))ᴴ *
        Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ) = 1 := by
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp_rw [Fam.rightBlockPiece_isometry]
  exact Matrix.blockDiagonal'_one

/-- **The right iterated fusion isometry** first applies `fusionIsometry β γ`, with the
bond space of `M_α` unchanged, and then applies `fusionIsometry α δ` in every intermediate
sector `δ`.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`, and arXiv:1511.08090, source lines 237--251.
This is the right-parenthesized isometry
appearing before any F-move comparison. -/
noncomputable def rightFusionIsometry (α β γ : Λ) :
    Matrix ((δ : Λ) × (ε : Λ) × Fin (Fam.chi.dim β γ δ) ×
        Fin (Fam.chi.dim α δ ε) × Fin (Fam.bondDim ε))
      (Fin (Fam.bondDim α * (Fam.bondDim β * Fam.bondDim γ))) ℂ :=
  (Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ) * Fam.fuseLastTwoStep α β γ).submatrix
    (Fam.rightTripleFlattenEquiv α β γ).symm id

/-- **The right iterated fusion map is an isometry**.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999, and arXiv:1511.08090,
source lines 237--251. -/
theorem rightFusionIsometry_isometry (α β γ : Λ) :
    (Fam.rightFusionIsometry α β γ)ᴴ * Fam.rightFusionIsometry α β γ = 1 := by
  unfold rightFusionIsometry
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.rightTripleFlattenEquiv α β γ).symm _,
    Matrix.submatrix_id_id, Matrix.conjTranspose_mul]
  have hreassoc : (Fam.fuseLastTwoStep α β γ)ᴴ *
      (Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ))ᴴ *
      (Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ) *
        Fam.fuseLastTwoStep α β γ) =
      (Fam.fuseLastTwoStep α β γ)ᴴ *
      ((Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ))ᴴ *
        Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ)) *
      Fam.fuseLastTwoStep α β γ := by
    simp only [Matrix.mul_assoc]
  rw [hreassoc, Fam.blockDiagonal'_rightBlockPiece_isometry, Matrix.mul_one,
    Fam.fuseLastTwoStep_isometry]

/-- **The right iterated fusion isometry conjugates the right-parenthesized triple product**
onto the direct sum whose `(δ, ε)` block is
`χ_{β,γ,δ} ⊗ (χ_{α,δ,ε} ⊗ M_ε)`.

This is the tensor identity obtained by first applying the fusion equation to `M_β M_γ`
and then applying it to each product `M_α M_δ`. It is one side of the two-parenthesization
comparison in the associativity section of arXiv:1511.08090; no change of basis between the two
direct sums is asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`, and arXiv:1511.08090, source lines 237--251. -/
theorem rightFusion_apply (α β γ : Λ) (i k : Fin p) :
    Fam.rightFusionIsometry α β γ *
        (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k *
        (Fam.rightFusionIsometry α β γ)ᴴ =
      Matrix.blockDiagonal' fun δ => Matrix.blockDiagonal' fun ε =>
        Fam.chi.matrix β γ δ ⊗ₖ (Fam.chi.matrix α δ ε ⊗ₖ Fam.tensor ε i k) := by
  unfold rightFusionIsometry
  let A := Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ) * Fam.fuseLastTwoStep α β γ
  let r := (Fam.rightTripleFlattenEquiv α β γ).symm
  let X := (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k
  change A.submatrix r id * X * (A.submatrix r id)ᴴ = _
  rw [Matrix.submatrix_left_conj_equiv]
  dsimp only [A, r, X]
  have hreassoc :
      Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ) * Fam.fuseLastTwoStep α β γ *
          (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k *
          (Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ) *
            Fam.fuseLastTwoStep α β γ)ᴴ =
        Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ) *
          (Fam.fuseLastTwoStep α β γ *
            (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k *
            (Fam.fuseLastTwoStep α β γ)ᴴ) *
          (Matrix.blockDiagonal' (Fam.rightBlockPiece α β γ))ᴴ := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hreassoc, Fam.fuseLastTwoStep_apply, Fam.lastPair_sum_blockDiagonal,
    Matrix.blockDiagonal'_conj]
  simp_rw [Fam.rightBlockPiece_apply]
  rw [rightTripleFlatten_blockDiagonal']

end BNTFusionIsometryFamily
end MPOTensor
