/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.MPDO.BNTFusionIsometries

/-!
# Left iterated fusion of a triple product tensor

Statement (iii) of Theorem IV.13 of arXiv:1606.00608 (label Ualphabeta, lines 986--993 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`) gives, for every pair of labels, an isometry conjugating
the product tensor of the corresponding pair of labelled tensors onto a chi-weighted direct sum.
The remark following the theorem (lines 995--999) observes that associativity of the product in
(eq:algebra) constrains the chi coefficients and, through (Ualphabeta), gives an equation relating
the fusion isometries for the two ways of bracketing a triple product; the source attributes the
construction and the classification of solutions of that equation to
[Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015] (arXiv:1511.08090).
arXiv:1606.00608 itself does not spell out that equation.

This file stays within Cirac--Perez-Garcia--Schuch--Verstraete's own objects (the tensors, the
chi matrices, and the fusion isometries of `BNTFusionIsometryFamily`) and records one concrete
consequence of applying the fusion identity twice: fusing the first two factors of a triple
product tensor with `fusionIsometry α β`, then fusing the result with the third factor label by
label with `fusionIsometry δ γ`, conjugates the triple product tensor onto a tensor that is
block-diagonal in two nested labels, with block `(δ, ε)` equal to the Kronecker product of the
two chi matrices `χ_{α,β,δ}` and `χ_{δ,γ,ε}` with the tensor of label `ε`. This is the
tensor-level refinement, for one bracketing of the triple product, of the associativity remark;
it is infrastructure toward the equation of lines 997--999 relating the two bracketings, not that
equation itself. The comparison with the other bracketing of the triple product is left to a
follow-up.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Theorem IV.13(iii), lines
  986--999 of `Papers/1606.00608/MPDO-22-12-17-2.tex`
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor

/-- A sum, over the physical index `j`, of Kronecker products with a fixed left spectator factor
`X` reassociates against `finProdFinEquiv` and `Equiv.prodAssoc` to exhibit the sum as `X` tensored
with the corresponding letter of the product tensor `mulTensor Y Z`. The reindexing equivalence
`E` is supplied together with a proof that it is this specific composite, so that a caller's own
named equivalence (defeq to the composite) can be substituted and the conclusion matches the
caller's goal on the nose.

Source: bookkeeping lemma for the second fusion stage of arXiv:1606.00608, Theorem IV.13(iii),
lines 986--993. -/
private theorem kronecker_sum_mulTensor {p a bd1 bd2 : ℕ} (X : Matrix (Fin a) (Fin a) ℂ)
    (Y : MPOTensor p bd1) (Z : MPOTensor p bd2) (i k : Fin p)
    (E : Fin a × Fin (bd1 * bd2) ≃ (Fin a × Fin bd1) × Fin bd2)
    (hE : E = (Equiv.prodCongr (Equiv.refl (Fin a)) finProdFinEquiv.symm).trans
        (Equiv.prodAssoc (Fin a) (Fin bd1) (Fin bd2)).symm) :
    (∑ j : Fin p, (X ⊗ₖ Y i j) ⊗ₖ Z j k) =
      (X ⊗ₖ mulTensor Y Z i k).submatrix E.symm E.symm := by
  subst hE
  rw [mulTensor_apply]
  ext ⟨⟨x1, x2⟩, x3⟩ ⟨⟨y1, y2⟩, y3⟩
  simp only [Matrix.submatrix_apply, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.symm_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_symm, Equiv.coe_refl,
    id_eq, Equiv.prodAssoc_apply, Matrix.sum_apply, Matrix.kronecker_apply,
    Equiv.symm_apply_apply]
  simpa only [mul_assoc] using
    Fintype.sum_mul_mul_eq_mul_sum_mul (X x1 y1)
      (fun j => Y i j x2 y2) (fun j => Z j k x3 y3)

namespace BNTFusionIsometryFamily

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

/-- The reindexing equivalence identifying the bond space of the fusion isometry of `α, β`
tensored with a spectator label `γ` with the flattened sigma type of `leftFusionIsometry`'s first
stage. This is the plain distributivity of a sigma type over a product, chosen so that composing
it with its own inverse cancels on the nose in `blockPiece_apply` and `pairBond_sum_blockDiagonal`.

Source: bookkeeping for arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private def pairBondEquiv (α β γ : Λ) :
    ((δ : Λ) × (Fin (Fam.chi.dim α β δ) × Fin (Fam.bondDim δ))) × Fin (Fam.bondDim γ) ≃
      (δ : Λ) × (Fin (Fam.chi.dim α β δ) × Fin (Fam.bondDim δ)) × Fin (Fam.bondDim γ) :=
  Equiv.sigmaProdDistrib (fun δ => Fin (Fam.chi.dim α β δ) × Fin (Fam.bondDim δ))
    (Fin (Fam.bondDim γ))

/-- The reindexing equivalence identifying the multiplicity factor `Fin (chi.dim α β δ)` tensored
with the bond space `bondDim δ * bondDim γ` of the fusion isometry of `δ, γ` with the per-block
product type of `pairBondEquiv`'s target, associated as
`(Fin (chi.dim α β δ) × Fin (bondDim δ)) × Fin (bondDim γ)`.

Source: bookkeeping for arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private def tripleMultEquiv (α β δ γ : Λ) :
    Fin (Fam.chi.dim α β δ) × Fin (Fam.bondDim δ * Fam.bondDim γ) ≃
      (Fin (Fam.chi.dim α β δ) × Fin (Fam.bondDim δ)) × Fin (Fam.bondDim γ) :=
  (Equiv.prodCongr (Equiv.refl (Fin (Fam.chi.dim α β δ))) finProdFinEquiv.symm).trans
    (Equiv.prodAssoc (Fin (Fam.chi.dim α β δ)) (Fin (Fam.bondDim δ))
      (Fin (Fam.bondDim γ))).symm

/-- The reindexing equivalence flattening the two-level sigma type produced by fusing `α, β` and
then `δ, γ` down to a single pair of labels `δ, ε` with their multiplicity indices.

Source: bookkeeping for arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private def tripleFlattenEquiv (α β γ : Λ) :
    (δ : Λ) × Fin (Fam.chi.dim α β δ) × (ε : Λ) × Fin (Fam.chi.dim δ γ ε) ×
        Fin (Fam.bondDim ε) ≃
      (δ : Λ) × (ε : Λ) × Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε) ×
        Fin (Fam.bondDim ε) :=
  Equiv.sigmaCongrRight fun δ =>
    (Equiv.prodComm (Fin (Fam.chi.dim α β δ))
        ((ε : Λ) × Fin (Fam.chi.dim δ γ ε) × Fin (Fam.bondDim ε))).trans
      ((Equiv.sigmaProdDistrib (fun ε => Fin (Fam.chi.dim δ γ ε) × Fin (Fam.bondDim ε))
          (Fin (Fam.chi.dim α β δ))).trans
        (Equiv.sigmaCongrRight fun ε =>
          Equiv.prodComm (Fin (Fam.chi.dim δ γ ε) × Fin (Fam.bondDim ε))
            (Fin (Fam.chi.dim α β δ))))

/-- The first stage of the left iterated fusion isometry: `fusionIsometry α β` tensored with the
identity on the bond space of `γ`, reindexed against `γ`'s bond space by `pairBondEquiv` and
against `Fin (bondDim α * bondDim β * bondDim γ)` by `finProdFinEquiv`, exactly as `mulTensor`
itself reindexes bond spaces.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private noncomputable def fuseFirstTwoStep (α β γ : Λ) :
    Matrix ((δ : Λ) × (Fin (Fam.chi.dim α β δ) × Fin (Fam.bondDim δ)) ×
        Fin (Fam.bondDim γ))
      (Fin (Fam.bondDim α * Fam.bondDim β * Fam.bondDim γ)) ℂ :=
  (Fam.fusionIsometry α β ⊗ₖ
      (1 : Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)).submatrix
    (Fam.pairBondEquiv α β γ).symm finProdFinEquiv.symm

private theorem fuseFirstTwoStep_isometry (α β γ : Λ) :
    (Fam.fuseFirstTwoStep α β γ)ᴴ * Fam.fuseFirstTwoStep α β γ = 1 := by
  unfold fuseFirstTwoStep
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.pairBondEquiv α β γ).symm _,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Fam.isometry,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

private theorem fuseFirstTwoStep_apply (α β γ : Λ) (i k : Fin p) :
    Fam.fuseFirstTwoStep α β γ *
        (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k *
        (Fam.fuseFirstTwoStep α β γ)ᴴ =
      (∑ j : Fin p,
          (Matrix.blockDiagonal' fun δ => Fam.chi.matrix α β δ ⊗ₖ Fam.tensor δ i j) ⊗ₖ
            Fam.tensor γ j k).submatrix (Fam.pairBondEquiv α β γ).symm
        (Fam.pairBondEquiv α β γ).symm := by
  unfold fuseFirstTwoStep
  rw [mulTensor_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Fam.fusion]

/-- The second stage of the left iterated fusion isometry, block `δ`: the identity on the
multiplicity factor `Fin (chi.dim α β δ)` tensored with `fusionIsometry δ γ`, reindexed by
`tripleMultEquiv` against the block-`δ` fiber of `pairBondEquiv`'s target.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private noncomputable def blockPiece (α β γ δ : Λ) :
    Matrix (Fin (Fam.chi.dim α β δ) × (ε : Λ) × Fin (Fam.chi.dim δ γ ε) ×
        Fin (Fam.bondDim ε))
      ((Fin (Fam.chi.dim α β δ) × Fin (Fam.bondDim δ)) × Fin (Fam.bondDim γ)) ℂ :=
  ((1 : Matrix (Fin (Fam.chi.dim α β δ)) (Fin (Fam.chi.dim α β δ)) ℂ) ⊗ₖ
      Fam.fusionIsometry δ γ).submatrix (Equiv.refl _) (Fam.tripleMultEquiv α β δ γ).symm

private theorem blockPiece_isometry (α β γ δ : Λ) :
    (Fam.blockPiece α β γ δ)ᴴ * Fam.blockPiece α β γ δ = 1 := by
  unfold blockPiece
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Fam.isometry,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/-- Conjugating a fixed `δ`-block of the fused pair, summed against the third factor's physical
index, by `blockPiece` reduces to the fusion identity of `fusionIsometry δ γ` applied to the
letter `mulTensor (tensor δ) (tensor γ) i k`, with `chi.matrix α β δ` carried through as a
spectator factor.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private theorem blockPiece_apply (α β γ δ : Λ) (i k : Fin p) :
    Fam.blockPiece α β γ δ *
        (∑ j : Fin p, (Fam.chi.matrix α β δ ⊗ₖ Fam.tensor δ i j) ⊗ₖ
            Fam.tensor γ j k) *
        (Fam.blockPiece α β γ δ)ᴴ =
      Fam.chi.matrix α β δ ⊗ₖ
        Matrix.blockDiagonal' fun ε => Fam.chi.matrix δ γ ε ⊗ₖ Fam.tensor ε i k := by
  rw [kronecker_sum_mulTensor _ _ _ _ _ (Fam.tripleMultEquiv α β δ γ) rfl]
  unfold blockPiece
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.tripleMultEquiv α β δ γ).symm _,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.tripleMultEquiv α β δ γ).symm _,
    Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.conjTranspose_one, Matrix.mul_one, Fam.fusion]

/-- Flattening the two-level block-diagonal structure produced by fusing `α, β` and then `δ, γ`
via `tripleFlattenEquiv`: the nested block-diagonal matrix reindexes to the single block-diagonal
matrix over the pair `(δ, ε)`.

Source: bookkeeping lemma for arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private theorem tripleFlatten_blockDiagonal' (α β γ : Λ)
    (X : ∀ δ, Matrix (Fin (Fam.chi.dim α β δ)) (Fin (Fam.chi.dim α β δ)) ℂ)
    (Y : ∀ δ ε, Matrix (Fin (Fam.chi.dim δ γ ε)) (Fin (Fam.chi.dim δ γ ε)) ℂ)
    (T : ∀ ε, Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ) :
    (Matrix.blockDiagonal' fun δ =>
        X δ ⊗ₖ Matrix.blockDiagonal' fun ε => Y δ ε ⊗ₖ T ε).submatrix
        (Fam.tripleFlattenEquiv α β γ).symm (Fam.tripleFlattenEquiv α β γ).symm =
      Matrix.blockDiagonal' fun δ =>
        Matrix.blockDiagonal' fun ε => X δ ⊗ₖ (Y δ ε ⊗ₖ T ε) := by
  ext ⟨δ, ε, m1, m2, b⟩ ⟨δ', ε', m1', m2', b'⟩
  simp only [Matrix.submatrix_apply, tripleFlattenEquiv, Equiv.symm_trans_apply,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Equiv.sigmaProdDistrib_symm_apply]
  by_cases hδ : δ = δ'
  · subst hδ
    by_cases hε : ε = ε'
    · subst hε; simp
    · simp [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_ne _ _ _ hε]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hδ]

/-- The sum, over the physical index `j`, of the block-diagonal chi-weighted letters produced by
`fuseFirstTwoStep_apply` reindexes, via `pairBondEquiv`, to the block-diagonal matrix whose block
`δ` is the corresponding sum carried entirely inside the block.

Source: bookkeeping lemma for arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
private theorem pairBond_sum_blockDiagonal (α β γ : Λ) (i k : Fin p) :
    (∑ j : Fin p,
        (Matrix.blockDiagonal' fun δ => Fam.chi.matrix α β δ ⊗ₖ Fam.tensor δ i j) ⊗ₖ
          Fam.tensor γ j k).submatrix (Fam.pairBondEquiv α β γ).symm
        (Fam.pairBondEquiv α β γ).symm =
      Matrix.blockDiagonal' fun δ =>
        ∑ j : Fin p, (Fam.chi.matrix α β δ ⊗ₖ Fam.tensor δ i j) ⊗ₖ
          Fam.tensor γ j k := by
  ext ⟨δ, m1, m2, b⟩ ⟨δ', m1', m2', b'⟩
  simp only [Matrix.submatrix_apply, pairBondEquiv, Equiv.sigmaProdDistrib_symm_apply,
    Matrix.sum_apply, Matrix.kronecker_apply, Matrix.blockDiagonal'_apply]
  by_cases hδ : δ = δ'
  · subst hδ; simp
  · simp [hδ]

private theorem blockDiagonal'_blockPiece_isometry (α β γ : Λ) :
    (Matrix.blockDiagonal' (Fam.blockPiece α β γ))ᴴ *
        Matrix.blockDiagonal' (Fam.blockPiece α β γ) = 1 := by
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp_rw [Fam.blockPiece_isometry]
  exact Matrix.blockDiagonal'_one

/-- **The left iterated fusion isometry** of a triple of labels: apply `fusionIsometry α β` to
fuse the first two factors, then apply `fusionIsometry δ γ` for each intermediate label `δ` to
fuse the result with the third factor. Concretely, this composes `fuseFirstTwoStep` (the fusion
isometry of `α, β` tensored with the identity on `γ`'s bond space, reindexed against
`Fin (bondDim α * bondDim β * bondDim γ)`) with the block-diagonal family of
`fusionIsometry δ γ` maps, and flattens the resulting two-level sigma type of intermediate and
final labels via `tripleFlattenEquiv`.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--993, and the associativity remark, lines
995--999, of `Papers/1606.00608/MPDO-22-12-17-2.tex`. This is the tensor-level object underlying
one bracketing of the equation of lines 997--999 relating the two ways of fusing a triple
product; the source attributes the construction and the classification of solutions of that
equation to arXiv:1511.08090, not to arXiv:1606.00608 itself. -/
noncomputable def leftFusionIsometry (α β γ : Λ) :
    Matrix ((δ : Λ) × (ε : Λ) × Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε) ×
        Fin (Fam.bondDim ε))
      (Fin (Fam.bondDim α * Fam.bondDim β * Fam.bondDim γ)) ℂ :=
  (Matrix.blockDiagonal' (Fam.blockPiece α β γ) * Fam.fuseFirstTwoStep α β γ).submatrix
    (Fam.tripleFlattenEquiv α β γ).symm id

/-- **`leftFusionIsometry` is an isometry**: the composite of the two fusion-isometry stages is
again an isometry.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--993. -/
theorem leftFusionIsometry_isometry (α β γ : Λ) :
    (Fam.leftFusionIsometry α β γ)ᴴ * Fam.leftFusionIsometry α β γ = 1 := by
  unfold leftFusionIsometry
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Fam.tripleFlattenEquiv α β γ).symm _,
    Matrix.submatrix_id_id, Matrix.conjTranspose_mul]
  have hreassoc : (Fam.fuseFirstTwoStep α β γ)ᴴ *
      (Matrix.blockDiagonal' (Fam.blockPiece α β γ))ᴴ *
      (Matrix.blockDiagonal' (Fam.blockPiece α β γ) * Fam.fuseFirstTwoStep α β γ) =
      (Fam.fuseFirstTwoStep α β γ)ᴴ *
      ((Matrix.blockDiagonal' (Fam.blockPiece α β γ))ᴴ *
        Matrix.blockDiagonal' (Fam.blockPiece α β γ)) * Fam.fuseFirstTwoStep α β γ := by
    simp only [Matrix.mul_assoc]
  rw [hreassoc, Fam.blockDiagonal'_blockPiece_isometry, Matrix.mul_one,
    Fam.fuseFirstTwoStep_isometry]

/-- **`leftFusionIsometry` conjugates the triple product tensor onto a doubly block-diagonal
tensor**: applying `leftFusionIsometry α β γ` to a letter of the triple product tensor
`mulTensor (mulTensor (tensor α) (tensor β)) (tensor γ)` gives the tensor block-diagonal in the
intermediate label `δ` and the final label `ε`, with block `(δ, ε)` equal to the chi matrices
`χ_{α,β,δ}` and `χ_{δ,γ,ε}` tensored with the letter of the tensor of label `ε`.

This is the tensor-level refinement, for the left bracketing `(M_α M_β) M_γ` of the triple
product, of the associativity remark following Theorem IV.13(iii) (lines 995--999): the source
observes that associativity of the product constrains the chi coefficients and, via the isometry
statement (Ualphabeta), gives an equation relating the fusion isometries of the two bracketings
of a triple product, attributing the construction of that equation to arXiv:1511.08090. This
theorem stays within the source's own objects and records one concrete conjugation identity that
such an equation would relate to the corresponding identity for the right bracketing
`M_α (M_β M_γ)`; that comparison is left to a follow-up.

The block content is stated as
`χ_{α,β,δ} ⊗ (χ_{δ,γ,ε} ⊗ tensor_ε^{ij})`, right-associated in the Kronecker product,
rather than the left-associated `(χ_{α,β,δ} ⊗ χ_{δ,γ,ε}) ⊗ tensor_ε^{ij}`. This is a
harmless reassociation of the same three factors in the same order, forced by the natural bond
splitting
of `mulTensor`.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--993, and the associativity remark, lines
995--999, of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem leftFusion_apply (α β γ : Λ) (i k : Fin p) :
    Fam.leftFusionIsometry α β γ *
        (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k *
        (Fam.leftFusionIsometry α β γ)ᴴ =
      Matrix.blockDiagonal' fun δ => Matrix.blockDiagonal' fun ε =>
        Fam.chi.matrix α β δ ⊗ₖ (Fam.chi.matrix δ γ ε ⊗ₖ Fam.tensor ε i k) := by
  unfold leftFusionIsometry
  rw [Matrix.submatrix_left_conj_equiv]
  have hreassoc :
      Matrix.blockDiagonal' (Fam.blockPiece α β γ) * Fam.fuseFirstTwoStep α β γ *
          (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k *
          (Matrix.blockDiagonal' (Fam.blockPiece α β γ) * Fam.fuseFirstTwoStep α β γ)ᴴ =
        Matrix.blockDiagonal' (Fam.blockPiece α β γ) *
          (Fam.fuseFirstTwoStep α β γ *
              (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k *
              (Fam.fuseFirstTwoStep α β γ)ᴴ) *
          (Matrix.blockDiagonal' (Fam.blockPiece α β γ))ᴴ := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hreassoc, Fam.fuseFirstTwoStep_apply, Fam.pairBond_sum_blockDiagonal,
    Matrix.blockDiagonal'_conj]
  simp_rw [Fam.blockPiece_apply]
  rw [tripleFlatten_blockDiagonal']

end BNTFusionIsometryFamily
end MPOTensor
