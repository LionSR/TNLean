/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.ComplexOfRing
import TNLean.MPS.MPDO.DirectSum
import TNLean.MPS.MPDO.OperatorProduct

/-!
# The operator product of block-diagonal matrix product operator tensors

**Source.** None: this is infrastructure of this development, and no paper states it.

**Formalized here.** If the letters of two matrix product operator tensors `A` and `B` are,
after relabellings `e₁` and `e₂` of their bond coordinates, block diagonal with blocks `M k`
and `N l`, then the letters of the stacked product `A · B` are block diagonal over the pairs
`(k, l)`, with the stacked products `M k · N l` as blocks. The bond coordinates of the pair
`(k, l)` are the products of the coordinates of `k` and of `l`, relabelled by `mulBond e₁ e₂`.
This is how the stacked square of a direct sum `⊕_g U_g`, such as a condensation defect, splits
into the pair blocks `U_g · U_h`.

## Main definitions

* `MPOTensor.sigmaProdFinEquiv`: the coordinates of the pair blocks as pairs of coordinates.
* `MPOTensor.mulBond`: the labelling of the bond coordinates of `A · B` by the coordinates of
  the pair blocks.

## Main results

* `MPOTensor.directSum_complexOfRing`: the direct sum of the images of tensors over a subring of
  the complex numbers is the image of their direct sum, so that identities of direct sums over
  the subring can be decided there.
* `MPOTensor.mulTensor_blockDiagonal'`: the letters of the stacked product of two block-diagonal
  tensors are block diagonal over the pairs of blocks.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {κ ν : Type*} {n : κ → ℕ} {m : ν → ℕ}

/-- The coordinates of the pair blocks, a coordinate of the block `(k, l)` being a pair of a
coordinate of `k` and a coordinate of `l`. -/
def sigmaProdFinEquiv (n : κ → ℕ) (m : ν → ℕ) :
    (Σ kl : κ × ν, Fin (n kl.1 * m kl.2)) ≃ (Σ k, Fin (n k)) × (Σ l, Fin (m l)) where
  toFun x := (⟨x.1.1, (finProdFinEquiv.symm x.2).1⟩, ⟨x.1.2, (finProdFinEquiv.symm x.2).2⟩)
  invFun y := ⟨(y.1.1, y.2.1), finProdFinEquiv (y.1.2, y.2.2)⟩
  left_inv x := by
    obtain ⟨⟨k, l⟩, r⟩ := x
    change (⟨(k, l), finProdFinEquiv (finProdFinEquiv.symm r)⟩ :
      Σ kl : κ × ν, Fin (n kl.1 * m kl.2)) = ⟨(k, l), r⟩
    rw [Equiv.apply_symm_apply]
  right_inv y := by
    obtain ⟨⟨k, a⟩, ⟨l, b⟩⟩ := y
    simp

/-- The labelling of the bond coordinates of a stacked product by the coordinates of the pair
blocks: a coordinate of the block `(k, l)` is sent to the pair of its coordinates in `A` and in
`B`, in the bond order of `finProdFinEquiv`. -/
def mulBond {D₁ D₂ : ℕ} (e₁ : (Σ k, Fin (n k)) ≃ Fin D₁) (e₂ : (Σ l, Fin (m l)) ≃ Fin D₂) :
    (Σ kl : κ × ν, Fin (n kl.1 * m kl.2)) ≃ Fin (D₁ * D₂) :=
  (sigmaProdFinEquiv n m).trans ((e₁.prodCongr e₂).trans finProdFinEquiv)

variable [DecidableEq κ] [DecidableEq ν] {d D₁ D₂ : ℕ}

/-- **The stacked product of block-diagonal tensors is block diagonal over the pairs of
blocks.** If `A^{ij}` is block diagonal along `e₁` with blocks `M k` and `B^{ij}` along `e₂`
with blocks `N l`, then `(A · B)^{ik}` is block diagonal along `mulBond e₁ e₂` with blocks
`(M k · N l)^{ik}`. -/
theorem mulTensor_blockDiagonal' (M : ∀ k, MPOTensor d (n k)) (N : ∀ l, MPOTensor d (m l))
    (e₁ : (Σ k, Fin (n k)) ≃ Fin D₁) (e₂ : (Σ l, Fin (m l)) ≃ Fin D₂) {A : MPOTensor d D₁}
    {B : MPOTensor d D₂}
    (hA : ∀ i j, A i j = (Matrix.blockDiagonal' fun k => M k i j).submatrix e₁.symm e₁.symm)
    (hB : ∀ i j, B i j = (Matrix.blockDiagonal' fun l => N l i j).submatrix e₂.symm e₂.symm)
    (i k : Fin d) :
    mulTensor A B i k =
      (Matrix.blockDiagonal' fun kl : κ × ν => mulTensor (M kl.1) (N kl.2) i k).submatrix
        (mulBond e₁ e₂).symm (mulBond e₁ e₂).symm := by
  ext a b
  obtain ⟨⟨⟨k₁, l₁⟩, r⟩, rfl⟩ := (mulBond e₁ e₂).surjective a
  obtain ⟨⟨⟨k₂, l₂⟩, c⟩, rfl⟩ := (mulBond e₁ e₂).surjective b
  simp only [mulTensor_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, hA, hB]
  simp only [mulBond, sigmaProdFinEquiv, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.prodCongr_apply, Prod.map, Equiv.symm_apply_apply]
  by_cases hk : k₁ = k₂
  · subst hk
    by_cases hl : l₁ = l₂
    · subst hl
      simp [Matrix.blockDiagonal'_apply_eq, Matrix.sum_apply]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun h => hl (congrArg Prod.snd h))]
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hl]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun h => hk (congrArg Prod.fst h))]
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ hk]

/-- The direct sum of the images of two tensors over a ring `R →+* ℂ` is the image of the direct
sum of the two tensors, formed over `R`. -/
theorem directSum_complexOfRing {R : Type*} [CommRing R] (f : R →+* ℂ)
    (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (i j : Fin d) :
    directSum (fun i j => MPSTensor.complexOfRing f (M i j))
        (fun i j => MPSTensor.complexOfRing f (N i j)) i j =
      MPSTensor.complexOfRing f ((Matrix.fromBlocks (M i j) 0 0 (N i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) := by
  simp only [directSum, MPSTensor.complexOfRing]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f),
    Matrix.map_zero _ (map_zero f)]

end MPOTensor
