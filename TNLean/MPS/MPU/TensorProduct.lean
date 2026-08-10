/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixRankKronecker
import TNLean.Algebra.TraceReindex
import TNLean.MPS.MPU.Basic
import TNLean.MPS.MPU.SourceCuts

/-!
# Independent tensor products of matrix product unitaries

This file defines the independent tensor product of two MPO tensors. Both physical
spaces and both virtual spaces are tensored, so tensors of dimensions `(d, D)` and
`(e, E)` produce one of dimensions `(d * e, D * E)`. This operation is distinct
from contraction-based MPO multiplication.

The construction is the tensoring operation in the proof of part (ii) of the Index
Theorem in arXiv:1703.09188, lines 824--847.

## Main definitions

* `MPOTensor.tensorProduct`: the local Kronecker product with standard finite-product
  coordinates.
* `MPOTensor.tensorProductConfigEquiv`: the sitewise splitting of product physical
  configurations.
* `MPOTensor.tensorProductCutShuffle`: the shuffle relating a Kronecker product of
  source cuts to the source cut of a tensor product.

## Main results

* `MPOTensor.mpo_tensorProduct`: the exact finite-size reindexed-Kronecker formula.
* `MPOTensor.IsMPU.tensorProduct`: independent tensor products preserve the MPU property.
* `MPOTensor.sourceCutM₁_tensorProduct`, `MPOTensor.sourceCutM₂_tensorProduct`: the two
  source-cut identities, with the right and left orientations unchanged.
* `MPOTensor.rightRank_tensorProduct`, `MPOTensor.leftRank_tensorProduct`: multiplicativity
  of the two source ranks.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D e E : ℕ}

/-- The independent tensor product of two MPO tensors, using `finProdFinEquiv` on
both physical and virtual indices.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
def tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    MPOTensor (d * e) (D * E) :=
  fun ij kl ↦ Matrix.reindex finProdFinEquiv finProdFinEquiv
    (U ij.divNat kl.divNat ⊗ₖ V ij.modNat kl.modNat)

/-- Entry formula for the independent tensor product. -/
@[simp] theorem tensorProduct_apply (U : MPOTensor d D) (V : MPOTensor e E)
    (i j : Fin d) (k l : Fin e) (α β : Fin D) (γ δ : Fin E) :
    tensorProduct U V (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l))
        (finProdFinEquiv (α, γ)) (finProdFinEquiv (β, δ)) =
      U i j α β * V k l γ δ := by
  simp [tensorProduct, Matrix.reindex_apply]

/-- Split a product-valued physical configuration site by site. -/
def tensorProductConfigEquiv (N d e : ℕ) :
    (Fin N → Fin (d * e)) ≃ (Fin N → Fin d) × (Fin N → Fin e) :=
  (Equiv.arrowCongr (Equiv.refl (Fin N)) finProdFinEquiv.symm).trans
    (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ ↦ Fin d) (fun _ ↦ Fin e))

private theorem evalWord_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E)
    (is js : List (Fin (d * e))) :
    evalWord (tensorProduct U V) is js =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (evalWord U (is.map Fin.divNat) (js.map Fin.divNat) ⊗ₖ
          evalWord V (is.map Fin.modNat) (js.map Fin.modNat)) := by
  induction is generalizing js with
  | nil =>
      cases js <;> simp [evalWord, Matrix.one_kronecker_one]
  | cons i is ih =>
      cases js with
      | nil => simp [evalWord]
      | cons j js =>
          simp only [evalWord_cons, List.map_cons, tensorProduct]
          rw [ih]
          rw [← Matrix.coe_reindexRingEquiv ℂ finProdFinEquiv]
          rw [← map_mul, Matrix.mul_kronecker_mul]

/-- The closed MPO of an independent tensor product is the Kronecker product of
the two closed MPOs, in sitewise product coordinates.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem mpo_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) (N : ℕ) :
    mpo (tensorProduct U V) N =
      Matrix.reindex (tensorProductConfigEquiv N d e).symm
        (tensorProductConfigEquiv N d e).symm (mpo U N ⊗ₖ mpo V N) := by
  ext σ τ
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    mpo_apply, mpoMatrixEntry]
  rw [evalWord_tensorProduct, Matrix.trace_reindex, Matrix.trace_kronecker]
  simp [tensorProductConfigEquiv, Equiv.arrowCongr, Function.comp_def]

/-- Independent tensor products of matrix product unitaries are matrix product
unitaries.

Source: arXiv:1703.09188, Theorem `IndexTh` (ii), lines 824--847. -/
theorem IsMPU.tensorProduct {U : MPOTensor d D} {V : MPOTensor e E}
    (hU : IsMPU U) (hV : IsMPU V) : IsMPU (tensorProduct U V) := by
  intro N hN
  rw [mpo_tensorProduct]
  apply Matrix.reindex_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, hU.mpo_mul_conjTranspose_mpo hN,
    hV.mpo_mul_conjTranspose_mpo hN, Matrix.one_kronecker_one]

/-- Shuffle `((α, j), (α', j'))` to `((α, α'), (j, j'))`, encoding each
new pair by `finProdFinEquiv`. This is the coordinate change between a
Kronecker product of source cuts and the source cut of a tensor product. -/
def tensorProductCutShuffle (a b c f : ℕ) :
    ((Fin a × Fin b) × (Fin c × Fin f)) ≃ (Fin (a * c) × Fin (b * f)) where
  toFun x := (finProdFinEquiv (x.1.1, x.2.1), finProdFinEquiv (x.1.2, x.2.2))
  invFun x :=
    (((finProdFinEquiv.symm x.1).1, (finProdFinEquiv.symm x.2).1),
      ((finProdFinEquiv.symm x.1).2, (finProdFinEquiv.symm x.2).2))
  left_inv x := by simp
  right_inv x := by simp

/-- The first source cut of an independent tensor product is the reindexed
Kronecker product of the first source cuts. Its row shuffle is
`((α,j),(α',j')) ↦ ((α,α'),(j,j'))`, so the paper's right orientation is
preserved without a swap.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem sourceCutM₁_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    sourceCutM₁ (tensorProduct U V) =
      Matrix.reindex (tensorProductCutShuffle D d E e)
        (tensorProductCutShuffle d D e E) (sourceCutM₁ U ⊗ₖ sourceCutM₁ V) := by
  ext row col
  obtain ⟨αγ, jl⟩ := row
  obtain ⟨ik, βδ⟩ := col
  obtain ⟨α, γ⟩ := finProdFinEquiv.symm αγ
  obtain ⟨j, l⟩ := finProdFinEquiv.symm jl
  obtain ⟨i, k⟩ := finProdFinEquiv.symm ik
  obtain ⟨β, δ⟩ := finProdFinEquiv.symm βδ
  simp [tensorProductCutShuffle, Matrix.reindex_apply]

/-- The second source cut of an independent tensor product is the reindexed
Kronecker product of the second source cuts. Its row shuffle is
`((α,i),(α',i')) ↦ ((α,α'),(i,i'))`, so the paper's left orientation is
preserved without a swap.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem sourceCutM₂_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    sourceCutM₂ (tensorProduct U V) =
      Matrix.reindex (tensorProductCutShuffle D d E e)
        (tensorProductCutShuffle d D e E) (sourceCutM₂ U ⊗ₖ sourceCutM₂ V) := by
  ext row col
  obtain ⟨αγ, ik⟩ := row
  obtain ⟨jl, βδ⟩ := col
  obtain ⟨α, γ⟩ := finProdFinEquiv.symm αγ
  obtain ⟨i, k⟩ := finProdFinEquiv.symm ik
  obtain ⟨j, l⟩ := finProdFinEquiv.symm jl
  obtain ⟨β, δ⟩ := finProdFinEquiv.symm βδ
  simp [tensorProductCutShuffle, Matrix.reindex_apply]

/-- The right source rank is multiplicative under independent tensor products.
The first source cut retains the paper's right orientation.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem rightRank_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    r[tensorProduct U V] = r[U] * r[V] := by
  rw [rightRank, sourceCutM₁_tensorProduct, Matrix.rank_reindex,
    Matrix.rank_kronecker]
  rfl

/-- The left source rank is multiplicative under independent tensor products.
The second source cut retains the paper's left orientation.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem leftRank_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    ℓ[tensorProduct U V] = ℓ[U] * ℓ[V] := by
  rw [leftRank, sourceCutM₂_tensorProduct, Matrix.rank_reindex,
    Matrix.rank_kronecker]
  rfl

end MPOTensor
