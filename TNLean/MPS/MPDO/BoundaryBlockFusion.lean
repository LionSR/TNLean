/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryRestriction

/-!
# Fusion decompositions for fixed incoming blocks

Closedness of the complete arbitrary-boundary MPO family gives exact local
fusion tensors for each pair of invariant retracts of the MPO bond space.
Coordinate inclusions of the original blocks provide the required retracts.
The multiplicities may depend on both incoming block labels.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `fusiontensors`,
  `eq:orthoW`, and Appendix A, the block-projector argument.
-/

open scoped Matrix BigOperators Kronecker

noncomputable section

namespace MPOTensor

variable {d D D₁ D₂ E₁ E₂ F₁ F₂ r : ℕ} {dim : Fin r → ℕ}

/-- A rectangular Kronecker product in the flattened bond coordinates used
by the stacked MPO tensor. -/
def stackedBondMap (W₁ : Matrix (Fin D₁) (Fin E₁) ℂ)
    (W₂ : Matrix (Fin D₂) (Fin E₂) ℂ) :
    Matrix (Fin (D₁ * D₂)) (Fin (E₁ * E₂)) ℂ :=
  (W₁ ⊗ₖ W₂).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Stacking rectangular bond maps preserves their composition. -/
theorem stackedBondMap_mul (W₁ : Matrix (Fin D₁) (Fin E₁) ℂ)
    (W₂ : Matrix (Fin D₂) (Fin E₂) ℂ)
    (V₁ : Matrix (Fin E₁) (Fin F₁) ℂ) (V₂ : Matrix (Fin E₂) (Fin F₂) ℂ) :
    stackedBondMap W₁ W₂ * stackedBondMap V₁ V₂ =
      stackedBondMap (W₁ * V₁) (W₂ * V₂) := by
  simp only [stackedBondMap, Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

/-- Stacking identity bond maps gives the identity on the stacked space. -/
@[simp] theorem stackedBondMap_one :
    stackedBondMap (1 : Matrix (Fin D₁) (Fin D₁) ℂ)
      (1 : Matrix (Fin D₂) (Fin D₂) ℂ) = 1 := by
  simp only [stackedBondMap, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- Two invariant bond inclusions give an invariant inclusion of the
corresponding stacked tensor. Source: GLM23, Appendix A, restriction to
incoming blocks before `decompopen`. -/
theorem mulTensor_intertwine_stackedBondMap
    (T₁ : MPOTensor d D₁) (T₂ : MPOTensor d D₂)
    (S₁ : MPOTensor d E₁) (S₂ : MPOTensor d E₂)
    (W₁ : Matrix (Fin D₁) (Fin E₁) ℂ) (W₂ : Matrix (Fin D₂) (Fin E₂) ℂ)
    (hW₁ : ∀ i j, T₁ i j * W₁ = W₁ * S₁ i j)
    (hW₂ : ∀ i j, T₂ i j * W₂ = W₂ * S₂ i j) (i k : Fin d) :
    mulTensor T₁ T₂ i k * stackedBondMap W₁ W₂ =
      stackedBondMap W₁ W₂ * mulTensor S₁ S₂ i k := by
  simp only [mulTensor_apply, stackedBondMap, Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hW₁, hW₂]

/-- Closedness gives an exact fusion decomposition for any two invariant
bond retracts of the original tensor. In particular, coordinate inclusions
of fixed incoming blocks give their individual fusion multiplicities.
Source: GLM23, Appendix A, `decompopen` and `eq:ortho`. -/
theorem IsBoundaryClosed.exists_fusionDecomposition_of_retracts
    {T : MPOTensor d (∑ c : Fin r, dim c)} (hT : IsBoundaryClosed T)
    (A : (c : Fin r) → MPSTensor (d * d) (dim c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L)
    (S₁ : MPOTensor d E₁) (S₂ : MPOTensor d E₂)
    (V₁ : Matrix (Fin E₁) (Fin (∑ c : Fin r, dim c)) ℂ)
    (W₁ : Matrix (Fin (∑ c : Fin r, dim c)) (Fin E₁) ℂ)
    (V₂ : Matrix (Fin E₂) (Fin (∑ c : Fin r, dim c)) ℂ)
    (W₂ : Matrix (Fin (∑ c : Fin r, dim c)) (Fin E₂) ℂ)
    (hVW₁ : V₁ * W₁ = 1) (hVW₂ : V₂ * W₂ = 1)
    (hW₁ : ∀ i j, T i j * W₁ = W₁ * S₁ i j)
    (hW₂ : ∀ i j, T i j * W₂ = W₂ * S₂ i j) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (E₁ * E₂)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (E₁ * E₂)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (mulTensor S₁ S₂).toMPSTensor
        (fun q : (c : Fin r) × Fin (m c) ↦ A q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨b, hb⟩ := (isBoundaryClosed_iff_exists_linearMap T).mp hT
  apply MPSTensor.exists_biorthogonalDecomposition_of_boundaryTransport_restrict
    (mulTensor T T).toMPSTensor (mulTensor S₁ S₂).toMPSTensor A
    (Matrix.finSigmaDiagonalBlocks.comp b) ?_
    (stackedBondMap V₁ V₂) (stackedBondMap W₁ W₂) ?_ ?_ hL hSpan
  · intro n hn X w
    rw [mpvWithBoundary_toMPSTensor]
    have hh := congrArg (fun M ↦ M (fun k ↦ (w k).divNat) (fun k ↦ (w k).modNat))
      (hb n hn X)
    rw [hh, ← mpvWithBoundary_toMPSTensor, hBlocks,
      MPSTensor.mpvWithBoundary_toTensorFromBlocks_one]
    rfl
  · rw [stackedBondMap_mul, hVW₁, hVW₂, stackedBondMap_one]
  · intro i
    exact mulTensor_intertwine_stackedBondMap T T S₁ S₂ W₁ W₂ hW₁ hW₂
      i.divNat i.modNat

/-- The individual incoming blocks of a closed block-diagonal tensor have
exact biorthogonal fusion tensors. Source: GLM23, `fusiontensors`,
`eq:orthoW`, and Appendix A. -/
theorem IsBoundaryClosed.exists_blockFusionDecomposition
    {T : MPOTensor d (∑ c : Fin r, dim c)} (hT : IsBoundaryClosed T)
    (A : (c : Fin r) → MPOTensor d (dim c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun c ↦ (A c).toMPSTensor))
    {L : ℕ} (hL : 0 < L)
    (hSpan : MPSTensor.WordTupleSpanTop (fun c ↦ (A c).toMPSTensor) L)
    (a b : Fin r) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (dim a * dim b)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (dim a * dim b)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (A a) (A b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (m c) ↦ (A q.1).toMPSTensor)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  have hinter c i j : T i j * MPSTensor.blockInclusion dim c =
      MPSTensor.blockInclusion dim c * A c i j := by
    have h := MPSTensor.toTensorFromBlocks_mul_blockInclusion
      (fun _ ↦ 1) (fun c ↦ (A c).toMPSTensor) c (finProdFinEquiv (i, j))
    rw [← hBlocks] at h
    simpa [toMPSTensor] using h
  exact hT.exists_fusionDecomposition_of_retracts
    (fun c ↦ (A c).toMPSTensor) hBlocks hL hSpan (A a) (A b)
    (MPSTensor.blockInclusion dim a)ᴴ (MPSTensor.blockInclusion dim a)
    (MPSTensor.blockInclusion dim b)ᴴ (MPSTensor.blockInclusion dim b)
    (MPSTensor.blockInclusion_conjTranspose_mul_self dim a)
    (MPSTensor.blockInclusion_conjTranspose_mul_self dim b)
    (hinter a) (hinter b)

end MPOTensor
