/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryKronecker
import QICLean.Algebra.MatrixReindex
import TNLean.MPS.MPU.SourceUV
import TNLean.MPS.MPU.TensorProduct

/-!
# Source factors of independent tensor products

This module constructs supplied source factors for an independent tensor
product from supplied identity-weight factors for its two constituents.  The
source ranks and the entries of the paper's tensors $u$ and $v$ are
multiplicative in the corresponding product-rank coordinates.

The identity-weight restriction is explicit in the declaration names below.
An arbitrary-weight construction would additionally require a source-weight
shuffle relating the reindexed virtual Kronecker weight to the two constituent
source weights; that construction is not used for the shift formulas.

This is formalization infrastructure for the tensoring clause of Theorem
`IndexTh` (ii), which arXiv:1703.09188 calls trivial in lines 824--847; the
paper does not print these explicit supplied factors.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

/-- Product source coordinates, followed by the multiplicative right-rank
identification for an independent tensor product.

Formalization infrastructure for the tensoring clause of Theorem `IndexTh`
(ii), which arXiv:1703.09188 calls trivial in lines 824--847. -/
noncomputable def tensorProductRightRankEquiv
    {d D e E : ℕ} (U : MPOTensor d D) (V : MPOTensor e E) :
    Fin r[U] × Fin r[V] ≃ Fin r[tensorProduct U V] :=
  finProdFinEquiv.trans (finCongr (rightRank_tensorProduct U V).symm)

/-- Product source coordinates, followed by the multiplicative left-rank
identification for an independent tensor product.

Formalization infrastructure for the tensoring clause of Theorem `IndexTh`
(ii), which arXiv:1703.09188 calls trivial in lines 824--847. -/
noncomputable def tensorProductLeftRankEquiv
    {d D e E : ℕ} (U : MPOTensor d D) (V : MPOTensor e E) :
    Fin ℓ[U] × Fin ℓ[V] ≃ Fin ℓ[tensorProduct U V] :=
  finProdFinEquiv.trans (finCongr (leftRank_tensorProduct U V).symm)

private theorem tensorProductCutShuffle_symm_apply
    (a b c f : ℕ) (x : Fin a × Fin b) (y : Fin c × Fin f) :
    (tensorProductCutShuffle a b c f).symm
        (finProdFinEquiv (x.1, y.1), finProdFinEquiv (x.2, y.2)) = (x, y) :=
  (tensorProductCutShuffle a b c f).symm_apply_apply (x, y)

/-- Supplied source factors are multiplicative under the independent tensor
product when both source weights are identities.

Formalization infrastructure for the tensoring clause of Theorem `IndexTh`
(ii), which arXiv:1703.09188 calls trivial in lines 824--847. -/
noncomputable def SourceFactors.independentTensorProductOfIdentityWeight
    {d D e E : ℕ} {U : MPOTensor d D} {V : MPOTensor e E}
    (S : SourceFactors U (1 : Matrix (Fin D) (Fin D) ℂ))
    (T : SourceFactors V (1 : Matrix (Fin E) (Fin E) ℂ)) :
    SourceFactors (tensorProduct U V)
      (1 : Matrix (Fin (D * E)) (Fin (D * E)) ℂ) := by
  let eRow := tensorProductCutShuffle D d E e
  let eCol := tensorProductCutShuffle d D e E
  let eR := tensorProductRightRankEquiv U V
  let eL := tensorProductLeftRankEquiv U V
  let X₁ := Matrix.reindex eRow eR (S.X₁ ⊗ₖ T.X₁)
  let Y₁ := Matrix.reindex eR eCol (S.Y₁ ⊗ₖ T.Y₁)
  let Z₁ := Matrix.reindex eCol eR (S.Z₁ ⊗ₖ T.Z₁)
  let X₂ := Matrix.reindex eRow eL (S.X₂ ⊗ₖ T.X₂)
  let Y₂ := Matrix.reindex eL eCol (S.Y₂ ⊗ₖ T.Y₂)
  let Z₂ := Matrix.reindex eCol eL (S.Z₂ ⊗ₖ T.Z₂)
  have hSX₁ : S.X₁.IsIsometry := by
    have h := S.X₁_weighted_isometry
    rw [show sourceWeight (d := d) (1 : Matrix (Fin D) (Fin D) ℂ) = 1 by
      simp [sourceWeight]] at h
    simpa [Matrix.IsIsometry] using h
  have hTX₁ : T.X₁.IsIsometry := by
    have h := T.X₁_weighted_isometry
    rw [show sourceWeight (d := e) (1 : Matrix (Fin E) (Fin E) ℂ) = 1 by
      simp [sourceWeight]] at h
    simpa [Matrix.IsIsometry] using h
  have hKX₁ : (S.X₁ ⊗ₖ T.X₁).IsIsometry :=
    Matrix.IsIsometry.kronecker S.X₁ T.X₁ hSX₁ hTX₁
  have hKX₂ : (S.X₂ ⊗ₖ T.X₂).IsIsometry :=
    Matrix.IsIsometry.kronecker S.X₂ T.X₂ S.X₂_isometry T.X₂_isometry
  have hX₁ : X₁.IsIsometry :=
    Matrix.IsIsometry.reindex _ hKX₁ eRow eR
  have hX₂ : X₂.IsIsometry :=
    Matrix.IsIsometry.reindex _ hKX₂ eRow eL
  have hcut₁ : sourceCutM₁ (tensorProduct U V) = X₁ * Y₁ := by
    rw [sourceCutM₁_tensorProduct, S.sourceCutM₁_eq, T.sourceCutM₁_eq]
    change Matrix.reindex eRow eCol
        ((S.X₁ * S.Y₁) ⊗ₖ (T.X₁ * T.Y₁)) =
      Matrix.reindex eRow eR (S.X₁ ⊗ₖ T.X₁) *
        Matrix.reindex eR eCol (S.Y₁ ⊗ₖ T.Y₁)
    rw [Matrix.reindex_mul_reindex, Matrix.mul_kronecker_mul]
  have hcut₂ : sourceCutM₂ (tensorProduct U V) = X₂ * Y₂ := by
    rw [sourceCutM₂_tensorProduct, S.sourceCutM₂_eq, T.sourceCutM₂_eq]
    change Matrix.reindex eRow eCol
        ((S.X₂ * S.Y₂) ⊗ₖ (T.X₂ * T.Y₂)) =
      Matrix.reindex eRow eL (S.X₂ ⊗ₖ T.X₂) *
        Matrix.reindex eL eCol (S.Y₂ ⊗ₖ T.Y₂)
    rw [Matrix.reindex_mul_reindex, Matrix.mul_kronecker_mul]
  have hweighted : X₁ᴴ * sourceWeight (d := d * e)
      (1 : Matrix (Fin (D * E)) (Fin (D * E)) ℂ) * X₁ = 1 := by
    rw [show sourceWeight (d := d * e)
        (1 : Matrix (Fin (D * E)) (Fin (D * E)) ℂ) = 1 by
      simp [sourceWeight]]
    simpa [Matrix.IsIsometry] using hX₁
  have hY₁Z₁ : Y₁ * Z₁ = 1 := by
    change Matrix.reindex eR eCol (S.Y₁ ⊗ₖ T.Y₁) *
      Matrix.reindex eCol eR (S.Z₁ ⊗ₖ T.Z₁) = 1
    rw [Matrix.reindex_mul_reindex, ← Matrix.mul_kronecker_mul,
      S.Y₁_mul_Z₁, T.Y₁_mul_Z₁]
    simp
  have hY₂Z₂ : Y₂ * Z₂ = 1 := by
    change Matrix.reindex eL eCol (S.Y₂ ⊗ₖ T.Y₂) *
      Matrix.reindex eCol eL (S.Z₂ ⊗ₖ T.Z₂) = 1
    rw [Matrix.reindex_mul_reindex, ← Matrix.mul_kronecker_mul,
      S.Y₂_mul_Z₂, T.Y₂_mul_Z₂]
    simp
  exact ⟨X₁, Y₁, Z₁, X₂, Y₂, Z₂, hcut₁, hcut₂,
    hweighted, hX₂, hY₁Z₁, hY₂Z₂⟩

/-- The supplied source $u$ of an independent tensor product is the product
of the two constituent source entries in the product rank coordinates.

Formalization infrastructure for the tensoring clause of Theorem `IndexTh`
(ii), which arXiv:1703.09188 calls trivial in lines 824--847. -/
theorem SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply
    {d D e E : ℕ} {U : MPOTensor d D} {V : MPOTensor e E}
    (S : SourceFactors U (1 : Matrix (Fin D) (Fin D) ℂ))
    (T : SourceFactors V (1 : Matrix (Fin E) (Fin E) ℂ))
    (lᵤ : Fin ℓ[U]) (lᵥ : Fin ℓ[V]) (rᵤ : Fin r[U]) (rᵥ : Fin r[V])
    (i₁ i₂ : Fin d) (j₁ j₂ : Fin e) :
    SourceFactors.sourceU (tensorProduct U V)
        (SourceFactors.independentTensorProductOfIdentityWeight S T)
        (tensorProductLeftRankEquiv U V (lᵤ, lᵥ),
          tensorProductRightRankEquiv U V (rᵤ, rᵥ))
        (finProdFinEquiv (i₁, j₁), finProdFinEquiv (i₂, j₂)) =
      SourceFactors.sourceU U S (lᵤ, rᵤ) (i₁, i₂) *
        SourceFactors.sourceU V T (lᵥ, rᵥ) (j₁, j₂) := by
  simp only [SourceFactors.sourceU,
    SourceFactors.independentTensorProductOfIdentityWeight]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [tensorProductCutShuffle_symm_apply d D e E (i₁, β) (j₁, γ),
    tensorProductCutShuffle_symm_apply D d E e (β, i₂) (γ, j₂)]
  ring

/-- The supplied source $v$ of an independent tensor product is the product
of the two constituent source entries in the product rank coordinates.

Formalization infrastructure for the tensoring clause of Theorem `IndexTh`
(ii), which arXiv:1703.09188 calls trivial in lines 824--847. -/
theorem SourceFactors.sourceV_independentTensorProductOfIdentityWeight_apply
    {d D e E : ℕ} {U : MPOTensor d D} {V : MPOTensor e E}
    (S : SourceFactors U (1 : Matrix (Fin D) (Fin D) ℂ))
    (T : SourceFactors V (1 : Matrix (Fin E) (Fin E) ℂ))
    (j₁ j₂ : Fin d) (k₁ k₂ : Fin e)
    (rᵤ : Fin r[U]) (rᵥ : Fin r[V]) (lᵤ : Fin ℓ[U]) (lᵥ : Fin ℓ[V]) :
    SourceFactors.sourceV (tensorProduct U V)
        (SourceFactors.independentTensorProductOfIdentityWeight S T)
        (finProdFinEquiv (j₁, k₁), finProdFinEquiv (j₂, k₂))
        (tensorProductRightRankEquiv U V (rᵤ, rᵥ),
          tensorProductLeftRankEquiv U V (lᵤ, lᵥ)) =
      SourceFactors.sourceV U S (j₁, j₂) (rᵤ, lᵤ) *
        SourceFactors.sourceV V T (k₁, k₂) (rᵥ, lᵥ) := by
  simp only [SourceFactors.sourceV,
    SourceFactors.independentTensorProductOfIdentityWeight]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [tensorProductCutShuffle_symm_apply D d E e (α, j₁) (γ, k₁),
    tensorProductCutShuffle_symm_apply d D e E (j₂, α) (k₂, γ)]
  ring

end MPOTensor
