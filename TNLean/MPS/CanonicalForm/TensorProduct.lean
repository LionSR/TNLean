/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Core.TensorProductSpan

/-!
# Independent tensor products of CPSV canonical-form-II data

This module packages the tensor-product argument for the retained blocks of
the CPSV canonical-form-II decomposition.  The product of two retained blocks
is left-canonical by a direct Kronecker calculation, algebraically normal by
the common homogeneous word-span length, and hence a CPSV normal tensor by the
established left-canonical bridge.  The diagonal positive fixed point is the
reindexed Kronecker product of the two fixed points.

The result is project infrastructure for the tensoring clause in
arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845; it is not a
separately stated theorem of that paper.  The retained-normal-block terminology
comes from arXiv:1606.00608, equation `II_CF1`, lines 214--245.  The two
left-canonical identities are explicit project hypotheses, not an additional
claim attributed to that passage.

## Main statement

* `MPSTensor.IsNormalTensor.tensorProduct_of_leftCanonical` preserves CPSV
  normality for two left-canonical normal blocks;
  `MPSTensor.leftCanonical_tensorProduct`
  supplies the accompanying left-canonical conclusion.
* `MPSTensor.transferMap_tensorProduct_kronecker` identifies the product
  transfer map on a reindexed Kronecker product.

## References

* Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Unitaries:
  Structure, Symmetries, and Topological Invariants*, arXiv:1703.09188.
* Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPSTensor

variable {d D e E : ℕ}

/-- The independent tensor product of two left-canonical CPSV normal blocks is
again a CPSV normal tensor.  Its left-canonicality is the conclusion of
`MPSTensor.leftCanonical_tensorProduct`.

For normal blocks `A` and `B`, algebraic normality follows at the common
homogeneous word length `N_A N_B`, while the two identities
\[
  \sum_i (A^i)^\dagger A^i=\mathbf 1_D,
  \qquad
  \sum_k (B^k)^\dagger B^k=\mathbf 1_E
\]
give left-canonicality of `A \boxtimes B`.  The theorem then applies
`MPSTensor.isNormalTensor_of_isNormal_leftCanonical`.

This is infrastructure for arXiv:1703.09188, proof of Theorem `IndexTh` (ii),
lines 824--845, not a separate result asserted there.  The normal-block and
left-canonical hypotheses are the project inputs for the retained
canonical-form blocks described around arXiv:1606.00608, equation `II_CF1`,
lines 214--245; the passage itself is not cited as asserting left-canonicality.
-/
theorem IsNormalTensor.tensorProduct_of_leftCanonical {A : MPSTensor d D}
    (hA : IsNormalTensor A)
    {B : MPSTensor e E} (hB : IsNormalTensor B)
    (hLeftA : IsLeftCanonical A) (hLeftB : IsLeftCanonical B) :
    IsNormalTensor (MPSTensor.tensorProduct A B) := by
  let _ : NeZero (D * E) :=
    ⟨Nat.mul_ne_zero hA.bondDim_ne_zero hB.bondDim_ne_zero⟩
  exact isNormalTensor_of_isNormal_leftCanonical (MPSTensor.tensorProduct A B)
    (isNormal_tensorProduct A B hA.isNormal hB.isNormal)
    (leftCanonical_tensorProduct A B hLeftA hLeftB)

/-- The transfer map of an independent tensor product acts on a reindexed
Kronecker product as the reindexed Kronecker product of the two transfer maps:
\[
  \mathcal E_{A\boxtimes B}(\operatorname{reind}(X\otimes Y))
  =\operatorname{reind}(\mathcal E_A(X)\otimes\mathcal E_B(Y)).
\]

This is the algebraic identity used for the diagonal positive fixed points in
the product canonical-form-II construction.  Its terminology and fixed-point
orientation are those of arXiv:1606.00608, Appendix A, equations `TP` and
`Lambda`, lines 1054--1077. -/
theorem transferMap_tensorProduct_kronecker (A : MPSTensor d D)
    (B : MPSTensor e E) (X : Matrix (Fin D) (Fin D) ℂ)
    (Y : Matrix (Fin E) (Fin E) ℂ) :
    Kraus.transferMap (tensorProduct A B)
        (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Kraus.transferMap A X ⊗ₖ Kraus.transferMap B Y) := by
  classical
  have hterm (i : Fin d) (k : Fin e) :
      tensorProduct A B (finProdFinEquiv (i, k)) *
            Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y) *
            (tensorProduct A B (finProdFinEquiv (i, k)))ᴴ =
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          ((A i * X * (A i)ᴴ) ⊗ₖ (B k * Y * (B k)ᴴ)) := by
    have hi : (finProdFinEquiv (i, k) : Fin (d * e)).divNat = i :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, k))
    have hk : (finProdFinEquiv (i, k) : Fin (d * e)).modNat = k :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, k))
    simp only [tensorProduct, hi, hk]
    rw [Matrix.conjTranspose_reindex]
    change
      (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (A i ⊗ₖ B k) *
          Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) *
          Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
            ((A i ⊗ₖ B k)ᴴ) = _
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv finProdFinEquiv
        finProdFinEquiv,
      Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv finProdFinEquiv
        finProdFinEquiv,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    rfl
  rw [Kraus.transferMap_apply, ← Equiv.sum_comp finProdFinEquiv,
    Fintype.sum_prod_type]
  simp_rw [hterm]
  change
    ∑ i : Fin d, ∑ k : Fin e,
        Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          ((A i * X * (A i)ᴴ) ⊗ₖ (B k * Y * (B k)ᴴ)) =
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
        (Kraus.transferMap A X ⊗ₖ Kraus.transferMap B Y)
  apply (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv).symm.injective
  simp only [map_sum, LinearEquiv.symm_apply_apply]
  rw [Kraus.transferMap_apply, Kraus.transferMap_apply]
  symm
  change Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)
      (∑ i : Fin d, A i * X * (A i)ᴴ)
      (∑ k : Fin e, B k * Y * (B k)ᴴ) = _
  rw [map_sum]
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  simp only [LinearMap.sum_apply]
  rfl

namespace CPSVCanonicalFormIIData

variable {A : MPSTensor d D} {B : MPSTensor e E}

/-- Combine heterogeneous equalities coordinatewise. -/
private theorem prod_heq {α β γ δ : Type} {a : α} {b : β} {c : γ} {d : δ}
    (hac : a ≍ c) (hbd : b ≍ d) : (a, b) ≍ (c, d) := by
  cases hac
  cases hbd
  rfl

/-- Regroup a pair of dependent coordinates as one dependent coordinate over
the product label. -/
private def sigmaProdFiberEquiv {α β : Type*} (γ : α → Type*) (δ : β → Type*) :
    (Sigma γ × Sigma δ) ≃ Σ ab : α × β, γ ab.1 × δ ab.2 where
  toFun x := ⟨(x.1.1, x.2.1), (x.1.2, x.2.2)⟩
  invFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Bond dimension of the retained product block labelled by `ab`. -/
private def tensorProductDim (dataA : CPSVCanonicalFormIIData A)
    (dataB : CPSVCanonicalFormIIData B) (ab : Fin (dataA.r * dataB.r)) : ℕ :=
  dataA.dim (finProdFinEquiv.symm ab).1 * dataB.dim (finProdFinEquiv.symm ab).2

/-- Weight of the retained product block labelled by `ab`. -/
private def tensorProductWeight (dataA : CPSVCanonicalFormIIData A)
    (dataB : CPSVCanonicalFormIIData B) (ab : Fin (dataA.r * dataB.r)) : ℂ :=
  dataA.weights (finProdFinEquiv.symm ab).1 *
    dataB.weights (finProdFinEquiv.symm ab).2

/-- Retained product block labelled by `ab`. -/
private def tensorProductBlock (dataA : CPSVCanonicalFormIIData A)
    (dataB : CPSVCanonicalFormIIData B) (ab : Fin (dataA.r * dataB.r)) :
    MPSTensor (d * e) (tensorProductDim dataA dataB ab) :=
  MPSTensor.tensorProduct
    (dataA.blocks (finProdFinEquiv.symm ab).1)
    (dataB.blocks (finProdFinEquiv.symm ab).2)

/-- Product-coordinate equivalence for the fiber over the retained label `(a,b)`. -/
private noncomputable def tensorProductFiberEquiv
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B)
    (a : Fin dataA.r) (b : Fin dataB.r) :
    (Fin (dataA.dim a) × Fin (dataB.dim b)) ≃
      Fin (tensorProductDim dataA dataB (finProdFinEquiv (a, b))) :=
  finProdFinEquiv |>.trans (finCongr (by simp [tensorProductDim]))

/-- Canonical retained-coordinate regrouping
`((a, α), (b, β)) ↦ ((a, b), (α, β))` for the product block family. -/
private noncomputable def tensorProductRetainedEquiv
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B) :
    (Fin (∑ a : Fin dataA.r, dataA.dim a) ×
        Fin (∑ b : Fin dataB.r, dataB.dim b)) ≃
      Fin (∑ ab : Fin (dataA.r * dataB.r), tensorProductDim dataA dataB ab) :=
  (Equiv.prodCongr
      (finSigmaFinEquiv (m := dataA.r) (n := dataA.dim)).symm
      (finSigmaFinEquiv (m := dataB.r) (n := dataB.dim)).symm) |>.trans
    (sigmaProdFiberEquiv (fun a ↦ Fin (dataA.dim a))
      (fun b ↦ Fin (dataB.dim b))) |>.trans
    (Equiv.sigmaCongr finProdFinEquiv fun ab ↦
      tensorProductFiberEquiv dataA dataB ab.1 ab.2) |>.trans
    finSigmaFinEquiv

@[simp]
private theorem tensorProductRetainedEquiv_apply
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B)
    (a : Fin dataA.r) (b : Fin dataB.r)
    (α : Fin (dataA.dim a)) (β : Fin (dataB.dim b)) :
    tensorProductRetainedEquiv dataA dataB
        (finSigmaFinEquiv ⟨a, α⟩, finSigmaFinEquiv ⟨b, β⟩) =
      finSigmaFinEquiv
        ⟨finProdFinEquiv (a, b), tensorProductFiberEquiv dataA dataB a b (α, β)⟩ := by
  apply finSigmaFinEquiv.symm.injective
  simp only [tensorProductRetainedEquiv, Equiv.sigmaCongr, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaCongrLeft_apply, sigmaProdFiberEquiv,
    Equiv.coe_fn_mk]

@[simp]
private theorem tensorProductBlock_apply
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B)
    (a : Fin dataA.r) (b : Fin dataB.r) (i : Fin d) (k : Fin e)
    (α γ : Fin (dataA.dim a)) (β δ : Fin (dataB.dim b)) :
    tensorProductBlock dataA dataB (finProdFinEquiv (a, b))
        (finProdFinEquiv (i, k)) (tensorProductFiberEquiv dataA dataB a b (α, β))
        (tensorProductFiberEquiv dataA dataB a b (γ, δ)) =
      dataA.blocks a i α γ * dataB.blocks b k β δ := by
  let coord (p : Fin dataA.r × Fin dataB.r) :=
    Fin (dataA.dim p.1 * dataB.dim p.2)
  let entry (z : Σ p, coord p × coord p) : ℂ :=
    MPSTensor.tensorProduct (dataA.blocks z.1.1) (dataB.blocks z.1.2)
      (finProdFinEquiv (i, k)) z.2.1 z.2.2
  have hz :
      (⟨finProdFinEquiv.symm (finProdFinEquiv (a, b)),
          (tensorProductFiberEquiv dataA dataB a b (α, β),
            tensorProductFiberEquiv dataA dataB a b (γ, δ))⟩ :
        Σ p, coord p × coord p) =
      ⟨(a, b), (finProdFinEquiv (α, β), finProdFinEquiv (γ, δ))⟩ := by
    apply Sigma.ext (finProdFinEquiv.symm_apply_apply (a, b))
    have hαβ :
        tensorProductFiberEquiv dataA dataB a b (α, β) ≍ finProdFinEquiv (α, β) := by
      simp only [tensorProductFiberEquiv, Equiv.trans_apply, finCongr_apply]
      rw [Fin.cast_eq_cast]
      exact cast_heq _ _
    have hγδ :
        tensorProductFiberEquiv dataA dataB a b (γ, δ) ≍ finProdFinEquiv (γ, δ) := by
      simp only [tensorProductFiberEquiv, Equiv.trans_apply, finCongr_apply]
      rw [Fin.cast_eq_cast]
      exact cast_heq _ _
    exact prod_heq hαβ hγδ
  calc
    _ = entry
        ⟨finProdFinEquiv.symm (finProdFinEquiv (a, b)),
          (tensorProductFiberEquiv dataA dataB a b (α, β),
            tensorProductFiberEquiv dataA dataB a b (γ, δ))⟩ := rfl
    _ = entry ⟨(a, b), (finProdFinEquiv (α, β), finProdFinEquiv (γ, δ))⟩ :=
      congrArg entry hz
    _ = _ := MPSTensor.tensorProduct_apply (dataA.blocks a) (dataB.blocks b)
      i k α γ β δ

/-- The weighted direct sum of the product blocks is the retained-coordinate
reindexing of the Kronecker product of the two weighted direct sums. -/
private theorem toTensorFromBlocks_tensorProduct
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B)
    (i : Fin d) (k : Fin e) :
    toTensorFromBlocks (tensorProductWeight dataA dataB)
        (tensorProductBlock dataA dataB) (finProdFinEquiv (i, k)) =
      Matrix.reindex (tensorProductRetainedEquiv dataA dataB)
        (tensorProductRetainedEquiv dataA dataB)
        (toTensorFromBlocks dataA.weights dataA.blocks i ⊗ₖ
          toTensorFromBlocks dataB.weights dataB.blocks k) := by
  classical
  ext x y
  rcases (tensorProductRetainedEquiv dataA dataB).surjective x with
    ⟨⟨xa, xb⟩, rfl⟩
  rcases (tensorProductRetainedEquiv dataA dataB).surjective y with
    ⟨⟨ya, yb⟩, rfl⟩
  rcases finSigmaFinEquiv.surjective xa with ⟨⟨a, α⟩, rfl⟩
  rcases finSigmaFinEquiv.surjective xb with ⟨⟨b, β⟩, rfl⟩
  rcases finSigmaFinEquiv.surjective ya with ⟨⟨c, γ⟩, rfl⟩
  rcases finSigmaFinEquiv.surjective yb with ⟨⟨f, δ⟩, rfl⟩
  simp only [toTensorFromBlocks, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  simp only [Equiv.symm_apply_apply]
  rw [tensorProductRetainedEquiv_apply, tensorProductRetainedEquiv_apply]
  simp only [finSigmaFinEquiv.symm_apply_apply]
  by_cases hac : a = c
  · subst c
    by_cases hbf : b = f
    · subst f
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq,
        Matrix.blockDiagonal'_apply_eq]
      simp only [tensorProductWeight, Equiv.symm_apply_apply, Matrix.smul_apply,
        tensorProductBlock_apply, smul_eq_mul]
      ring
    · have hab : finProdFinEquiv (a, b) ≠ finProdFinEquiv (a, f) := by
        exact fun h ↦ hbf (congrArg Prod.snd (finProdFinEquiv.injective h))
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab,
        Matrix.blockDiagonal'_apply_ne _ _ _ hbf]
      simp
  · have hab : finProdFinEquiv (a, b) ≠ finProdFinEquiv (c, f) := by
      exact fun h ↦ hac (congrArg Prod.fst (finProdFinEquiv.injective h))
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab,
      Matrix.blockDiagonal'_apply_ne _ _ _ hac]
    simp

/-- Reindexed Kronecker product of the two ambient coisometries. -/
private noncomputable def tensorProductAmbientCoisometry
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B) :
    Matrix
      (Fin (∑ ab : Fin (dataA.r * dataB.r), tensorProductDim dataA dataB ab))
      (Fin (D * E)) ℂ :=
  Matrix.reindex (tensorProductRetainedEquiv dataA dataB) finProdFinEquiv
    (dataA.ambient_coisometry ⊗ₖ dataB.ambient_coisometry)

private theorem tensorProductAmbientCoisometry_coisometric
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B) :
    tensorProductAmbientCoisometry dataA dataB *
        (tensorProductAmbientCoisometry dataA dataB)ᴴ = 1 := by
  rw [tensorProductAmbientCoisometry, Matrix.conjTranspose_reindex]
  change
    Matrix.reindexLinearEquiv ℂ ℂ (tensorProductRetainedEquiv dataA dataB)
        finProdFinEquiv (dataA.ambient_coisometry ⊗ₖ dataB.ambient_coisometry) *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv
        (tensorProductRetainedEquiv dataA dataB)
        ((dataA.ambient_coisometry ⊗ₖ dataB.ambient_coisometry)ᴴ) = 1
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (tensorProductRetainedEquiv dataA dataB)
      finProdFinEquiv (tensorProductRetainedEquiv dataA dataB),
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    dataA.coisometric, dataB.coisometric, Matrix.one_kronecker_one,
    Matrix.reindexLinearEquiv_one]

private theorem sum_tensorProductDim
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B) :
    (∑ ab : Fin (dataA.r * dataB.r), tensorProductDim dataA dataB ab) =
      (∑ a : Fin dataA.r, dataA.dim a) *
        (∑ b : Fin dataB.r, dataB.dim b) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [tensorProductDim, Equiv.symm_apply_apply]
  rw [← Fintype.sum_mul_sum]

private theorem tensorProduct_reconstruct
    (dataA : CPSVCanonicalFormIIData A) (dataB : CPSVCanonicalFormIIData B)
    (q : Fin (d * e)) :
    MPSTensor.tensorProduct A B q =
      (tensorProductAmbientCoisometry dataA dataB)ᴴ *
        toTensorFromBlocks (tensorProductWeight dataA dataB)
          (tensorProductBlock dataA dataB) q *
        tensorProductAmbientCoisometry dataA dataB := by
  rcases finProdFinEquiv.surjective q with ⟨⟨i, k⟩, rfl⟩
  rw [toTensorFromBlocks_tensorProduct]
  have hi : (finProdFinEquiv (i, k) : Fin (d * e)).divNat = i :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, k))
  have hk : (finProdFinEquiv (i, k) : Fin (d * e)).modNat = k :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, k))
  simp only [MPSTensor.tensorProduct, hi, hk]
  rw [dataA.reconstruct i, dataB.reconstruct k]
  rw [tensorProductAmbientCoisometry, Matrix.conjTranspose_reindex]
  change
    Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
        (((dataA.ambient_coisometryᴴ *
              toTensorFromBlocks dataA.weights dataA.blocks i) *
            dataA.ambient_coisometry) ⊗ₖ
          ((dataB.ambient_coisometryᴴ *
              toTensorFromBlocks dataB.weights dataB.blocks k) *
            dataB.ambient_coisometry)) =
      (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv
          (tensorProductRetainedEquiv dataA dataB)
          ((dataA.ambient_coisometry ⊗ₖ dataB.ambient_coisometry)ᴴ) *
        Matrix.reindexLinearEquiv ℂ ℂ (tensorProductRetainedEquiv dataA dataB)
          (tensorProductRetainedEquiv dataA dataB)
          (toTensorFromBlocks dataA.weights dataA.blocks i ⊗ₖ
            toTensorFromBlocks dataB.weights dataB.blocks k)) *
        Matrix.reindexLinearEquiv ℂ ℂ (tensorProductRetainedEquiv dataA dataB)
          finProdFinEquiv
          (dataA.ambient_coisometry ⊗ₖ dataB.ambient_coisometry)
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv
      (tensorProductRetainedEquiv dataA dataB)
      (tensorProductRetainedEquiv dataA dataB),
    Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv
      (tensorProductRetainedEquiv dataA dataB) finProdFinEquiv]
  rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
    Matrix.mul_kronecker_mul]

/-- Assemble canonical-form-II data for the independent tensor product.

For retained labels `(a,b)`, the construction uses exactly
`D_(a,b) = D_a E_b`, `ω_(a,b) = μ_a ν_b`,
`C_(a,b) = A_a ⊠ B_b`, and
`Λ_(a,b) = reind (Λ_a ⊗ Γ_b)`.  These are the weighted direct-sum and CFII
conditions of arXiv:1606.00608, equation `II_CF1`, lines 214--245, and
Appendix A, equations `TP` and `Lambda`, lines 1054--1077.  The construction
is project infrastructure for the tensoring sentence in arXiv:1703.09188,
proof of Theorem `IndexTh` (ii), lines 824--845; that paper does not state it
as a separate theorem. -/
noncomputable def tensorProduct (dataA : CPSVCanonicalFormIIData A)
    (dataB : CPSVCanonicalFormIIData B) :
    CPSVCanonicalFormIIData (MPSTensor.tensorProduct A B) where
  r := dataA.r * dataB.r
  dim := tensorProductDim dataA dataB
  dim_pos := by
    intro ab
    exact Nat.mul_pos (dataA.dim_pos _) (dataB.dim_pos _)
  weights := tensorProductWeight dataA dataB
  weights_ne_zero := by
    intro ab
    exact mul_ne_zero (dataA.weights_ne_zero _) (dataB.weights_ne_zero _)
  blocks := tensorProductBlock dataA dataB
  blocks_normal := by
    intro ab
    exact (dataA.blocks_normal _).tensorProduct_of_leftCanonical
      (dataB.blocks_normal _) (dataA.blocks_left_canonical _)
      (dataB.blocks_left_canonical _)
  total_dim_le := by
    rw [sum_tensorProductDim]
    exact Nat.mul_le_mul dataA.total_dim_le dataB.total_dim_le
  ambient_coisometry := tensorProductAmbientCoisometry dataA dataB
  coisometric := tensorProductAmbientCoisometry_coisometric dataA dataB
  reconstruct := tensorProduct_reconstruct dataA dataB
  blocks_left_canonical := by
    intro ab
    exact leftCanonical_tensorProduct (dataA.blocks _) (dataB.blocks _)
      (dataA.blocks_left_canonical _) (dataB.blocks_left_canonical _)
  blocks_fixed_point := by
    intro ab
    obtain ⟨Λ, hΛpos, hΛdiag, hΛfix⟩ :=
      dataA.blocks_fixed_point (finProdFinEquiv.symm ab).1
    obtain ⟨Γ, hΓpos, hΓdiag, hΓfix⟩ :=
      dataB.blocks_fixed_point (finProdFinEquiv.symm ab).2
    refine ⟨Matrix.reindex finProdFinEquiv finProdFinEquiv (Λ ⊗ₖ Γ), ?_, ?_, ?_⟩
    · exact (hΛpos.kronecker hΓpos).submatrix finProdFinEquiv.symm.injective
    · exact (hΛdiag.kronecker hΓdiag).submatrix finProdFinEquiv.symm.injective
    · exact
        (transferMap_tensorProduct_kronecker
          (dataA.blocks (finProdFinEquiv.symm ab).1)
          (dataB.blocks (finProdFinEquiv.symm ab).2) Λ Γ).trans
          (by rw [hΛfix, hΓfix])

end CPSVCanonicalFormIIData

end MPSTensor
