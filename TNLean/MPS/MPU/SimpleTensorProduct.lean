/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Simple
import TNLean.MPS.MPU.SourceIndexValue
import TNLean.MPS.MPU.TensorProduct

/-!
# Simplicity of independent tensor products of matrix product unitaries

The proof of part (ii) of the Index Theorem of arXiv:1703.09188 disposes of
tensor products with the sentence "The case of tensoring is trivial"
(`Papers/1703.09188/paper_v2.tex`, lines 835--836). Computing the index of
$\mathcal U\otimes\mathcal V$ at a simple blocking uses that the tensor product of
two simple tensors (Definition III.2, lines 363--374) is again simple. This file
proves that step, with no hypothesis beyond the simplicity of the two factors,
together with the additivity of the source-index expression of a specified tensor
under tensor products.

The double layer of $\mathcal U\otimes\mathcal V$ is, up to a shuffle of its bond
indices, the Kronecker product of the two double layers. The boundary vectors
of the product are the products $a\otimes a'$ and $b\otimes b'$ of the boundary
vectors of the factors.

## Main definitions

* `MPOTensor.doubleLayerTensorProductShuffle`: the bond shuffle
  $((\alpha,\alpha'),(\gamma,\gamma'))\mapsto((\alpha,\gamma),(\alpha',\gamma'))$.

## Main results

* `MPOTensor.doubleLayerTensor_tensorProduct`: the double layer of a tensor product
  is the shuffled Kronecker product of the double layers.
* `MPOTensor.IsMPUSimple.tensorProduct`: tensor products of simple tensors are simple.
* `MPOTensor.sourceIndexValue_tensorProduct`: the source-index expression is additive
  under tensor products.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, "Matrix Product Unitaries:
  Structure, Symmetries, and Topological Invariants", arXiv:1703.09188,
  Definition III.2 and Theorem `IndexTh`.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

variable {d D e E : ℕ}

/-- The bond shuffle relating the Kronecker product of two double-layer bond spaces
to the double-layer bond space of a tensor product:
$((\alpha,\alpha'),(\gamma,\gamma'))\mapsto((\alpha,\gamma),(\alpha',\gamma'))$,
each pair encoded by `finProdFinEquiv`. -/
def doubleLayerTensorProductShuffle (D E : ℕ) :
    Fin (D * D) × Fin (E * E) ≃ Fin ((D * E) * (D * E)) :=
  (finProdFinEquiv.symm.prodCongr finProdFinEquiv.symm).trans
    ((tensorProductCutShuffle D D E E).trans finProdFinEquiv)

@[simp] theorem doubleLayerTensorProductShuffle_apply (α α' : Fin D) (γ γ' : Fin E) :
    doubleLayerTensorProductShuffle D E (finProdFinEquiv (α, α'), finProdFinEquiv (γ, γ')) =
      finProdFinEquiv (finProdFinEquiv (α, γ), finProdFinEquiv (α', γ')) := by
  simp [doubleLayerTensorProductShuffle, tensorProductCutShuffle]

/-- The double layer of an independent tensor product is the Kronecker product of
the two double layers, after the bond shuffle
`doubleLayerTensorProductShuffle`.

Bridge: relates the double layer of Definition III.2 of arXiv:1703.09188,
lines 363--374, to the tensoring operation in the proof of Theorem `IndexTh` (ii),
lines 835--836. -/
theorem doubleLayerTensor_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E)
    (i j : Fin d) (k l : Fin e) :
    doubleLayerTensor (tensorProduct U V) (finProdFinEquiv (i, k))
        (finProdFinEquiv (j, l)) =
      Matrix.reindex (doubleLayerTensorProductShuffle D E)
        (doubleLayerTensorProductShuffle D E)
        (doubleLayerTensor U i j ⊗ₖ doubleLayerTensor V k l) := by
  ext x y
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ := (doubleLayerTensorProductShuffle D E).surjective x
  obtain ⟨⟨y₁, y₂⟩, rfl⟩ := (doubleLayerTensorProductShuffle D E).surjective y
  obtain ⟨⟨α, α'⟩, rfl⟩ := finProdFinEquiv.surjective x₁
  obtain ⟨⟨γ, γ'⟩, rfl⟩ := finProdFinEquiv.surjective x₂
  obtain ⟨⟨β, β'⟩, rfl⟩ := finProdFinEquiv.surjective y₁
  obtain ⟨⟨δ, δ'⟩, rfl⟩ := finProdFinEquiv.surjective y₂
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, doubleLayerTensorProductShuffle_apply,
    doubleLayerTensorProductShuffle_apply]
  simp only [doubleLayerTensor_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply, physicalAdjointTensor_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp only [tensorProduct_apply]
  refine Finset.sum_congr rfl fun m₁ _ ↦ Finset.sum_congr rfl fun m₂ _ ↦ ?_
  rw [star_mul']
  ring

/-- The contraction $(a|M|b)$ is the trace of $M$ against the rank-one operator
$|b)(a|$. -/
private theorem dotProduct_mulVec_eq_trace {n : Type*} [Fintype n]
    (a b : n → ℂ) (M : Matrix n n ℂ) :
    a ⬝ᵥ (M *ᵥ b) = trace (M * vecMulVec b a) := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- The rank-one operator built from product boundary vectors is the shuffled
Kronecker product of the two rank-one operators. -/
private theorem vecMulVec_shuffle (a b : Fin (D * D) → ℂ) (a' b' : Fin (E * E) → ℂ) :
    vecMulVec
        (fun z ↦ b ((doubleLayerTensorProductShuffle D E).symm z).1 *
          b' ((doubleLayerTensorProductShuffle D E).symm z).2)
        (fun z ↦ a ((doubleLayerTensorProductShuffle D E).symm z).1 *
          a' ((doubleLayerTensorProductShuffle D E).symm z).2) =
      Matrix.reindex (doubleLayerTensorProductShuffle D E)
        (doubleLayerTensorProductShuffle D E) (vecMulVec b a ⊗ₖ vecMulVec b' a') := by
  ext z w
  simp only [vecMulVec_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  ring

/-- The independent tensor product of two simple tensors is simple. The boundary
vectors are the products $a\otimes a'$ and $b\otimes b'$ of those of the factors,
and both identities `simple1` and `simple2` factor through the Kronecker product
of the double layers.

Source: arXiv:1703.09188, Definition III.2, lines 363--374; this is the step
behind "The case of tensoring is trivial" in the proof of Theorem `IndexTh` (ii),
lines 835--836. -/
theorem IsMPUSimple.tensorProduct {U : MPOTensor d D} {V : MPOTensor e E}
    (hU : IsMPUSimple U) (hV : IsMPUSimple V) :
    IsMPUSimple (MPOTensor.tensorProduct U V) := by
  obtain ⟨a, b, ha, hb⟩ := hU
  obtain ⟨a', b', ha', hb'⟩ := hV
  set σ := doubleLayerTensorProductShuffle D E
  have hR := vecMulVec_shuffle a b a' b'
  refine ⟨fun z ↦ a (σ.symm z).1 * a' (σ.symm z).2,
    fun z ↦ b (σ.symm z).1 * b' (σ.symm z).2, fun I J ↦ ?_, fun I J K L ↦ ?_⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective I
    obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective J
    rw [dotProduct_mulVec_eq_trace, doubleLayerTensor_tensorProduct, hR,
      ← Matrix.coe_reindexRingEquiv ℂ σ, ← map_mul, ← Matrix.mul_kronecker_mul,
      Matrix.coe_reindexRingEquiv, Matrix.trace_reindex, Matrix.trace_kronecker,
      ← dotProduct_mulVec_eq_trace, ← dotProduct_mulVec_eq_trace, ha, ha']
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
    split_ifs <;> simp_all
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective I
    obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective J
    obtain ⟨⟨i', k'⟩, rfl⟩ := finProdFinEquiv.surjective K
    obtain ⟨⟨j', l'⟩, rfl⟩ := finProdFinEquiv.surjective L
    rw [doubleLayerTensor_tensorProduct, doubleLayerTensor_tensorProduct, hR,
      ← Matrix.coe_reindexRingEquiv ℂ σ, ← map_mul, ← map_mul, ← map_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← hb, ← hb']

/-- The source-index value of an independent tensor product is the sum of the
source-index values of the factors, since both source ranks are multiplicative.

This is the specified-tensor part of "The case of tensoring is trivial" in the
proof of arXiv:1703.09188, Theorem `IndexTh` (ii), lines 835--836.

**Scope restriction (specified tensors):** the identity is for the displayed
tensors, not the public blocking-independent index of Definition IV.1; documented
in `docs/paper-gaps/mpu_shift_specified_tensor_index_scope.tex`. -/
theorem sourceIndexValue_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E)
    (hrU : 0 < r[U]) (hℓU : 0 < ℓ[U]) (hrV : 0 < r[V]) (hℓV : 0 < ℓ[V]) :
    sourceIndexValue (MPOTensor.tensorProduct U V)
        (rightRank_tensorProduct U V ▸ Nat.mul_pos hrU hrV)
        (leftRank_tensorProduct U V ▸ Nat.mul_pos hℓU hℓV) =
      sourceIndexValue U hrU hℓU + sourceIndexValue V hrV hℓV :=
  sourceIndexValue_eq_add_of_common_rank_product U V _ 1 one_pos hrU hℓU hrV hℓV _ _
    (by rw [rightRank_tensorProduct, one_mul]) (by rw [leftRank_tensorProduct, one_mul])

end MPOTensor
