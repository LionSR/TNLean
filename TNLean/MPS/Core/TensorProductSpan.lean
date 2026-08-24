/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.MatrixAlgebra
import QICLean.Kraus.Injectivity
import QICLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.Core.TensorProduct

/-!
# Homogeneous word spans of independent tensor products

The length-`N` words of an independent tensor product are exactly the
reindexed Kronecker products of a length-`N` word in each constituent tensor.
Consequently, simultaneous full homogeneous word spans imply a full word span
for the product tensor.  Two eventual full-span witnesses meet at the common
positive length `N_A * N_B`.

This is project infrastructure for the sentence "The case of tensoring is
trivial" in arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845;
the paper does not state a separate normality theorem here.  The tensors to
which this infrastructure is applied are the retained normal blocks of
arXiv:1606.00608, equation `II_CF1`, lines 214--245.

## Main statements

* `MPSTensor.word_span_tensor_product` identifies the product word span with the
  image of the paired constituent spans.
* `MPSTensor.is_n_blk_injective_tensor_product` preserves full homogeneous word
  spans at a common length.
* `MPSTensor.is_normal_tensor_product` preserves algebraic normality by using
  the common length `N_A * N_B`.

## References

* Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Unitaries:
  Structure, Symmetries, and Topological Invariants*, arXiv:1703.09188.
* Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {d D e E : ℕ}

/-- The homogeneous word span of an independent tensor product is the image
of the two constituent homogeneous word spans under the canonical tensor-product
and matrix-reindexing equivalences.

Writing `S_N(A)` for the span of the length-`N` words of `A`, the statement is
\[
  S_N(A\boxtimes B)
  =\operatorname{reind}_{\pi_{D,E}}
    \left(\kappa\bigl(S_N(A)\otimes S_N(B)\bigr)\right),
\]
where `κ` is Mathlib's matrix Kronecker linear equivalence and
`π_{D,E}` is the standard finite-product coordinate bijection.

This is infrastructure for arXiv:1703.09188, proof of Theorem `IndexTh` (ii),
lines 824--845, rather than a separately stated theorem of that paper.  Its
homogeneous-word route supplies the project's algebraic-normality input for
the retained blocks described around arXiv:1606.00608, equation `II_CF1`,
lines 214--245. -/
theorem word_span_tensor_product (A : MPSTensor d D) (B : MPSTensor e E)
    (N : ℕ) :
    Kraus.wordSpan (tensorProduct A B) N =
      Submodule.map
        (((kroneckerLinearEquiv (Fin D) (Fin D) (Fin E) (Fin E) ℂ).trans
          (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv)).toLinearMap)
        (Submodule.map₂
          (TensorProduct.mk ℂ
            (Matrix (Fin D) (Fin D) ℂ)
            (Matrix (Fin E) (Fin E) ℂ))
          (Kraus.wordSpan A N) (Kraus.wordSpan B N)) := by
  unfold Kraus.wordSpan
  rw [Submodule.map_map₂, Submodule.map₂_span_span]
  congr 1
  ext X
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨Kraus.evalWord A (List.ofFn (fun n ↦ (σ n).divNat)), ?_,
      Kraus.evalWord B (List.ofFn (fun n ↦ (σ n).modNat)), ?_, ?_⟩
    · exact ⟨fun n ↦ (σ n).divNat, rfl⟩
    · exact ⟨fun n ↦ (σ n).modNat, rfl⟩
    · change _ = Kraus.evalWord (tensorProduct A B) (List.ofFn σ)
      rw [evalWord_tensorProduct]
      simp only [List.map_ofFn, Function.comp_def]
      rfl
  · rintro ⟨_, ⟨σA, rfl⟩, _, ⟨σB, rfl⟩, rfl⟩
    refine ⟨(finTupleProdEquiv N d e).symm (σA, σB), ?_⟩
    change Kraus.evalWord (tensorProduct A B)
      (List.ofFn ((finTupleProdEquiv N d e).symm (σA, σB))) = _
    rw [evalWord_tensorProduct]
    have hsplit := (finTupleProdEquiv N d e).apply_symm_apply (σA, σB)
    rw [finTupleProdEquiv_apply] at hsplit
    have hσA := congrArg Prod.fst hsplit
    change (fun n ↦ ((finTupleProdEquiv N d e).symm (σA, σB) n).divNat) = σA at hσA
    have hσB := congrArg Prod.snd hsplit
    change (fun n ↦ ((finTupleProdEquiv N d e).symm (σA, σB) n).modNat) = σB at hσB
    simp only [List.map_ofFn, Function.comp_def, hσA, hσB]
    rfl

/-- Full homogeneous word spans at the same length are preserved by an
independent tensor product.

Surjectivity of the composite of `kroneckerLinearEquiv` and
`Matrix.reindexLinearEquiv` sends the full tensor product of the two matrix
spaces onto the full product matrix algebra.  This is the fixed-length step
in the algebraic proof associated with arXiv:1703.09188, Theorem `IndexTh`
(ii), lines 824--845. -/
theorem is_n_blk_injective_tensor_product (A : MPSTensor d D) (B : MPSTensor e E)
    {N : ℕ} (hA : Kraus.IsNBlkInjective A N)
    (hB : Kraus.IsNBlkInjective B N) :
    Kraus.IsNBlkInjective (tensorProduct A B) N := by
  rw [Kraus.IsNBlkInjective, word_span_tensor_product]
  change Kraus.wordSpan A N = ⊤ at hA
  change Kraus.wordSpan B N = ⊤ at hB
  rw [hA, hB, TensorProduct.map₂_mk_top_top_eq_top]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    ((kroneckerLinearEquiv (Fin D) (Fin D) (Fin E) (Fin E) ℂ).trans
      (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv)).surjective

/-- Algebraic normality is preserved by independent tensor products.

If `S_{N_A}(A)` and `S_{N_B}(B)` are full at positive lengths `N_A` and
`N_B`, then `Kraus.wordSpan_top_of_mul` gives
\[
  S_{N_A N_B}(A)=\operatorname{Mat}_D(\mathbb C),\qquad
  S_{N_A N_B}(B)=\operatorname{Mat}_E(\mathbb C).
\]
The paired-span theorem at this common length gives a full product matrix
algebra.  This is project infrastructure for arXiv:1703.09188, proof of
Theorem `IndexTh` (ii), lines 824--845, not a separate paper theorem. -/
theorem is_normal_tensor_product (A : MPSTensor d D) (B : MPSTensor e E)
    (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B) :
    Kraus.IsNormal (tensorProduct A B) := by
  rcases hA with ⟨NA, hNA, hA⟩
  rcases hB with ⟨NB, hNB, hB⟩
  refine ⟨NA * NB, Nat.mul_pos hNA hNB, ?_⟩
  have hAcommon : Kraus.IsNBlkInjective A (NA * NB) := by
    change Kraus.wordSpan A (NA * NB) = ⊤
    have h := Kraus.wordSpan_top_of_mul A hA NB
      (Nat.one_le_iff_ne_zero.mpr hNB.ne')
    simpa [Nat.mul_comm] using h
  have hBcommon : Kraus.IsNBlkInjective B (NA * NB) := by
    change Kraus.wordSpan B (NA * NB) = ⊤
    exact Kraus.wordSpan_top_of_mul B hB NA
      (Nat.one_le_iff_ne_zero.mpr hNA.ne')
  exact is_n_blk_injective_tensor_product A B hAcommon hBcommon

end MPSTensor
