/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.SpectralRadius
import TNLean.MPS.CanonicalForm.CPSVPhysicalReindex
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.CanonicalForm.SectorComparison.PrimitiveBlocks

/-!
# Literal CPSV canonical forms under positive physical blocking

This module proves that CPSV normal tensors and literal CPSV canonical-form
data are preserved by blocking a positive number of physical sites.

The retained block dimensions and the ambient coisometry are unchanged.  Each
normal block is replaced by its physical block tensor and each CPSV weight is
raised to the blocking length.  The reconstruction is the exact blocked
letterwise reconstruction, not only equality of closed-chain coefficients.

## Main results

* `MPSTensor.IsNormalTensor.blockTensor`: positive blocking preserves normal
  tensors.
* `MPSTensor.CPSVCanonicalFormData.blockTensor`: literal canonical-form data
  block exactly.
* `MPSTensor.IsCPSVCanonicalForm.blockTensor`: positive blocking preserves
  literal CPSV canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Section 2.3,
  lines 214--245 and eq. `II_CF1`.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

namespace GaugeEquiv

/-- Gauge equivalence is preserved by blocking the physical alphabet. -/
theorem blockTensor {A B : MPSTensor d D} (h : GaugeEquiv A B) (p : ℕ) :
    GaugeEquiv (blockTensor (d := d) (D := D) A p)
      (blockTensor (d := d) (D := D) B p) := by
  obtain ⟨X, hX⟩ := h
  refine ⟨X, fun i ↦ ?_⟩
  simpa [MPSTensor.blockTensor, Matrix.GeneralLinearGroup.coe_inv] using
    evalWord_gauge (A := A) (B := B) X hX (wordOfBlock d p i)

/-- The transfer maps of gauge-equivalent tensors are related by the standard
congruence similarity of completely positive maps. -/
theorem transferMap_eq_similarityMap {A B : MPSTensor d D} (h : GaugeEquiv A B) :
    ∃ C : Matrix (Fin D) (Fin D) ℂ, C.det ≠ 0 ∧
      transferMap (d := d) (D := D) B =
        similarityMap (D := D) C (transferMap (d := d) (D := D) A) := by
  obtain ⟨X, hX⟩ := h
  refine ⟨((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), ?_, ?_⟩
  · exact Matrix.GeneralLinearGroup.det_ne_zero (X⁻¹ : GL (Fin D) ℂ)
  · apply LinearMap.ext
    intro Y
    have hXdet : IsUnit ((X : Matrix (Fin D) (Fin D) ℂ).det) :=
      Ne.isUnit (Matrix.GeneralLinearGroup.det_ne_zero X)
    have hX_inv_inv :
        ((X : Matrix (Fin D) (Fin D) ℂ)⁻¹)⁻¹ =
          (X : Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.nonsing_inv_nonsing_inv (X : Matrix (Fin D) (Fin D) ℂ) hXdet
    have hXstar_det : IsUnit (((X : Matrix (Fin D) (Fin D) ℂ)ᴴ).det) := by
      simpa [Matrix.det_conjTranspose] using IsUnit.star hXdet
    have hXstar_inv_inv :
        (((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)⁻¹)⁻¹ =
          (X : Matrix (Fin D) (Fin D) ℂ)ᴴ :=
      Matrix.nonsing_inv_nonsing_inv
        ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ) hXstar_det
    calc
      transferMap (d := d) (D := D) B Y =
          ∑ x : Fin d,
            ((X : Matrix (Fin D) (Fin D) ℂ) * A x *
              (X : Matrix (Fin D) (Fin D) ℂ)⁻¹) * Y *
              (((X : Matrix (Fin D) (Fin D) ℂ) * A x *
                (X : Matrix (Fin D) (Fin D) ℂ)⁻¹)ᴴ) := by
            simp [transferMap_apply, hX]
      _ = ∑ x : Fin d,
            (X : Matrix (Fin D) (Fin D) ℂ) *
              (A x * ((X : Matrix (Fin D) (Fin D) ℂ)⁻¹ * Y *
                ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)⁻¹) * (A x)ᴴ) *
              (X : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro x _
            simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
              Matrix.mul_assoc]
      _ = (X : Matrix (Fin D) (Fin D) ℂ) *
            (∑ x : Fin d,
              A x * ((X : Matrix (Fin D) (Fin D) ℂ)⁻¹ * Y *
                ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)⁻¹) * (A x)ᴴ) *
            (X : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
            simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
      _ = similarityMap (D := D)
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
            (transferMap (d := d) (D := D) A) Y := by
            simp [similarityMap, transferMap_apply, Matrix.conjTranspose_nonsing_inv,
              hX_inv_inv, hXstar_inv_inv, Matrix.mul_assoc]

end GaugeEquiv

namespace IsNormalTensor

/-- Transport normal-tensor status backward along a gauge equivalence.

The transfer maps are similar, hence have the same spectral radius and
peripheral spectrum; irreducibility is transported through the corresponding
irreducible-map similarity. -/
theorem of_gaugeEquiv {A B : MPSTensor d D} (hB : IsNormalTensor B)
    (hGauge : GaugeEquiv A B) :
    IsNormalTensor A := by
  obtain ⟨C, hC, hMap⟩ := hGauge.transferMap_eq_similarityMap
  refine ⟨?_, ?_, ?_⟩
  · have hIrrB : IsIrreducibleMap (transferMap (d := d) (D := D) B) :=
      isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB.no_invariant_proj
    have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) := by
      have hIrrSim : IsIrreducibleMap
          (similarityMap (D := D) C (transferMap (d := d) (D := D) A)) := by
        simpa [hMap] using hIrrB
      exact (isIrreducibleMap_similarity_iff (D := D) hC).1 hIrrSim
    exact isIrreducibleTensor_of_isIrreducibleMap A hIrrA
  · have hsr := hB.spectral_radius_one
    rw [hMap] at hsr
    rw [spectralRadius_similarityMap_eq (D := D) C hC
      (transferMap (d := d) (D := D) A)] at hsr
    exact hsr
  · have hPrim := hB.primitive_transfer
    rw [hMap] at hPrim
    exact (IsPrimitive.similarityMap_iff (D := D) C hC
      (transferMap (d := d) (D := D) A)).1 hPrim

/-- Positive physical blocking preserves CPSV normal tensors.

The proof puts the tensor into its trace-preserving Perron gauge.  Positive
blocking preserves trace preservation, transfer-map primitivity, and tensor
irreducibility for that gauge; hence the blocked gauge is a normal tensor.  A
blocked gauge equivalence then transports the result back to the original
blocked tensor. -/
theorem blockTensor {A : MPSTensor d D} (hA : IsNormalTensor A) (p : ℕ) (hp : 0 < p) :
    IsNormalTensor (MPSTensor.blockTensor (d := d) (D := D) A p) := by
  letI : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, _hσpos, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := hA.exists_tpGauge
  let B : MPSTensor d D := tpGauge (d := d) (D := D) A σ
  have hExtra := tp_primitive_irreducible_extra_blocking
    (d := d) (D := D) B hTP hPrim hIrr hp
  have hNormalAlg : IsNormal (MPSTensor.blockTensor (d := d) (D := D) B p) :=
    isNormal_of_tp_primitive_irreducible
      (d := blockPhysDim d p) (D := D)
      (MPSTensor.blockTensor (d := d) (D := D) B p) hExtra.1 hExtra.2.1 hExtra.2.2
  have hBlockedGaugeNormal :
      IsNormalTensor (MPSTensor.blockTensor (d := d) (D := D) B p) :=
    isNormalTensor_of_isNormal_leftCanonical
      (d := blockPhysDim d p) (D := D)
      (MPSTensor.blockTensor (d := d) (D := D) B p) hNormalAlg hExtra.1
  exact hBlockedGaugeNormal.of_gaugeEquiv (hGauge.blockTensor p)

end IsNormalTensor

/-- Exact word-level transport through a coisometric reconstruction, for
nonempty words. -/
theorem evalWord_eq_coisometry_reconstruction_of_ne_nil
    {s d n : ℕ} {A : MPSTensor s d} {B : MPSTensor s n}
    (U : Matrix (Fin n) (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ v, A v = Uᴴ * B v * U) :
    ∀ w : List (Fin s), w ≠ [] →
      evalWord A w = Uᴴ * evalWord B w * U
  | [], hnil => False.elim (hnil rfl)
  | v :: w, _ => by
      induction w generalizing v with
      | nil =>
          simpa [evalWord] using hReconstruct v
      | cons v' w ih =>
          change A v * evalWord A (v' :: w) =
            Uᴴ * (B v * evalWord B (v' :: w)) * U
          rw [hReconstruct v, ih v' (by simp)]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul]

/-- Blocking a weighted direct sum is exactly the weighted direct sum of the
blocked summands, with every weight raised to the blocking length. -/
theorem blockTensor_toTensorFromBlocks_apply {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k))
    (p : ℕ) (i : Fin (blockPhysDim d p)) :
    blockTensor (d := d) (D := ∑ k : Fin r, dim k)
        (toTensorFromBlocks (d := d) (μ := μ) blocks) p i =
      toTensorFromBlocks (d := blockPhysDim d p)
        (fun k ↦ μ k ^ p)
        (fun k ↦ blockTensor (d := d) (D := dim k) (blocks k) p) i := by
  simp [MPSTensor.blockTensor, toTensorFromBlocks,
    evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal,
    length_wordOfBlock]

namespace CPSVCanonicalFormData

/-- Literal CPSV canonical-form data are preserved by positive physical
blocking.

The retained dimensions and ambient coisometry are unchanged.  The retained
weights are raised to the blocking length and each retained normal tensor is
blocked by that length.

Source: arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`. -/
noncomputable def blockTensor {A : MPSTensor d D}
    (data : CPSVCanonicalFormData A) (p : ℕ) (hp : 0 < p) :
    CPSVCanonicalFormData (MPSTensor.blockTensor (d := d) (D := D) A p) where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := fun k ↦ data.weights k ^ p
  blocks := fun k ↦ MPSTensor.blockTensor (d := d) (D := data.dim k) (data.blocks k) p
  blocks_normal := fun k ↦ (data.blocks_normal k).blockTensor p hp
  total_dim_le := data.total_dim_le
  ambient_coisometry := data.ambient_coisometry
  coisometric := data.coisometric
  reconstruct := by
    intro i
    have hword_ne : wordOfBlock d p i ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp [length_wordOfBlock, hp.ne'] at hlen
    calc
      MPSTensor.blockTensor (d := d) (D := D) A p i =
          data.ambient_coisometryᴴ *
            evalWord (toTensorFromBlocks (d := d) data.weights data.blocks)
              (wordOfBlock d p i) *
            data.ambient_coisometry := by
            simpa [MPSTensor.blockTensor] using
              evalWord_eq_coisometry_reconstruction_of_ne_nil
                data.ambient_coisometry data.coisometric data.reconstruct
                (wordOfBlock d p i) hword_ne
      _ = data.ambient_coisometryᴴ *
            toTensorFromBlocks (d := blockPhysDim d p)
              (fun k ↦ data.weights k ^ p)
              (fun k ↦ MPSTensor.blockTensor (d := d) (D := data.dim k)
                (data.blocks k) p) i *
            data.ambient_coisometry := by
            have hblock := blockTensor_toTensorFromBlocks_apply
              (d := d) (dim := data.dim) data.weights data.blocks p i
            rw [← hblock]
            rfl

end CPSVCanonicalFormData

namespace IsCPSVCanonicalForm

/-- Positive physical blocking preserves literal CPSV canonical form. -/
theorem blockTensor {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A)
    (p : ℕ) (hp : 0 < p) :
    IsCPSVCanonicalForm (MPSTensor.blockTensor (d := d) (D := D) A p) := by
  obtain ⟨data⟩ := hA
  exact ⟨data.blockTensor p hp⟩

end IsCPSVCanonicalForm

end MPSTensor
