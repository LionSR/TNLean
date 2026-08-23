/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
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

## Main definitions

* `MPSTensor.CPSVCanonicalFormData.blockTensor`: literal canonical-form data
  block exactly.
* `MPSTensor.CPSVCanonicalFormIIData.blockTensor`: blockwise canonical-form-II data block
  exactly.

## Main results

* `MPSTensor.IsNormalTensor.blockTensor`: positive blocking preserves normal
  tensors.
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

/-- Gauge equivalence is preserved by blocking the physical alphabet.

Source: arXiv:1606.00608, line 227 defines blocking by matrix products and
lines 264--268 give the invertible gauge relation. -/
theorem blockTensor {A B : MPSTensor d D} (h : GaugeEquiv A B) (p : ℕ) :
    GaugeEquiv (blockTensor (d := d) (D := D) A p)
      (blockTensor (d := d) (D := D) B p) := by
  obtain ⟨X, hX⟩ := h
  refine ⟨X, fun i ↦ ?_⟩
  simpa [MPSTensor.blockTensor, Matrix.GeneralLinearGroup.coe_inv] using
    evalWord_gauge (A := A) (B := B) X hX (wordOfBlock d p i)

end GaugeEquiv

namespace IsNormalTensor

/-- Positive physical blocking preserves CPSV normal tensors.

The proof puts the tensor into its trace-preserving Perron gauge.  Positive
blocking preserves trace preservation, transfer-map primitivity, and tensor
irreducibility for that gauge; hence the blocked gauge is a normal tensor.  A
blocked gauge equivalence then transports the result back to the original
blocked tensor.

Source: arXiv:1606.00608, lines 227--235 define physical blocking and normal
tensors; the closure under reblocking is used in the normal-block arguments at
lines 332--345. -/
theorem blockTensor {A : MPSTensor d D} (hA : IsNormalTensor A) (p : ℕ) (hp : 0 < p) :
    IsNormalTensor (MPSTensor.blockTensor (d := d) (D := D) A p) := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, _hσpos, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := hA.exists_tpGauge
  let B : MPSTensor d D := tpGauge (d := d) (D := D) A σ
  have hExtra := tp_primitive_irreducible_extra_blocking
    (d := d) (D := D) B hTP hPrim hIrr hp
  have hNormalAlg : Kraus.IsNormal (MPSTensor.blockTensor (d := d) (D := D) B p) :=
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
nonempty words.

Source: arXiv:1606.00608, equation `II_CF1` at lines 237--244 gives the
one-site canonical-form reconstruction, and Proposition 4.13 at lines
1917--1921 uses the corresponding coisometric reconstruction.  This theorem is
its nonempty-word iteration, with intermediate coisometries cancelled by
\(UU^*=1\). -/
theorem evalWord_eq_coisometry_reconstruction_of_ne_nil
    {s d n : ℕ} {A : MPSTensor s d} {B : MPSTensor s n}
    (U : Matrix (Fin n) (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ v, A v = Uᴴ * B v * U) :
    ∀ w : List (Fin s), w ≠ [] →
      Kraus.evalWord A w = Uᴴ * Kraus.evalWord B w * U
  | [], hnil => False.elim (hnil rfl)
  | v :: w, _ => by
      induction w generalizing v with
      | nil =>
          simpa [Kraus.evalWord] using hReconstruct v
      | cons v' w ih =>
          change A v * Kraus.evalWord A (v' :: w) =
            Uᴴ * (B v * Kraus.evalWord B (v' :: w)) * U
          rw [hReconstruct v, ih v' (by simp)]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul]

/-- Blocking a weighted direct sum is exactly the weighted direct sum of the
blocked summands, with every weight raised to the blocking length.

Source: arXiv:1606.00608, lines 259--301, especially equations `II_Psi_k`,
`II_ABasicTensors`, and `decBSV`. -/
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
            Kraus.evalWord (toTensorFromBlocks (d := d) data.weights data.blocks)
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

namespace CPSVCanonicalFormIIData

/-- Blockwise CPSV canonical-form-II data are preserved by positive physical blocking.

Each fixed-point matrix remains positive definite and diagonal, and is fixed by the blocked transfer
map because that map is the corresponding positive power of the original transfer map. The same
matrix is retained, so any separately supplied trace normalization is also unchanged.

Source: arXiv:1703.09188, Section II, lines 297--305, and Section III, line 356. -/
noncomputable def blockTensor {A : MPSTensor d D}
    (data : CPSVCanonicalFormIIData A) (p : ℕ) (hp : 0 < p) :
    CPSVCanonicalFormIIData (MPSTensor.blockTensor (d := d) (D := D) A p) where
  toCPSVCanonicalFormData := data.toCPSVCanonicalFormData.blockTensor p hp
  blocks_left_canonical := fun k ↦
    leftCanonical_blockTensor (data.blocks k) p (data.blocks_left_canonical k)
  blocks_fixed_point := by
    intro k
    obtain ⟨Λ, hΛpos, hΛdiag, hΛfix⟩ := data.blocks_fixed_point k
    exact ⟨Λ, hΛpos, hΛdiag, by
      change Kraus.transferMap (MPSTensor.blockTensor (data.blocks k) p) Λ = Λ
      exact transferMap_blockTensor_fixedPoint (data.blocks k) p Λ hΛfix⟩

end CPSVCanonicalFormIIData

namespace IsCPSVCanonicalForm

/-- Positive physical blocking preserves literal CPSV canonical form.

Source: arXiv:1606.00608, lines 227--244 define blocking, normal tensors, and
canonical form; lines 259--301 give the weight-power expansion under products. -/
theorem blockTensor {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A)
    (p : ℕ) (hp : 0 < p) :
    IsCPSVCanonicalForm (MPSTensor.blockTensor (d := d) (D := D) A p) := by
  obtain ⟨data⟩ := hA
  exact ⟨data.blockTensor p hp⟩

end IsCPSVCanonicalForm

end MPSTensor
