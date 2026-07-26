/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Periodic.NormalizedSelfOverlap
import TNLean.MPS.RFP.BNTOrthogonality

/-!
# BNT basis data for the unit-weight direct sum

This file packages a BNT canonical form as a CPSV basis of normal tensors for
its multiplicity-one unit-weight direct-sum representative.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The unit-weight block tensor is the direct-sum tensor. -/
theorem toTensorFromBlocks_one_eq_directSumTensor
    (A : (j : Fin r) → MPSTensor d (dim j)) :
    toTensorFromBlocks (d := d) (fun _ ↦ 1) A = directSumTensor A := by
  funext i
  simp [toTensorFromBlocks, directSumTensor]

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- The multiplicity-one unit-weight direct sum of the distinct basis tensors
is in literal CPSV canonical form.

Each basis tensor is normal because it is irreducible and left-canonical, and
its retained coordinates are exactly the ambient direct-sum coordinates.

**Scope restriction (multiplicity-one unit weights):** the statement covers
one unit-weight copy of each distinct basis tensor. It does not reconstruct the
raw weighted repeated-copy tensor of arXiv:1606.00608, eq. `II_CF1`; see
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isCPSVCanonicalForm_basisDirectSum
    (hCF : IsBNTCanonicalForm P) :
    IsCPSVCanonicalForm (directSumTensor P.basis) := by
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
  rw [← toTensorFromBlocks_one_eq_directSumTensor P.basis]
  exact
    (CPSVCanonicalFormData.ofBlocks hCF.basis_dim_pos (fun _ ↦ 1) P.basis
      (fun j ↦ isNormalTensor_of_isNormal_leftCanonical (P.basis j)
        (hCF.basis_isNormal j) (hCF.basis_left_canonical j))).isCPSVCanonicalForm

/-- The distinct basis tensors of a BNT canonical form are a basis of normal
tensors for their direct-sum tensor.

Each basis block of a BNT canonical form is irreducible and left-canonical
with normalized self-overlap, hence a spectrally normalized normal tensor; the
MPV family of the unit-weight direct sum is the plain sum of the block MPV
families; and the eventual linear independence of the basis MPV states is part
of the canonical form. This is the basis-of-normal-tensors relation of
arXiv:1606.00608, lines 271--274, at the explicit multiplicity-one unit-weight
representative $A=\bigoplus_j A_j$ used in the proof of Theorem
`thm:main-MPS`, lines 534--541.

**Scope restriction (multiplicity-one unit weights):** the statement covers
the direct sum of the distinct basis tensors with one unit-weight copy each.
Repeated copies and raw sector weights remain outside this statement; see
docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex. -/
theorem isCPSVBasisOfNormalTensors_basisDirectSum
    (hCF : IsBNTCanonicalForm P) :
    IsCPSVBasisOfNormalTensors (directSumTensor P.basis)
      (fun j => ⟨P.basisDim j, P.basis j⟩) := by
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
  refine {
    blocks_normal := fun j ↦
      isNormalTensor_of_isNormal_leftCanonical (P.basis j)
        (hCF.basis_isNormal j) (hCF.basis_left_canonical j)
    spans_mpv := ?_
    eventually_li := by exact hCF.bnt_data }
  intro N _hN
  refine ⟨fun _ ↦ 1, fun σ ↦ ?_⟩
  rw [← toTensorFromBlocks_one_eq_directSumTensor P.basis,
    mpv_toTensorFromBlocks_eq_sum]
  simp

end IsBNTCanonicalForm

end MPSTensor
