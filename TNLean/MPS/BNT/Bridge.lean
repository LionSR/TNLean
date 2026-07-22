/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.BNT.Basic
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Periodic.NormalizedSelfOverlap

/-!
# Bridges between basis-of-normal-tensors predicates

This module records the one-way connections between the three BNT surfaces used
in TNLean:

* `IsCPSVBasisOfNormalTensors`, the source-faithful CPSV16 spectral predicate;
* `IsBNT`, the algebraic eventual-block-injectivity predicate; and
* `IsBNTCanonicalForm`, the stronger sector-decomposition canonical form.

The bridges are deliberately implications, not equivalences.  In particular,
`IsNormalTensor` contains spectral-radius and peripheral-spectrum data that are
not recoverable merely by unfolding `IsNormal`, while `IsBNTCanonicalForm`
contains normalization, irreducibility, left-canonicality, and distinctness data
absent from `IsBNT`.

## Main results

* `IsCPSVBasisOfNormalTensors.blocks_dim_pos`: every source BNT block has
  positive bond dimension;
* `IsCPSVBasisOfNormalTensors.isBNT`: a CPSV16 BNT gives an algebraic BNT;
* `IsBNT.of_sameMPV₂Pos`: transport an algebraic BNT along positive-length MPV
  equality;
* `IsBNTCanonicalForm.basis_isNormal`: every canonical-form basis block is
  algebraically normal;
* `IsBNTCanonicalForm.isBNT`: forget a canonical form to its algebraic BNT.

## References

* CPSV16, arXiv:1606.00608, lines 231--235 and 271--274.
* CPSV21, arXiv:2011.12127, Definition 4.2, lines 1846--1850.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A tensor with a nonzero matrix product state has positive bond dimension. -/
private theorem bondDim_pos_of_mpvState_ne_zero {A : MPSTensor d D} {N : ℕ}
    (hA : mpvState (d := d) A N ≠ 0) :
    0 < D := by
  by_contra hD
  have hD0 : D = 0 := Nat.eq_zero_of_not_pos hD
  subst D
  apply hA
  ext σ
  simp [mpvState, mpv, coeff, Matrix.trace]

/-- Every tensor in a CPSV16 basis of normal tensors has positive bond
 dimension.

This follows from eventual linear independence: each sufficiently long matrix
product state in the basis is nonzero.

Source: arXiv:1606.00608, BNT definition at lines 271--274. -/
theorem IsCPSVBasisOfNormalTensors.blocks_dim_pos
    {g : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    ∀ j, 0 < dim j := by
  intro j
  obtain ⟨N₀, hLI⟩ := hBNT.eventually_li
  have hN : N₀ < N₀ + 1 := by omega
  have hne : mpvState (d := d) (B j) (N₀ + 1) ≠ 0 :=
    (hLI (N₀ + 1) hN).ne_zero j
  exact bondDim_pos_of_mpvState_ne_zero hne

/-- Forget the spectral normality data of a CPSV16 BNT to obtain the algebraic
BNT predicate.

This implication uses `IsNormalTensor.isNormal` blockwise.  No converse is
asserted: algebraic eventual block injectivity alone does not carry the
spectral-radius-one normalization stored by `IsNormalTensor`.

Source: arXiv:1606.00608, lines 231--235 and 271--274. -/
theorem IsCPSVBasisOfNormalTensors.isBNT
    {g : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    IsBNT A g dim B := by
  refine ⟨?_, hBNT.spans_mpv, hBNT.eventually_li⟩
  intro j
  letI : NeZero (dim j) := ⟨(hBNT.blocks_dim_pos j).ne'⟩
  exact (hBNT.blocks_normal j).isNormal

/-- Transport an algebraic BNT from `A` to a tensor `A'` with the same
positive-length matrix product vectors.

Only the spanning clause depends on the represented tensor; normality and
eventual linear independence belong to the fixed basis family. -/
theorem IsBNT.of_sameMPV₂Pos
    {g D' : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {A' : MPSTensor d D'}
    {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsBNT A g dim B) (hSame : SameMPV₂Pos A A') :
    IsBNT A' g dim B := by
  refine ⟨hBNT.normal, ?_, hBNT.eventually_li⟩
  intro N hN
  obtain ⟨c, hc⟩ := hBNT.spans_mpv N hN
  exact ⟨c, fun σ => (hSame N hN σ).symm.trans (hc σ)⟩

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- Every basis tensor in BNT canonical form is algebraically normal.

The canonical-form irreducibility, left-canonicality, normalized self-overlap,
and positive bond dimension imply eventual block injectivity.

Source: CPSV21, arXiv:2011.12127, lines 1815--1830. -/
theorem basis_isNormal (hCF : IsBNTCanonicalForm P) (j : Fin P.basisCount) :
    IsNormal (P.basis j) := by
  letI : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
  exact isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
    (P.basis j) (hCF.basis_irreducible j) (hCF.basis_left_canonical j)
      (hCF.basis_normalized_self_overlap j)

/-- Forget a BNT canonical form to the algebraic BNT carried by its basis.

The sector coefficient formula supplies the spanning clause, while
`HasBNTSectorData` supplies eventual linear independence.  This is only a
projection: the weight normalization and canonical-form data cannot be
reconstructed from `IsBNT`.

Source: CPSV16, arXiv:1606.00608, lines 271--301; CPSV21,
arXiv:2011.12127, lines 1846--1884. -/
theorem isBNT (hCF : IsBNTCanonicalForm P) :
    IsBNT P.toTensor P.basisCount P.basisDim P.basis := by
  refine ⟨hCF.basis_isNormal, ?_, hCF.bnt_data⟩
  intro N _hN
  exact ⟨P.coeff N, fun σ => P.mpv_toTensor_eq_sum_coeff σ⟩

end IsBNTCanonicalForm

end MPSTensor
