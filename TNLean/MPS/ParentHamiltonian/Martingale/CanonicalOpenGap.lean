/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalBoundedRangeGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.BlockOpenGapAllLengths

/-!
# Uniform open-chain gaps for canonical tensors

The distinct normal representatives have the same positive-length local
spaces as the full canonical tensor, including its multiplicities and ambient
reconstruction. Their all-length open-chain gap therefore transfers to the
original tensor. A positive bond dimension \(D\) supplies a simultaneous
injectivity length \(S\) with \(S+1\leq3D^5\), giving the dimension bound
without a supplied injectivity length.

Source: arXiv:1606.00608, equations `II_CF1` and `decBSV`, lines 317--345;
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6.

**Scope restriction (sufficient interaction range):** The supplied-span
statements assume \(R\geq S+1\); the dimension-bound statement assumes
\(R\geq3D^5\). These sufficient ranges and the false unrestricted
short-range claim are documented in
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex` and
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Multiplicities and ambient reconstruction preserve every positive-range
open parent Hamiltonian. Source: CPSV16, arXiv:1606.00608, equations
`II_CF1`, `eq:II_ABasicTensors`, and `decBSV`. -/
theorem CPSVCanonicalFormData.openParentHamiltonianES_eq_representatives
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A)
    {R : ℕ} (hR : 0 < R) (N : ℕ) :
    openParentHamiltonianES A R N = openParentHamiltonianES
      (toTensorFromBlocks (d := d) (fun _ ↦ 1)
        (fun j ↦ data.blocks (data.representativeIndex j))) R N := by
  simp only [openParentHamiltonianES, localTermES, localTerm, parentInteraction,
    groundSpaceES, data.groundSpace_eq_toTensorFromBlocks_representatives hR]

variable [NeZero d]

/-- The normal representatives of a canonical tensor give a uniform open-chain
gap at every range \(R\geq S+1\), for every chain length \(N\geq R\).
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6;
CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem CPSVCanonicalFormData.exists_openParentHamiltonianES_gap_of_wordTupleSpanTop
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {S R : ℕ}
    (hS : 0 < S)
    (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S)
    (hR : S + 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let : ∀ j, NeZero (data.dim (data.representativeIndex j)) :=
    fun j ↦ ⟨(data.dim_pos (data.representativeIndex j)).ne'⟩
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_openParentHamiltonianES_toTensorFromBlocks_gap_of_wordTupleSpanTop
      (fun _ ↦ 1) (fun j ↦ data.blocks (data.representativeIndex j))
      (by simp) hS hSpan hR
  refine ⟨δ, hδ, ?_⟩
  exact fun N hN ↦ by
    simpa only [data.openParentHamiltonianES_eq_representatives (by omega : 0 < R) N,
      groundSpaceES, data.groundSpace_eq_toTensorFromBlocks_representatives
        (by omega : 0 < N)] using hGap N hN

/-- A canonical tensor of positive bond dimension \(D\) has a uniform
open-chain gap at every range \(R\geq3D^5\) and every length \(N\geq R\).
The simultaneous injectivity length is derived from the canonical data.
Source: arXiv:1606.00608, lines 317--345; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem IsCPSVCanonicalForm.exists_openParentHamiltonianES_gap_of_three_bondDim_pow_five_le
    [NeZero D]
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) {R : ℕ}
    (hR : 3 * D ^ 5 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let data := Classical.choice hA
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    data.exists_positive_wordTupleSpanTop_succ_le_three_bondDim_pow_five
  exact data.exists_openParentHamiltonianES_gap_of_wordTupleSpanTop
    hS hSpan (hBound.trans hR)

/-- One choice of normal representatives supplies the uniform open-chain gap
at every admissible supplied simultaneous injectivity range.
Source: CPSV16, arXiv:1606.00608, equations `II_CF1` and `decBSV`;
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem IsCPSVCanonicalForm.exists_bnt_open_gap_of_wordTupleSpanTop
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (B : (j : Fin g) → MPSTensor d (dim j)),
      IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dim j, B j⟩) ∧
      ∀ {S R : ℕ}, 0 < S → WordTupleSpanTop B S → S + 1 ≤ R →
        ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
          δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let data := Classical.choice hA
  refine ⟨data.phaseClasses.g, (fun j ↦ data.dim (data.representativeIndex j)),
    (fun j ↦ data.blocks (data.representativeIndex j)),
    data.bntRefinement.representativesBNT, ?_⟩
  exact fun {_S _R} hS hSpan hR ↦
    data.exists_openParentHamiltonianES_gap_of_wordTupleSpanTop hS hSpan hR

/-- At an admissible simultaneous injectivity range, the open kernel of a
canonical tensor is its full boundary-condition space, including multiplicities
and ambient reconstruction. Source: CPGSV21, arXiv:2011.12127, Section IV.C,
lines 2114--2129; CPSV16, arXiv:1606.00608, equations `II_CF1` and `decBSV`. -/
theorem CPSVCanonicalFormData.ker_openParentHamiltonianES_eq_groundSpaceES_of_wordTupleSpanTop
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {S R N : ℕ}
    (hS : 0 < S)
    (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S)
    (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N := by
  let : ∀ j, NeZero (data.dim (data.representativeIndex j)) :=
    fun j ↦ ⟨(data.dim_pos (data.representativeIndex j)).ne'⟩
  simpa only [data.openParentHamiltonianES_eq_representatives (by omega : 0 < R) N,
    groundSpaceES, data.groundSpace_eq_toTensorFromBlocks_representatives
      (by omega : 0 < N)] using
    ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
      (fun _ ↦ 1) (fun j ↦ data.blocks (data.representativeIndex j))
      (by simp) hS hSpan hR hRN

end MPSTensor
