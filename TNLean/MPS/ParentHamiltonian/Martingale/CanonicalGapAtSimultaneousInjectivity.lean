/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalBlockGroundSpaceAtInjectivityLength
import TNLean.MPS.ParentHamiltonian.Martingale.BlockGapAtSimultaneousInjectivity

/-!
# Canonical parent gaps at a supplied simultaneous injectivity length

Multiplicity copies and the ambient reconstruction of a canonical tensor
preserve its positive-length local ground spaces. The parent Hamiltonian
therefore agrees with that of its distinct normal representatives. This
transfers the block-injective gap to the original canonical tensor at the
same interaction range.

Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129 and
2183--2187; the canonical decomposition is CPSV16, arXiv:1606.00608,
equations `II_CF1`, `eq:II_ABasicTensors`, and `decBSV`.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Positive-range parent Hamiltonians of a canonical tensor coincide with
those of its distinct normal representatives, including all multiplicity
copies and the ambient reconstruction in CPSV16, equations `II_CF1` and
`decBSV`. -/
theorem CPSVCanonicalFormData.parentHamiltonianES_eq_representatives
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A)
    {R : ℕ} (hR : 0 < R) (N : ℕ) :
    parentHamiltonianES A R N = parentHamiltonianES
      (toTensorFromBlocks (d := d) (fun _ ↦ 1)
        (fun j ↦ data.blocks (data.representativeIndex j))) R N := by
  have hGS : groundSpace A R = groundSpace
      (toTensorFromBlocks (d := d) (fun _ ↦ 1)
        (fun j ↦ data.blocks (data.representativeIndex j))) R :=
    (data.groundSpace_eq_iSup_representatives data.bntRefinement hR).trans
      (groundSpace_toTensorFromBlocks_eq_iSup (fun _ ↦ 1)
        (fun j ↦ data.blocks (data.representativeIndex j)) (by simp) R).symm
  simp only [parentHamiltonianES, parentHamiltonian, localTerm, parentInteraction,
    groundSpaceES, hGS]

variable [NeZero d]

/-- A canonical tensor has a positive uniform periodic gap at every range
at least one more than a supplied simultaneous injectivity length of its normal
representatives. Multiplicities and ambient reconstruction remain part of the
original tensor. Source: CPGSV21, Section IV.C, lines 2114--2129 and 2183--2187. -/
theorem CPSVCanonicalFormData.exists_parentHamiltonianES_uniform_gap_of_wordTupleSpanTop
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {S R : ℕ}
    (hS : 0 < S)
    (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S)
    (hR : S + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      γ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  let : ∀ j, NeZero (data.dim (data.representativeIndex j)) :=
    fun j ↦ ⟨(data.dim_pos (data.representativeIndex j)).ne'⟩
  simp_rw [data.parentHamiltonianES_eq_representatives (show 0 < R by omega)]
  exact exists_parentHamiltonianES_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop
    (fun _ ↦ 1) (fun j ↦ data.blocks (data.representativeIndex j))
    (by simp) hS hSpan hR

/-- A canonical tensor admits one choice of normal representatives for which
every supplied simultaneous injectivity length yields the uniform gap at the
corresponding interaction range. Source: CPGSV21, Section IV.C,
lines 2114--2129 and 2183--2187. -/
theorem IsCPSVCanonicalForm.exists_bnt_uniform_gap_of_wordTupleSpanTop
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (B : (j : Fin g) → MPSTensor d (dim j)),
      IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dim j, B j⟩) ∧
      ∀ {S R : ℕ}, 0 < S → WordTupleSpanTop B S → S + 1 ≤ R →
        ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ v ∈
          (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
          γ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  let data := Classical.choice hA
  refine ⟨data.phaseClasses.g, (fun j ↦ data.dim (data.representativeIndex j)),
    (fun j ↦ data.blocks (data.representativeIndex j)),
    data.bntRefinement.representativesBNT, ?_⟩
  intro S R hS hSpan hR
  exact data.exists_parentHamiltonianES_uniform_gap_of_wordTupleSpanTop hS hSpan hR

end MPSTensor
