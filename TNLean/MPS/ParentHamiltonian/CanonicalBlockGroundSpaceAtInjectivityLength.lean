/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceAtInjectivityLength
import TNLean.MPS.ParentHamiltonian.CPSVOriginalRange

/-!
# Canonical tensors at a supplied simultaneous injectivity length

Repeated copies of a normal block and the ambient reconstruction of a
canonical tensor do not alter its positive-length local ground spaces.
Thus the periodic closure theorem for distinct blocks applies to the original
canonical tensor, retaining the supplied simultaneous injectivity length.

This is the block-injective parent ground-space theorem of CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2114--2129, including multiplicities
in the canonical form. The interaction range is at least the simultaneous
injectivity length plus one, as in the preceding intersection argument.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ} [NeZero d]

/-- The original canonical tensor, including all repeated block copies, has
the periodic ground space of its distinct normal representatives. The
supplied simultaneous injectivity length is retained. Source: CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem CPSVCanonicalFormData.ker_parentHamiltonian_eq_of_wordTupleSpanTop
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {S L N : ℕ}
    (hS : 0 < S)
    (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S)
    (hSL : S + 1 ≤ L) (hLN : L ≤ N) :
    LinearMap.ker (parentHamiltonian A L N) =
      bntMPSVectorSpan (fun j ↦ data.blocks (data.representativeIndex j)) N := by
  let B := fun j ↦ data.blocks (data.representativeIndex j)
  let : ∀ j, NeZero (data.dim (data.representativeIndex j)) :=
    fun j ↦ ⟨(data.dim_pos (data.representativeIndex j)).ne'⟩
  have hGS : groundSpace A L =
      groundSpace (toTensorFromBlocks (d := d) (fun _ ↦ 1) B) L := by
    exact (data.groundSpace_eq_iSup_representatives data.bntRefinement (by omega)).trans
      (groundSpace_toTensorFromBlocks_eq_iSup (fun _ ↦ 1) B (by simp) L).symm
  rw [ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hLN,
    chainGroundSpace_eq_of_groundSpace_eq hGS]
  exact chainGroundSpace_toTensorFromBlocks_eq_of_wordTupleSpanTop
    (fun _ ↦ 1) B (by simp) hS hSpan hSL hLN

/-- Positive terms with the prescribed local kernels have the same BNT
kernel for the original canonical tensor, including repeated copies.
Source: CPGSV21, arXiv:2011.12127, parent interactions at lines 1995--2007
and the block-injective closure theorem at lines 2126--2129. -/
theorem CPSVCanonicalFormData.ker_sum_eq_of_wordTupleSpanTop
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {S L N : ℕ}
    (hS : 0 < S)
    (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S)
    (hSL : S + 1 ≤ L) (hLN : L ≤ N)
    (H : Fin N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N))
    (hH : ∀ i, (H i).IsPositive)
    (hker : ∀ i, LinearMap.ker (H i) = LinearMap.ker (localTermES A L i)) :
    LinearMap.ker (∑ i, H i) =
      (bntMPSVectorSpan (fun j ↦ data.blocks (data.representativeIndex j)) N).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap := by
  have hEq : LinearMap.ker (∑ i, H i) = LinearMap.ker (parentHamiltonianES A L N) := by
    rw [parentHamiltonianES_eq_sum_localTermES,
      WeightedPositiveKernel.ker_sum_eq_iInf hH,
      WeightedPositiveKernel.ker_sum_eq_iInf (fun i ↦ localTermES_isPositive A L i)]
    simp only [hker]
  rw [hEq, ← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    data.ker_parentHamiltonian_eq_of_wordTupleSpanTop hS hSpan hSL hLN]

/-- A canonical tensor admits a basis of normal tensors for which every
supplied simultaneous injectivity length gives the sharp periodic kernel
identity, for all positive parent interactions with the prescribed kernels.
Repeated copies in the original canonical form are retained in the original
Hamiltonian. Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem IsCPSVCanonicalForm.exists_bnt_ker_sum_eq_of_wordTupleSpanTop
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (B : (j : Fin g) → MPSTensor d (dim j)),
      IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dim j, B j⟩) ∧
      ∀ {S L N : ℕ}, 0 < S → WordTupleSpanTop B S → S + 1 ≤ L → L ≤ N →
        ∀ H : Fin N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N),
          (∀ i, (H i).IsPositive) →
          (∀ i, LinearMap.ker (H i) = LinearMap.ker (localTermES A L i)) →
          LinearMap.ker (∑ i, H i) = (bntMPSVectorSpan B N).map
            (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap := by
  let data := Classical.choice hA
  refine ⟨data.phaseClasses.g, (fun j ↦ data.dim (data.representativeIndex j)),
    (fun j ↦ data.blocks (data.representativeIndex j)),
    data.bntRefinement.representativesBNT, ?_⟩
  intro S L N hS hSpan hSL hLN H hH hker
  exact data.ker_sum_eq_of_wordTupleSpanTop hS hSpan hSL hLN H hH hker

end MPSTensor
