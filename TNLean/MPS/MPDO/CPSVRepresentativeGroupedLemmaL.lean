/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ActiveBNTRefinement
import TNLean.MPS.MPDO.RepresentativeGroupedMarkedLemmaL
import TNLean.MPS.MPDO.SourceBNTBlocking
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.Scaling

/-!
# Lemma L for active refinements of literal CPSV canonical form

The nonzero listed blocks of a literal CPSV canonical form are grouped over chosen normal
representatives.  A copy with raw weight `ν` and phase `ζ` contributes the representative
weight `ν * ζ`.  Zero-weight listed blocks remain in the full grouped bond coordinates, but
are omitted from the representative sector decomposition.

The positive-length and marked-trace identities below connect these two descriptions.  The
representative-grouped versions of Lemma L then apply with no normalization assumptions.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858, as used in
Proposition 4.13, lines 1874--1887 and 1909--1919.
-/

open scoped Matrix BigOperators

namespace MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement

variable {d D e : ℕ} {A : MPSTensor d D}
variable {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement)

private noncomputable def activeCopy
    (j : Fin data.activePhaseClasses.g)
    (q : Fin (data.activePhaseClasses.copies j)) : data.Active :=
  data.activeClassCopyEquiv ⟨j, q⟩

/-- The active representative sector decomposition.  Its copy weight is the original raw
weight times the phase relating that copy to its chosen representative.

Inactive zero-weight listed blocks are absent because `SectorDecomposition` requires every
stored copy weight to be nonzero.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
noncomputable def representativeSectorDecomposition : SectorDecomposition d where
  basisCount := data.activePhaseClasses.g
  basisDim := fun j => data.dim (data.activeRepresentativeIndex j)
  basis := fun j => data.blocks (data.activeRepresentativeIndex j)
  sectors := {
    copies := data.activePhaseClasses.copies
    copies_pos := data.activePhaseClasses.copies_pos
    weight := fun j q => ref.copyWeight (ref.activeCopy j q) * ref.copyPhase (ref.activeCopy j q)
    weight_ne_zero := fun j q => mul_ne_zero
      (by rw [ref.copyWeightEq]; exact (ref.activeCopy j q).property)
      (Complex.ne_zero_of_norm_eq_one (ref.copyPhaseNorm (ref.activeCopy j q)))
  }

@[simp] theorem representativeSectorDecomposition_basisCount :
    ref.representativeSectorDecomposition.basisCount = data.activePhaseClasses.g := rfl

@[simp] theorem representativeSectorDecomposition_basisDim
    (j : Fin data.activePhaseClasses.g) :
    ref.representativeSectorDecomposition.basisDim j =
      data.dim (data.activeRepresentativeIndex j) := rfl

@[simp] theorem representativeSectorDecomposition_basis
    (j : Fin data.activePhaseClasses.g) :
    ref.representativeSectorDecomposition.basis j =
      data.blocks (data.activeRepresentativeIndex j) := rfl

@[simp] theorem representativeSectorDecomposition_copies
    (j : Fin data.activePhaseClasses.g) :
    ref.representativeSectorDecomposition.copies j =
      data.activePhaseClasses.copies j := rfl

@[simp] theorem representativeSectorDecomposition_weight
    (j : Fin data.activePhaseClasses.g)
    (q : Fin (data.activePhaseClasses.copies j)) :
    ref.representativeSectorDecomposition.weight j q =
      ref.copyWeight (ref.activeCopy j q) * ref.copyPhase (ref.activeCopy j q) := rfl

/-- The source-native BNT predicate supplies eventual simultaneous word span for the chosen
representatives.

Source: arXiv:1606.00608, lines 317--345 and Appendix C.3, lines 1848--1858. -/
theorem eventuallyRepresentativeWordTupleSpan :
    ref.representativeSectorDecomposition.EventuallyRepresentativeWordTupleSpan := by
  exact ref.representativesBNT.eventually_wordTupleSpanTop

/-- The full grouped tensor and the active representative sector tensor have equal closed-chain
coefficients at every positive length.  Inactive listed coordinates vanish because their raw
weight is zero.

Source: arXiv:1606.00608, lines 265--301 and Appendix C.3, lines 1843--1858. -/
theorem groupedTensor_sameMPV₂Pos_representativeSectorDecomposition :
    SameMPV₂Pos ref.groupedTensor ref.representativeSectorDecomposition.toTensor := by
  classical
  intro N hN σ
  let P := ref.representativeSectorDecomposition
  have hGrouped : ref.groupedTensor =
      toTensorFromBlocks (d := d) data.weights ref.regroupedBlocks := by
    funext i
    exact (ref.regroupedTensor_eq_groupedTensor i).symm
  rw [hGrouped, mpv_toTensorFromBlocks_eq_sum]
  rw [P.mpv_toTensor_eq_sum_sectors]
  simp only [smul_eq_mul]
  let f : Fin data.r → ℂ := fun k =>
    data.weights k ^ N * mpv (ref.regroupedBlocks k) σ
  have hInactive : ∑ k : data.Inactive, f k = 0 := by
    apply Fintype.sum_eq_zero
    intro k
    simp [f, not_ne_iff.mp k.property, Nat.ne_of_gt hN]
  have hSplit :=
    Fintype.sum_subtype_add_sum_subtype (fun k : Fin data.r => data.weights k ≠ 0) f
  have hActiveSum : (∑ k : Fin data.r, f k) = ∑ k : data.Active, f k := by
    rw [hInactive, add_zero] at hSplit
    exact hSplit.symm
  change (∑ k : Fin data.r, f k) =
    ∑ j : Fin data.activePhaseClasses.g,
      ∑ q : Fin (data.activePhaseClasses.copies j),
        (ref.copyWeight (ref.activeCopy j q) * ref.copyPhase (ref.activeCopy j q)) ^ N *
          mpv (data.blocks (data.activeRepresentativeIndex j)) σ
  rw [hActiveSum]
  rw [← data.activeClassCopyEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro jq _
  rcases jq with ⟨j, q⟩
  let k := ref.activeCopy j q
  change f k = _
  rw [ref.copyWeightEq]
  have hBlock := congrFun (ref.regroupedBlocksActive k) (0 : Fin d)
  rw [show ref.regroupedBlocks k = fun i => ref.copyPhase k •
      (cast (congr_arg (MPSTensor d) (ref.copyDimEq k))
        (data.blocks (data.activeRepresentativeIndex j))) i by
    simpa [k, activeCopy] using ref.regroupedBlocksActive k]
  rw [mpv_smul, mpv_cast_dim]
  ring

end MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement
