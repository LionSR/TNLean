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
import TNLean.MPS.Tactic.Basic

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

/-- The source-native BNT predicate supplies eventual simultaneous word span for the chosen
representatives.

Source: arXiv:1606.00608, lines 317--345 and Appendix C.3, lines 1848--1858. -/
theorem eventuallyRepresentativeWordTupleSpan :
    ref.representativeSectorDecomposition.EventuallyRepresentativeWordTupleSpan := by
  exact ref.representativesBNT.eventually_wordTupleSpanTop

private theorem trace_cast_mul_evalWord_cast
    {n m : ℕ} (h : n = m) (C : MPSTensor e n) (B : MPSTensor d n)
    (s : Fin e) (w : List (Fin d)) :
    Matrix.trace
        ((cast (congr_arg (MPSTensor e) h) C) s *
          evalWord (cast (congr_arg (MPSTensor d) h) B) w) =
      Matrix.trace (C s * evalWord B w) := by
  subst m
  rfl

/-- Full listed-coordinate marked blocks.  An active copy is the chosen representative mark
scaled by its raw weight and phase; an inactive listed coordinate is the zero block. -/
noncomputable def groupedMarkedBlocks
    (C : (j : Fin data.activePhaseClasses.g) →
      MPSTensor e (data.dim (data.activeRepresentativeIndex j))) :
    (k : Fin data.r) → MPSTensor e (data.dim k) := fun k =>
  if hk : data.weights k ≠ 0 then
    let ka : data.Active := ⟨k, hk⟩
    (data.weights k * ref.copyPhase ka) •
      cast (congr_arg (MPSTensor e) (ref.copyDimEq ka))
        (C (data.activeClassCopy ka).1)
  else fun _ => 0

/-- On an active listed coordinate, the marked block carries the raw weight and phase. -/
@[simp] theorem groupedMarkedBlocks_active
    (C : (j : Fin data.activePhaseClasses.g) →
      MPSTensor e (data.dim (data.activeRepresentativeIndex j)))
    (k : data.Active) :
    ref.groupedMarkedBlocks C k =
      (data.weights k * ref.copyPhase k) •
        cast (congr_arg (MPSTensor e) (ref.copyDimEq k))
          (C (data.activeClassCopy k).1) := by
  simp [groupedMarkedBlocks, k.property]

/-- The grouped marked tensor on all retained listed coordinates.

Active marks carry the factor `ν * ζ`, including the phase at the marked site.  Inactive
listed coordinates remain present as zero blocks.  Consequently a marked chain with tail
length `L` has active-copy coefficient `(ν * ζ)^(L+1)`.

Source: arXiv:1606.00608, Appendix C.3, lines 1835--1858 and the marked application at
lines 1909--1919. -/
noncomputable def groupedMarkedTensor
    (C : (j : Fin data.activePhaseClasses.g) →
      MPSTensor e (data.dim (data.activeRepresentativeIndex j))) :
    MPSTensor e (∑ k : Fin data.r, data.dim k) :=
  toTensorFromBlocks (d := e) (fun _ : Fin data.r => (1 : ℂ)) (ref.groupedMarkedBlocks C)

private theorem trace_groupedMarkedTensor_mul_evalWord_eq_sum
    (C : (j : Fin data.activePhaseClasses.g) →
      MPSTensor e (data.dim (data.activeRepresentativeIndex j)))
    (s : Fin e) (w : List (Fin d)) :
    Matrix.trace (ref.groupedMarkedTensor C s * evalWord ref.groupedTensor w) =
      ∑ k : Fin data.r, Matrix.trace
        (ref.groupedMarkedBlocks C k s *
          (data.weights k ^ w.length • evalWord (ref.regroupedBlocks k) w)) := by
  classical
  have hGrouped : ref.groupedTensor =
      toTensorFromBlocks (d := d) data.weights ref.regroupedBlocks := by
    funext i
    exact (ref.regroupedTensor_eq_groupedTensor i).symm
  rw [hGrouped, groupedMarkedTensor, evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal]
  rw [toTensorFromBlocks]
  change Matrix.trace
      ((Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv)
          (Matrix.blockDiagonal' fun k : Fin data.r =>
            (1 : ℂ) • ref.groupedMarkedBlocks C k s) *
        (Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv)
          (Matrix.blockDiagonal' fun k : Fin data.r =>
            data.weights k ^ w.length • evalWord (ref.regroupedBlocks k) w)) = _
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ finSigmaFinEquiv
    finSigmaFinEquiv finSigmaFinEquiv]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [Matrix.trace_reindex, ← Matrix.blockDiagonal'_mul,
    Matrix.trace_blockDiagonal']
  simp only [one_smul, Algebra.mul_smul_comm, Matrix.trace_smul, smul_eq_mul]

/-- Exact closed-chain trace identity from the full grouped marked tensor to the active
representative sector marked tensor.

The mark supplies one factor `ν * ζ` and each tail site supplies another, so a copy contributes
`(ν * ζ)^(|w|+1)`.  Inactive listed coordinates contribute zero.

Source: arXiv:1606.00608, Appendix C.3, lines 1843--1858 and 1909--1919. -/
theorem trace_groupedMarkedTensor_eq_representative_markedTensor
    (C : (j : Fin data.activePhaseClasses.g) →
      MPSTensor e (data.dim (data.activeRepresentativeIndex j)))
    (s : Fin e) (w : List (Fin d)) :
    Matrix.trace (ref.groupedMarkedTensor C s * evalWord ref.groupedTensor w) =
      Matrix.trace
        (ref.representativeSectorDecomposition.markedTensor C s *
          evalWord ref.representativeSectorDecomposition.toTensor w) := by
  classical
  let P := ref.representativeSectorDecomposition
  rw [ref.trace_groupedMarkedTensor_mul_evalWord_eq_sum C s w]
  rw [P.trace_markedTensor_mul_evalWord C s w]
  let f : Fin data.r → ℂ := fun k => Matrix.trace
    (ref.groupedMarkedBlocks C k s *
      (data.weights k ^ w.length • evalWord (ref.regroupedBlocks k) w))
  have hInactive : ∑ k : data.Inactive, f k = 0 := by
    apply Fintype.sum_eq_zero
    intro k
    simp [f, groupedMarkedBlocks, not_ne_iff.mp k.property]
  have hSplit :=
    Fintype.sum_subtype_add_sum_subtype (fun k : Fin data.r => data.weights k ≠ 0) f
  have hActiveSum : (∑ k : Fin data.r, f k) = ∑ k : data.Active, f k := by
    rw [hInactive, add_zero] at hSplit
    exact hSplit.symm
  change (∑ k : Fin data.r, f k) =
    ∑ j : Fin data.activePhaseClasses.g,
      P.coeff (w.length + 1) j *
        Matrix.trace
          (C j s * evalWord (data.blocks (data.activeRepresentativeIndex j)) w)
  rw [hActiveSum]
  calc
    (∑ k : data.Active, f k) =
        ∑ jq : Σ j : Fin data.activePhaseClasses.g,
          Fin (data.activePhaseClasses.copies j),
          f (data.activeClassCopyEquiv jq) :=
      (data.activeClassCopyEquiv.sum_comp (fun k : data.Active => f k)).symm
    _ = ∑ j : Fin data.activePhaseClasses.g,
        ∑ q : Fin (data.activePhaseClasses.copies j),
          (ref.copyWeight (activeCopy (data := data) j q) *
            ref.copyPhase (activeCopy (data := data) j q)) ^ (w.length + 1) *
            Matrix.trace
              (C j s * evalWord
                (data.blocks (data.activeRepresentativeIndex j)) w) := by
      rw [← Fintype.sum_sigma']
      apply Finset.sum_congr rfl
      intro jq _
      rcases jq with ⟨j, q⟩
      let k : data.Active := activeCopy (data := data) j q
      change f k = _
      have hkclass : data.activeClassCopy k = ⟨j, q⟩ := by
        simpa [k, activeCopy] using data.activeClassCopy_activeClassCopyEquiv j q
      have hkfst : (data.activeClassCopy k).1 = j := congrArg Sigma.fst hkclass
      have hTraceRepresentative :
          Matrix.trace
              (C (data.activeClassCopy k).1 s *
                evalWord
                  (data.blocks
                    (data.activeRepresentativeIndex (data.activeClassCopy k).1)) w) =
            Matrix.trace
              (C j s * evalWord
                (data.blocks (data.activeRepresentativeIndex j)) w) := by
        rw [hkfst]
      change Matrix.trace
          (ref.groupedMarkedBlocks C k s *
            (data.weights k ^ w.length • evalWord (ref.regroupedBlocks k) w)) = _
      rw [ref.groupedMarkedBlocks_active C k, ref.copyWeightEq]
      rw [ref.regroupedBlocksActive k, evalWord_smul]
      simp only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_smul, smul_eq_mul]
      rw [trace_cast_mul_evalWord_cast (ref.copyDimEq k), hTraceRepresentative]
      rw [pow_succ']
      ring
    _ = ∑ j : Fin data.activePhaseClasses.g,
        P.coeff (w.length + 1) j *
          Matrix.trace
            (C j s * evalWord (data.blocks (data.activeRepresentativeIndex j)) w) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      rfl


/-- Representative-grouped marked Lemma L for a literal CPSV active refinement.

This is the algebraic arbitrary-marked-letter extension of the source's
physical first-site statement.  If the full-coordinate grouped marked
closed-chain traces agree at every positive tail length, then the two marks
agree on every chosen normal representative.  The inactive listed coordinates
remain present in the hypothesis and vanish through their zero marked blocks.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858 and the marked use at
lines 1909--1919. -/
theorem groupedMarkedTensor_basis_eq_of_trace_agree
    (C E : (j : Fin data.activePhaseClasses.g) →
      MPSTensor e (data.dim (data.activeRepresentativeIndex j)))
    (hTrace : ∀ (L : ℕ), 0 < L → ∀ (s : Fin e) (w : Fin L → Fin d),
      Matrix.trace
          (ref.groupedMarkedTensor C s * evalWord ref.groupedTensor (List.ofFn w)) =
        Matrix.trace
          (ref.groupedMarkedTensor E s * evalWord ref.groupedTensor (List.ofFn w))) :
    ∀ j, C j = E j := by
  let P := ref.representativeSectorDecomposition
  apply P.markedTensor_basis_eq_of_trace_agree C E
    ref.eventuallyRepresentativeWordTupleSpan
  intro L hL s w
  rw [← ref.trace_groupedMarkedTensor_eq_representative_markedTensor C s (List.ofFn w)]
  rw [← ref.trace_groupedMarkedTensor_eq_representative_markedTensor E s (List.ofFn w)]
  exact hTrace L hL s w

/-- Physical first-site Lemma L on every chosen representative of a literal CPSV active
refinement.

First-site agreement on the full grouped tensor passes across its positive-length MPV equality
with the active representative sector tensor.  Eventual representative word span then separates
the insertion on each normal representative.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858, as used at
lines 1874--1887. -/
theorem insertedTensor_representative_eq_of_firstSiteActionAgree
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree ref.groupedTensor Y Z) :
    ∀ j : Fin data.activePhaseClasses.g,
      insertedTensor Y (data.blocks (data.activeRepresentativeIndex j)) =
        insertedTensor Z (data.blocks (data.activeRepresentativeIndex j)) := by
  exact SectorDecomposition.insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree
    ref.groupedTensor ref.representativeSectorDecomposition
    ref.groupedTensor_sameMPV₂Pos_representativeSectorDecomposition
    ref.eventuallyRepresentativeWordTupleSpan hAct


end MPSTensor.CPSVCanonicalFormData.ActiveBNTRefinement
