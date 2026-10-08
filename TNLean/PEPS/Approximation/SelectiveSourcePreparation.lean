/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePreparationCoordinates
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-!
# Selective preparation of source registers

An ordered list of pair slots is divided into free and fixed slots. One actual
composition prepares the fixed vectors and retains the free registers in their
original positions. The composition takes no free vector as an argument. Its
operator recovers the full preparation for every choice of the free vectors,
and it is allowed whenever the fixed vectors are normalized.

Every source that is prepared is identified with its original occurrence and
its original endpoint parties. Thus a mask chosen to retain all crossing sources
leaves only internal sources to be prepared after grouping the parties.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, selective free inputs and internal preparations,
lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-selective-prep-sourceinventory.selectedsources
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.selectedSources

Provenance-ID: 8769-selective-prep-sourceinventory.layout_selectedsources_eq
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.layout_selectedSources_eq

Provenance-ID: 8769-selective-prep-sourceinventory.freeslotlayout
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.freeSlotLayout

Provenance-ID: 8769-selective-prep-sourceinventory.prepareselected
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.prepareSelected

Provenance-ID: 8769-selective-prep-sourceinventory.preparefreeslots
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.prepareFreeSlots

Provenance-ID: 8769-selective-prep-sourceinventory.fillsourcevectors
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.fillSourceVectors

Provenance-ID: 8769-selective-prep-sourceinventory.isallowed_prepareselected
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.isAllowed_prepareSelected

Provenance-ID: 8769-selective-prep-sourceinventory.sources_prepareselected
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.sources_prepareSelected

Provenance-ID: 8769-selective-prep-sourceinventory.eval_prepareselected_preparefreeslots
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSelected_prepareFreeSlots

Provenance-ID: 8769-selective-prep-sourceinventory.mem_selectedsources
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.mem_selectedSources

Provenance-ID: 8769-selective-prep-sourceinventory.mem_sources_prepareselected
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.mem_sources_prepareSelected
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- Select original source occurrences without changing their order.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def selectedSources : (R : SourceInventory P) → (U V : Fin R.length → HSpace) →
    (Fin R.length → Bool) → (∀ i, U i ⊗[ℂ] V i) → SourceInventory P
  | [], _, _, _, _ => []
  | r :: R, U, V, free, ζ =>
    let tail := selectedSources R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
      (fun i ↦ free i.succ) (fun i ↦ ζ i.succ)
    if free 0 then ⟨r.left, r.right, r.distinct, U 0, V 0, ζ 0⟩ :: tail else tail

/-- The selected register layout is independent of the prepared vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem layout_selectedSources_eq (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (ζ ξ : ∀ i, U i ⊗[ℂ] V i) :
    (selectedSources R U V free ζ).layout = (selectedSources R U V free ξ).layout := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    simp only [selectedSources]
    split
    · simp only [layout_cons, PairSource.layout]
      rw [ih]
    · exact ih _ _ _ _ _

/-- The original-order layout of the source slots left free.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def freeSlotLayout (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) : Layout P :=
  (selectedSources R U V free (fun _ ↦ 0)).layout

/-- The free layout retains the head registers exactly when its mask is true. -/
private theorem freeSlotLayout_cons (r : PairSource P) (R : SourceInventory P)
    (U V : Fin (r :: R).length → HSpace) (free : Fin (r :: R).length → Bool) :
    freeSlotLayout (r :: R) U V free =
      if free 0 then ⟨r.left, U 0⟩ :: ⟨r.right, V 0⟩ ::
        freeSlotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) (fun i ↦ free i.succ)
      else freeSlotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
        (fun i ↦ free i.succ) := by
  simp only [freeSlotLayout, selectedSources]
  split <;> rfl

/-- Prepare only the fixed sources, leaving every selected register free.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def prepareSelected : (R : SourceInventory P) → (U V : Fin R.length → HSpace) →
    (free : Fin R.length → Bool) → (∀ i, free i = false → U i ⊗[ℂ] V i) →
    (ℓ : Layout P) → Word (freeSlotLayout R U V free ++ ℓ) (slotLayout R U V ++ ℓ)
  | [], _, _, _, _, ℓ => .id ℓ
  | r :: R, U, V, free, fixed, ℓ => by
    let tail := prepareSelected R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
      (fun i ↦ free i.succ) (fun i h ↦ fixed i.succ h) ℓ
    by_cases h : free 0 = true
    · exact (Word.frame ⟨r.left, U 0⟩ (Word.frame ⟨r.right, V 0⟩ tail)).castLayouts
        (by simp [freeSlotLayout_cons, h])
        (congrArg (· ++ ℓ) (slotLayout_cons r R U V).symm)
    · exact (Word.comp tail
        (Word.source r.distinct (U 0) (V 0) (fixed 0 (Bool.eq_false_iff.mpr h))
          (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) ++ ℓ))).castLayouts
        (by simp [freeSlotLayout_cons, h])
        (congrArg (· ++ ℓ) (slotLayout_cons r R U V).symm)

/-- Prepare an arbitrary vector in each free source slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def prepareFreeSlots (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (ζ : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) :
    Word ℓ (freeSlotLayout R U V free ++ ℓ) :=
  ((selectedSources R U V free ζ).prepare ℓ).castLayouts rfl
    (congrArg (· ++ ℓ) (layout_selectedSources_eq R U V free ζ (fun _ ↦ 0)))

/-- The fixed vectors and the arbitrary free vectors fill all original slots.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def fillSourceVectors (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i)
    (ζ : ∀ i, U i ⊗[ℂ] V i) (i : Fin R.length) : U i ⊗[ℂ] V i :=
  if h : free i = false then fixed i h else ζ i


/-- Only the fixed vectors need to be normalized.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem isAllowed_prepareSelected (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i)
    (hfixed : ∀ i h, ‖fixed i h‖ = 1) (ℓ : Layout P) :
    (prepareSelected R U V free fixed ℓ).IsAllowed := by
  induction R with
  | nil => trivial
  | cons r R ih =>
    simp only [prepareSelected]
    split
    · rw [Word.isAllowed_castLayouts]
      exact ih _ _ _ _ (fun i h ↦ hfixed i.succ h)
    · rw [Word.isAllowed_castLayouts]
      exact ⟨ih _ _ _ _ (fun i h ↦ hfixed i.succ h), hfixed _ _⟩

/-- The source occurrences are exactly the fixed original slots, in their order.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem sources_prepareSelected (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i) (ℓ : Layout P) :
    (prepareSelected R U V free fixed ℓ).sources =
      selectedSources R U V (fun i ↦ !free i)
        (fillSourceVectors R U V free fixed (fun _ ↦ 0)) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    simp only [prepareSelected]
    split <;> rename_i h
    · simp [Word.sources_castLayouts, Word.sources, selectedSources,
        fillSourceVectors, h, ih]
      rfl
    · simp [Word.sources_castLayouts, Word.sources, selectedSources,
        fillSourceVectors, Bool.eq_false_iff.mpr h, ih]
      rfl

/-- A canonical layout cast identifies the same vector in equal memories. -/
private theorem memCongr_apply_heq {a b : Layout P} (h : a = b) (x : Mem a) :
    HEq (Layout.memCongr h x) x := by
  cases h
  rfl

/-- Preparation in fixed slots identifies the actual inventory preparation. -/
private theorem prepareSlots_heq_prepare (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i)
    (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareSlots R U V η ℓ).eval x) (((ofSlots R U V η).prepare ℓ).eval x) := by
  rw [prepareSlots, Word.eval_castLayouts]
  exact memCongr_apply_heq _ _

/-- Adjoining a source respects equality of the spectator layout. -/
private theorem source_apply_heq (r : PairSource P) (U V : HSpace) (η : U ⊗[ℂ] V)
    {a b : Layout P} (h : a = b) {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq ((Word.source r.distinct U V η a).eval x)
      ((Word.source r.distinct U V η b).eval y) := by
  cases h
  exact heq_of_eq (congrArg _ (eq_of_heq hxy))

/-- Full preparation first prepares the tail and then its head source. -/
private theorem prepareSlots_cons_heq (r : PairSource P) (R : SourceInventory P)
    (U V : Fin (r :: R).length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i)
    (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareSlots (r :: R) U V η ℓ).eval x)
      ((Word.source r.distinct (U 0) (V 0) (η 0)
        (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) ++ ℓ)).eval
        ((prepareSlots R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ η i.succ) ℓ).eval x)) := by
  apply (prepareSlots_heq_prepare (r :: R) U V η ℓ x).trans
  rw [ofSlots_cons]
  exact source_apply_heq r (U 0) (V 0) (η 0)
    (congrArg (· ++ ℓ) (layout_ofSlots_eq R (fun i ↦ U i.succ)
      (fun i ↦ V i.succ) (fun i ↦ η i.succ) (fun _ ↦ 0)))
    (prepareSlots_heq_prepare R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
      (fun i ↦ η i.succ) ℓ x).symm

/-- Free-slot preparation identifies the selected inventory preparation. -/
private theorem prepareFreeSlots_heq_prepare (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (ζ : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareFreeSlots R U V free ζ ℓ).eval x)
      (((selectedSources R U V free ζ).prepare ℓ).eval x) := by
  exact Word.eval_castLayouts_apply_heq _ _ _ HEq.rfl

/-- A free head is prepared before the other selected source registers. -/
private theorem prepareFreeSlots_cons_true_heq (r : PairSource P)
    (R : SourceInventory P) (U V : Fin (r :: R).length → HSpace)
    (free : Fin (r :: R).length → Bool) (h : free 0 = true)
    (ζ : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareFreeSlots (r :: R) U V free ζ ℓ).eval x)
      ((Word.source r.distinct (U 0) (V 0) (ζ 0)
        (freeSlotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ free i.succ) ++ ℓ)).eval
        ((prepareFreeSlots R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ free i.succ) (fun i ↦ ζ i.succ) ℓ).eval x)) := by
  apply (prepareFreeSlots_heq_prepare (r :: R) U V free ζ ℓ x).trans
  rw [selectedSources, ite_eq_left h]
  exact source_apply_heq r (U 0) (V 0) (ζ 0)
    (congrArg (· ++ ℓ) (layout_selectedSources_eq R (fun i ↦ U i.succ)
      (fun i ↦ V i.succ) (fun i ↦ free i.succ) (fun i ↦ ζ i.succ) (fun _ ↦ 0)))
    (prepareFreeSlots_heq_prepare R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
      (fun i ↦ free i.succ) (fun i ↦ ζ i.succ) ℓ x).symm

/-- A fixed head contributes no register to the free preparation. -/
private theorem prepareFreeSlots_cons_false_heq (r : PairSource P)
    (R : SourceInventory P) (U V : Fin (r :: R).length → HSpace)
    (free : Fin (r :: R).length → Bool) (h : free 0 = false)
    (ζ : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareFreeSlots (r :: R) U V free ζ ℓ).eval x)
      ((prepareFreeSlots R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
        (fun i ↦ free i.succ) (fun i ↦ ζ i.succ) ℓ).eval x) := by
  apply (prepareFreeSlots_heq_prepare (r :: R) U V free ζ ℓ x).trans
  rw [selectedSources, ite_eq_right (by simp [h])]
  exact (prepareFreeSlots_heq_prepare R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
      (fun i ↦ free i.succ) (fun i ↦ ζ i.succ) ℓ x).symm


/-- A spectator operation commutes with preparation of the pair in front. -/
private theorem frame_pair_source (r : PairSource P) (U V : HSpace)
    (η : U ⊗[ℂ] V) {a b : Layout P} (w : Word a b) (x : Mem a) :
    (Word.frame ⟨r.left, U⟩ (Word.frame ⟨r.right, V⟩ w)).eval
      ((Word.source r.distinct U V η a).eval x) =
    (Word.source r.distinct U V η b).eval (w.eval x) := by
  exact eval_frameList_prepare [⟨r.left, r.right, r.distinct, U, V, η⟩] w x

/-- One fixed word reconstructs preparation for every family of free vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem eval_prepareSelected_prepareFreeSlots (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i)
    (ζ : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) :
    (prepareSelected R U V free fixed ℓ).eval ∘L (prepareFreeSlots R U V free ζ ℓ).eval =
      (prepareSlots R U V (fillSourceVectors R U V free fixed ζ) ℓ).eval := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    ext x
    apply eq_of_heq
    simp only [prepareSelected]
    split <;> rename_i h
    · refine (Word.eval_castLayouts_apply_heq
        (Word.frame ⟨r.left, U 0⟩ (Word.frame ⟨r.right, V 0⟩
          (prepareSelected R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
            (fun i ↦ free i.succ) (fun i h ↦ fixed i.succ h) ℓ))) _ _
        (prepareFreeSlots_cons_true_heq r R U V free h ζ ℓ x)).trans ?_
      have hout := prepareSlots_cons_heq r R U V
        (fillSourceVectors (r :: R) U V free fixed ζ) ℓ x
      have hzero : fillSourceVectors (r :: R) U V free fixed ζ 0 = ζ 0 := by
        simp [fillSourceVectors, h]
      rw [hzero] at hout
      refine (heq_of_eq ?_).trans hout.symm
      rw [frame_pair_source]
      rw [← comp_apply (prepareSelected R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
        (fun i ↦ free i.succ) (fun i h ↦ fixed i.succ h) ℓ).eval, ih]
      rfl
    · refine (Word.eval_castLayouts_apply_heq
        (Word.comp
          (prepareSelected R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
            (fun i ↦ free i.succ) (fun i h ↦ fixed i.succ h) ℓ)
          (Word.source r.distinct (U 0) (V 0) (fixed 0 (Bool.eq_false_iff.mpr h))
            (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) ++ ℓ))) _ _
        (prepareFreeSlots_cons_false_heq r R U V free (Bool.eq_false_iff.mpr h)
          ζ ℓ x)).trans ?_
      have hout := prepareSlots_cons_heq r R U V
        (fillSourceVectors (r :: R) U V free fixed ζ) ℓ x
      have hzero : fillSourceVectors (r :: R) U V free fixed ζ 0 =
          fixed 0 (Bool.eq_false_iff.mpr h) := by
        simp [fillSourceVectors, Bool.eq_false_iff.mpr h]
      rw [hzero] at hout
      refine (heq_of_eq ?_).trans hout.symm
      simp only [Word.eval_comp, comp_apply]
      rw [← comp_apply (prepareSelected R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
        (fun i ↦ free i.succ) (fun i h ↦ fixed i.succ h) ℓ).eval, ih]
      rfl

/-- Membership identifies the selected original slot and retains its endpoint
parties, halfspaces, and vector.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem mem_selectedSources (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (ζ : ∀ i, U i ⊗[ℂ] V i) (s : PairSource P) :
    s ∈ selectedSources R U V free ζ ↔ ∃ i : Fin R.length, free i = true ∧
      s = ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, U i, V i, ζ i⟩ := by
  induction R with
  | nil => simp [selectedSources]
  | cons r R ih =>
    by_cases h : free 0 = true
    all_goals simp [selectedSources, h, Fin.exists_fin_succ, ih]

/-- Each prepared source is one fixed original slot, with its original endpoints.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem mem_sources_prepareSelected (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i) (ℓ : Layout P) (s : PairSource P) :
    s ∈ (prepareSelected R U V free fixed ℓ).sources ↔
      ∃ i : Fin R.length, ∃ h : free i = false,
        s = ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, U i, V i, fixed i h⟩ := by
  rw [sources_prepareSelected, mem_selectedSources]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have h : free i = false := by simpa using hi
    exact ⟨i, h, by simp [fillSourceVectors, h]⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, by simp [h], by simp [fillSourceVectors, h]⟩

end TNLean.PEPS.PairEffect.SourceInventory
