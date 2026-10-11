/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SelectiveSourcePreparation
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-!
# Reordering source registers before their vectors are supplied

A permutation of the original source positions is implemented by one allowed,
source-free word. The word is chosen before every source vector, and its exact
preparation identity holds for all vectors and every spectator input.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Word


end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P I : Type}

/-- Register layout of a prescribed ordered list of source positions. -/
def sourcePositionsLayout (r : I → PairSource P) (indices : List I) : Layout P :=
  indices.flatMap (fun i ↦ (r i).layout)

/-- Prepare the vectors at the prescribed positions, in the stated register order. -/
def prepareSourcePositions (r : I → PairSource P)
    (η : ∀ i, (r i).leftSpace ⊗[ℂ] (r i).rightSpace) :
    (indices : List I) → (ℓ : Layout P) → Word ℓ (sourcePositionsLayout r indices ++ ℓ)
  | [], ℓ => .id ℓ
  | i :: indices, ℓ =>
    .comp (prepareSourcePositions r η indices ℓ)
      (.source (r i).distinct (r i).leftSpace (r i).rightSpace (η i)
        (sourcePositionsLayout r indices ++ ℓ))

/-- The position-indexed layout is the actual source inventory layout. -/
theorem sourcePositionsLayout_eq_layout (r : I → PairSource P) (indices : List I)
    (η : ∀ i, (r i).leftSpace ⊗[ℂ] (r i).rightSpace) :
    sourcePositionsLayout r indices =
      layout (indices.map (fun i ↦ ⟨(r i).left, (r i).right, (r i).distinct,
        (r i).leftSpace, (r i).rightSpace, η i⟩)) := by
  simp [sourcePositionsLayout, layout, List.flatMap_map, PairSource.layout]

/-- Preparing a source commutes with identifying the spectator register list. -/
private theorem source_apply_heq (s : PairSource P) {a b : Layout P} (h : a = b)
    {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq ((Word.source s.distinct s.leftSpace s.rightSpace s.vector a).eval x)
      ((Word.source s.distinct s.leftSpace s.rightSpace s.vector b).eval y) := by
  cases h
  exact heq_of_eq (congrArg _ (eq_of_heq hxy))

/-- The position-indexed preparation is the actual preparation of its source records. -/
theorem eval_prepareSourcePositions_heq (r : I → PairSource P) (indices : List I)
    (η : ∀ i, (r i).leftSpace ⊗[ℂ] (r i).rightSpace) (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareSourcePositions r η indices ℓ).eval x)
      ((prepare (indices.map (fun i ↦ ⟨(r i).left, (r i).right, (r i).distinct,
        (r i).leftSpace, (r i).rightSpace, η i⟩)) ℓ).eval x) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    exact source_apply_heq
      ⟨(r i).left, (r i).right, (r i).distinct,
        (r i).leftSpace, (r i).rightSpace, η i⟩
      (congrArg (· ++ ℓ) (sourcePositionsLayout_eq_layout r indices η)) ih

/-- Concatenating position lists concatenates their register layouts. -/
theorem sourcePositionsLayout_append (r : I → PairSource P) (a b : List I) :
    sourcePositionsLayout r (a ++ b) = sourcePositionsLayout r a ++ sourcePositionsLayout r b := by
  simp [sourcePositionsLayout]

/-- Preparing concatenated positions first prepares the second block. -/
theorem eval_prepareSourcePositions_append (r : I → PairSource P) (a b : List I)
    (η : ∀ i, (r i).leftSpace ⊗[ℂ] (r i).rightSpace) (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareSourcePositions r η (a ++ b) ℓ).eval x)
      ((prepareSourcePositions r η a (sourcePositionsLayout r b ++ ℓ)).eval
        ((prepareSourcePositions r η b ℓ).eval x)) := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    exact source_apply_heq
      ⟨(r i).left, (r i).right, (r i).distinct,
        (r i).leftSpace, (r i).rightSpace, η i⟩
      (by rw [sourcePositionsLayout_append, List.append_assoc]) ih

/-- Reorder source positions by a single actual word, uniformly for every source
vector. No normalization or nonemptiness assumption is needed. -/
theorem exists_reorderSourcePositions (r : I → PairSource P)
    {indices indices' : List I} (h : indices.Perm indices') (ℓ : Layout P) :
    ∃ w : Word (sourcePositionsLayout r indices ++ ℓ) (sourcePositionsLayout r indices' ++ ℓ),
      w.IsAllowed ∧ w.sources = [] ∧
      ∀ η : ∀ i, (r i).leftSpace ⊗[ℂ] (r i).rightSpace,
        w.eval ∘L (prepareSourcePositions r η indices ℓ).eval =
          (prepareSourcePositions r η indices' ℓ).eval := by
  induction h generalizing ℓ with
  | nil =>
    exact ⟨.id ℓ, trivial, rfl, fun _ ↦ rfl⟩
  | @cons i indices indices' h ih =>
    obtain ⟨w, hw, hws, hwe⟩ := ih ℓ
    refine ⟨Word.frame ⟨(r i).left, (r i).leftSpace⟩
      (Word.frame ⟨(r i).right, (r i).rightSpace⟩ w), hw, hws, ?_⟩
    intro η
    ext1 x
    let s : PairSource P := ⟨(r i).left, (r i).right, (r i).distinct,
      (r i).leftSpace, (r i).rightSpace, η i⟩
    change (Word.frameList (layout [s]) w).eval
        ((prepare [s] (sourcePositionsLayout r indices ++ ℓ)).eval
          ((prepareSourcePositions r η indices ℓ).eval x)) =
      (prepare [s] (sourcePositionsLayout r indices' ++ ℓ)).eval
        ((prepareSourcePositions r η indices' ℓ).eval x)
    rw [eval_frameList_prepare]
    exact congrArg ((prepare [s] (sourcePositionsLayout r indices' ++ ℓ)).eval)
      (DFunLike.congr_fun (hwe η) x)
  | swap i j indices =>
    refine ⟨Word.exchangeBlocks (r j).layout (r i).layout
      (sourcePositionsLayout r indices ++ ℓ), Word.isAllowed_exchangeBlocks _ _ _,
      Word.sources_exchangeBlocks _ _ _, ?_⟩
    intro η
    ext1 x
    let s : PairSource P := ⟨(r i).left, (r i).right, (r i).distinct,
      (r i).leftSpace, (r i).rightSpace, η i⟩
    let t : PairSource P := ⟨(r j).left, (r j).right, (r j).distinct,
      (r j).leftSpace, (r j).rightSpace, η j⟩
    change (Word.exchangeBlocks (layout [t]) (layout [s])
        (sourcePositionsLayout r indices ++ ℓ)).eval
      ((prepare [t] (layout [s] ++ (sourcePositionsLayout r indices ++ ℓ))).eval
        ((prepare [s] (sourcePositionsLayout r indices ++ ℓ)).eval
          ((prepareSourcePositions r η indices ℓ).eval x))) =
      (prepare [s] (layout [t] ++ (sourcePositionsLayout r indices ++ ℓ))).eval
        ((prepare [t] (sourcePositionsLayout r indices ++ ℓ)).eval
          ((prepareSourcePositions r η indices ℓ).eval x))
    simp only [eval_prepare_eq_appendIso_symm, Word.eval_exchangeBlocks_appendIso_symm]
  | trans h h' ih ih' =>
    obtain ⟨w, hw, hws, hwe⟩ := ih ℓ
    obtain ⟨v, hv, hvs, hve⟩ := ih' ℓ
    refine ⟨.comp w v, ⟨hw, hv⟩, ?_, ?_⟩
    · simp [Word.sources, hws, hvs]
    · intro η
      rw [Word.eval_comp, ContinuousLinearMap.comp_assoc, hwe, hve]

/-- Selection keeps the original finite positions, even when source records repeat. -/
theorem selectedSources_eq_map (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (η : ∀ i, U i ⊗[ℂ] V i) :
    selectedSources R U V free η =
      ((List.finRange R.length).filter free).map (fun i ↦
        ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, U i, V i, η i⟩) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    by_cases h : free 0 = true <;>
      simp [selectedSources, List.finRange_succ, List.filter_map, h, ih,
        List.get_eq_getElem, Function.comp_def]

/-- The zero vectors fix only the spaces of the source registers. -/
def slotReference (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (i : Fin R.length) : PairSource P :=
  ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, U i, V i, 0⟩

/-- The ordered free-position layout is precisely the existing free source layout. -/
theorem sourcePositionsLayout_filter (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool) :
    sourcePositionsLayout (slotReference R U V) ((List.finRange R.length).filter free) =
      freeSlotLayout R U V free := by
  rw [sourcePositionsLayout_eq_layout _ _ (fun _ ↦ 0)]
  exact congrArg layout (selectedSources_eq_map R U V free (fun _ ↦ 0)).symm

/-- The position-indexed free preparation agrees with the actual free-slot word. -/
theorem eval_prepareSourcePositions_filter (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareSourcePositions (slotReference R U V) η
      ((List.finRange R.length).filter free) ℓ).eval x)
      ((prepareFreeSlots R U V free η ℓ).eval x) := by
  apply (eval_prepareSourcePositions_heq (slotReference R U V)
    ((List.finRange R.length).filter free) η ℓ x).trans
  change HEq ((prepare (((List.finRange R.length).filter free).map (fun i ↦
    ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, U i, V i, η i⟩)) ℓ).eval x) _
  rw [← selectedSources_eq_map]
  exact (Word.eval_castLayouts_apply_heq _ _ _ HEq.rfl).symm

/-- Preparation respects equal spectator spaces and equal spectator vectors. -/
private theorem prepareSourcePositions_apply_heq (r : I → PairSource P)
    (η : ∀ i, (r i).leftSpace ⊗[ℂ] (r i).rightSpace) (indices : List I)
    {ℓ ℓ' : Layout P} (h : ℓ = ℓ') {x : Mem ℓ} {y : Mem ℓ'} (hxy : HEq x y) :
    HEq ((prepareSourcePositions r η indices ℓ).eval x)
      ((prepareSourcePositions r η indices ℓ').eval y) := by
  cases h
  exact heq_of_eq (congrArg ((prepareSourcePositions r η indices ℓ).eval) (eq_of_heq hxy))

/-- Bring a specified subset of the free source positions to the front by one
allowed source-free word. The exact recovery holds for every source vector. -/
theorem exists_reorderFreeSlots (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free selected : Fin R.length → Bool) (ℓ : Layout P) :
    ∃ w : Word
      (freeSlotLayout R U V (fun i ↦ free i && selected i) ++
        (freeSlotLayout R U V (fun i ↦ free i && !selected i) ++ ℓ))
      (freeSlotLayout R U V free ++ ℓ),
      w.IsAllowed ∧ w.sources = [] ∧
      ∀ η : ∀ i, U i ⊗[ℂ] V i,
        w.eval ∘L (prepareFreeSlots R U V (fun i ↦ free i && selected i) η
            (freeSlotLayout R U V (fun i ↦ free i && !selected i) ++ ℓ)).eval ∘L
          (prepareFreeSlots R U V (fun i ↦ free i && !selected i) η ℓ).eval =
          (prepareFreeSlots R U V free η ℓ).eval := by
  let r := slotReference R U V
  let positions := (List.finRange R.length).filter free
  let front := (List.finRange R.length).filter (fun i ↦ free i && selected i)
  let back := (List.finRange R.length).filter (fun i ↦ free i && !selected i)
  have hp : (front ++ back).Perm positions := by
    simpa only [positions, front, back, List.filter_filter, Bool.and_comm] using
      List.filter_append_perm selected positions
  obtain ⟨w, hw, hws, hwe⟩ := exists_reorderSourcePositions r hp ℓ
  have hi : sourcePositionsLayout r (front ++ back) ++ ℓ =
      freeSlotLayout R U V (fun i ↦ free i && selected i) ++
        (freeSlotLayout R U V (fun i ↦ free i && !selected i) ++ ℓ) := by
    rw [sourcePositionsLayout_append, sourcePositionsLayout_filter,
      sourcePositionsLayout_filter, List.append_assoc]
  have ho : sourcePositionsLayout r positions ++ ℓ = freeSlotLayout R U V free ++ ℓ :=
    congrArg (· ++ ℓ) (sourcePositionsLayout_filter R U V free)
  refine ⟨w.castLayouts hi ho, ?_, ?_, ?_⟩
  · exact (Word.isAllowed_castLayouts _ _ _).mpr hw
  · simpa using hws
  · intro η
    ext1 x
    have hback := eval_prepareSourcePositions_filter R U V
      (fun i ↦ free i && !selected i) η ℓ x
    have hprepare : HEq ((prepareSourcePositions r η (front ++ back) ℓ).eval x)
        ((prepareFreeSlots R U V (fun i ↦ free i && selected i) η
          (freeSlotLayout R U V (fun i ↦ free i && !selected i) ++ ℓ)).eval
          ((prepareFreeSlots R U V (fun i ↦ free i && !selected i) η ℓ).eval x)) := by
      apply (eval_prepareSourcePositions_append r front back η ℓ x).trans
      apply (prepareSourcePositions_apply_heq r η front
        (congrArg (· ++ ℓ) (sourcePositionsLayout_filter R U V
          (fun i ↦ free i && !selected i))) hback).trans
      exact eval_prepareSourcePositions_filter R U V (fun i ↦ free i && selected i) η _ _
    apply eq_of_heq
    exact (Word.eval_castLayouts_apply_heq w hi ho hprepare.symm).trans
      ((heq_of_eq (DFunLike.congr_fun (hwe η) x)).trans
        (eval_prepareSourcePositions_filter R U V free η ℓ x))

end TNLean.PEPS.PairEffect.SourceInventory
