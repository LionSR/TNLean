/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePreparationCoordinates
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-!
# Local maps on all source slots

One fixed composition applies prescribed maps to every source halfspace. The
composition is independent of the source vectors. It therefore acts on all
source preparations at once, including sources expressed in proper Schmidt
subspaces of their ambient halfspaces.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–355 and 409–427.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-free-input-maps-word.mapsourceslots
Downstream declaration: TNLean.PEPS.PairEffect.Word.mapSourceSlots

Provenance-ID: 8769-free-input-maps-word.mapsourceslots_spec
Downstream declaration: TNLean.PEPS.PairEffect.Word.mapSourceSlots_spec

Provenance-ID: 8769-free-input-maps-word.eval_mapsourceslots_prepareslots
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_mapSourceSlots_prepareSlots
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

open SourceInventory

variable {P : Type}

/-- Apply the prescribed endpoint maps in every source slot, leaving the original
input registers untouched. This word does not depend on the source vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 409–427. -/
def Word.mapSourceSlots : (R : SourceInventory P) →
    (U V U' V' : Fin R.length → HSpace) →
    (∀ i, U i →L[ℂ] U' i) → (∀ i, V i →L[ℂ] V' i) → (ℓ : Layout P) →
    Word (slotLayout R U V ++ ℓ) (slotLayout R U' V' ++ ℓ)
  | [], _, _, _, _, _, _, ℓ => .id ℓ
  | r :: R, U, V, U', V', f, g, ℓ =>
      (Word.comp (Word.mapPair r.left r.right (f 0) (g 0)
        (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) ++ ℓ))
        (.frame ⟨r.left, U' 0⟩ (.frame ⟨r.right, V' 0⟩
          (mapSourceSlots R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
            (fun i ↦ U' i.succ) (fun i ↦ V' i.succ)
            (fun i ↦ f i.succ) (fun i ↦ g i.succ) ℓ)))).castLayouts
        (congrArg (· ++ ℓ) (slotLayout_cons r R U V).symm)
        (congrArg (· ++ ℓ) (slotLayout_cons r R U' V').symm)

/-- Endpoint contractions give an allowed composition with no pair sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem Word.mapSourceSlots_spec (R : SourceInventory P)
    (U V U' V' : Fin R.length → HSpace)
    (f : ∀ i, U i →L[ℂ] U' i) (g : ∀ i, V i →L[ℂ] V' i)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) (ℓ : Layout P) :
    (Word.mapSourceSlots R U V U' V' f g ℓ).IsAllowed ∧
      (Word.mapSourceSlots R U V U' V' f g ℓ).sources = [] := by
  induction R with
  | nil => exact ⟨trivial, rfl⟩
  | cons r R ih =>
    obtain ⟨ha, hs⟩ := Word.mapPair_spec r.left r.right (f 0) (g 0) (hf 0) (hg 0)
      (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) ++ ℓ)
    obtain ⟨hta, hts⟩ := ih (fun i ↦ U i.succ) (fun i ↦ V i.succ)
      (fun i ↦ U' i.succ) (fun i ↦ V' i.succ) (fun i ↦ f i.succ)
      (fun i ↦ g i.succ) (fun i ↦ hf i.succ) (fun i ↦ hg i.succ)
    simp only [Word.mapSourceSlots, Word.isAllowed_castLayouts,
      Word.sources_castLayouts, Word.IsAllowed, Word.sources, hs, hts,
      List.nil_append]
    exact ⟨⟨ha, hta⟩, trivial⟩

/-- An operation on spectator registers commutes with preparing the pair in front. -/
private theorem frame_pair_source (r : PairSource P) (U V : HSpace)
    (η : U ⊗[ℂ] V) {a b : Layout P} (w : Word a b) (x : Mem a) :
    (Word.frame ⟨r.left, U⟩ (Word.frame ⟨r.right, V⟩ w)).eval
      ((Word.source r.distinct U V η a).eval x) =
    (Word.source r.distinct U V η b).eval (w.eval x) := by
  exact eval_frameList_prepare [⟨r.left, r.right, r.distinct, U, V, η⟩] w x

/-- Fixed-layout preparation retains the actual preparation vector. -/
private theorem prepareSlots_heq_prepare (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i)
    (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepareSlots R U V η ℓ).eval x) (((ofSlots R U V η).prepare ℓ).eval x) := by
  exact Word.eval_castLayouts_apply_heq _ _ _ HEq.rfl

/-- Equal spectator layouts identify the vectors obtained by adjoining one source. -/
private theorem source_apply_heq (r : PairSource P) (U V : HSpace) (η : U ⊗[ℂ] V)
    {a b : Layout P} (h : a = b) {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq ((Word.source r.distinct U V η a).eval x)
      ((Word.source r.distinct U V η b).eval y) := by
  cases h
  exact heq_of_eq (congrArg _ (eq_of_heq hxy))

/-- Preparation of a nonempty source list first prepares its tail and then its head. -/
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

/-- The same source-free word transforms every source preparation by the tensor
products of its endpoint maps. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–355 and 409–427. -/
theorem Word.eval_mapSourceSlots_prepareSlots (R : SourceInventory P)
    (U V U' V' : Fin R.length → HSpace)
    (f : ∀ i, U i →L[ℂ] U' i) (g : ∀ i, V i →L[ℂ] V' i)
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) :
    (Word.mapSourceSlots R U V U' V' f g ℓ).eval ∘L (prepareSlots R U V η ℓ).eval =
      (prepareSlots R U' V' (fun i ↦ TensorProduct.mapL (f i) (g i) (η i)) ℓ).eval := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    apply ContinuousLinearMap.ext
    intro x
    apply eq_of_heq
    refine (Word.eval_castLayouts_apply_heq
      (Word.comp (Word.mapPair r.left r.right (f 0) (g 0)
        (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) ++ ℓ))
        (Word.frame ⟨r.left, U' 0⟩ (Word.frame ⟨r.right, V' 0⟩
          (Word.mapSourceSlots R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
            (fun i ↦ U' i.succ) (fun i ↦ V' i.succ)
            (fun i ↦ f i.succ) (fun i ↦ g i.succ) ℓ))))
      _ _ (prepareSlots_cons_heq r R U V η ℓ x)).trans ?_
    refine (heq_of_eq ?_).trans (prepareSlots_cons_heq r R U' V'
      (fun i ↦ TensorProduct.mapL (f i) (g i) (η i)) ℓ x).symm
    simp only [Word.eval_comp, comp_apply]
    rw [← comp_apply (Word.mapPair r.left r.right (f 0) (g 0) _).eval,
      Word.eval_mapPair_source, frame_pair_source]
    rw [← comp_apply (Word.mapSourceSlots R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
      (fun i ↦ U' i.succ) (fun i ↦ V' i.succ)
      (fun i ↦ f i.succ) (fun i ↦ g i.succ) ℓ).eval, ih]

end TNLean.PEPS.PairEffect
