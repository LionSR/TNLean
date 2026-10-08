/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceInputPartition

/-!
# Source vectors and framed input preparations

Uniform source reordering and source preparation identify the original partial
circuit vector with the absorbed word on its literal corrected and crossing
source inputs. No desired vector identity or factorization is assumed.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-sourcepreparationvectors-01
TNLean.PEPS.PairEffect.SourceInventory.eval_framed_freeSourceVectors
Provenance-ID: 8769-source-resource-sourcepreparationvectors-02
TNLean.PEPS.PairEffect.SourceInventory.eval_framed_sourceVector
Provenance-ID: 8769-source-resource-sourcepreparationvectors-03
TNLean.PEPS.PairEffect.SourceInventory.eval_prepareFreeSlots_nil_heq
Provenance-ID: 8769-source-resource-sourcepreparationvectors-04
TNLean.PEPS.PairEffect.SourceInventory.eval_prepare_nil_heq
Provenance-ID: 8769-source-resource-sourcepreparationvectors-05
TNLean.PEPS.PairEffect.SourceInventory.eval_reordered_prepared_vector
Provenance-ID: 8769-source-resource-sourcepreparationvectors-06
TNLean.PEPS.PairEffect.SourceInventory.preparedReorderedWord
Provenance-ID: 8769-source-resource-sourcepreparationvectors-07
TNLean.PEPS.PairEffect.SourceInventory.sourceVectorPair
Provenance-ID: 8769-source-resource-sourcepreparationvectors-08
TNLean.PEPS.PairEffect.SourceInventory.vector_append_eq
Provenance-ID: 8769-source-resource-sourcepreparationvectors-09
TNLean.PEPS.PairEffect.SourceInventory.vector_append_heq
Provenance-ID: 8769-source-resource-sourcepreparationvectors-10
TNLean.PEPS.PairEffect.Word.eval_source_apply_heq
-/


noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Word

/-- A source operation respects equality of the spectator register list and vector. -/
theorem eval_source_apply_heq {P : Type} (s : PairSource P) {a b : Layout P} (h : a = b)
    {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq ((source s.distinct s.leftSpace s.rightSpace s.vector a).eval x)
      ((source s.distinct s.leftSpace s.rightSpace s.vector b).eval y) := by
  cases h
  exact heq_of_eq (congrArg _ (eq_of_heq hxy))

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- Preparing a source inventory on the scalar unit produces its actual joint vector. -/
theorem eval_prepare_nil_heq (S : SourceInventory P) :
    HEq ((prepare S []).eval (1 : ℂ)) (vector S) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    exact Word.eval_source_apply_heq s (List.append_nil _) ih


/-- Preparation preserves equality of the spectator register list and input. -/
private theorem prepare_apply_heq (S : SourceInventory P) {a b : Layout P} (h : a = b)
    {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq ((prepare S a).eval x) ((prepare S b).eval y) := by
  cases h
  exact heq_of_eq (congrArg ((prepare S a).eval) (eq_of_heq hxy))

/-- The actual joint vector of two inventories is their canonical tensor product. -/
theorem vector_append_heq (S T : SourceInventory P) :
    HEq (vector (S ++ T))
      ((appendIso S.layout T.layout).symm (vector S ⊗ₜ[ℂ] vector T)) := by
  apply (eval_prepare_nil_heq (S ++ T)).symm.trans
  apply (eval_prepare_append S T [] (1 : ℂ)).trans
  apply (prepare_apply_heq S (List.append_nil _) (eval_prepare_nil_heq T)).trans
  exact heq_of_eq (eval_prepare_eq_appendIso_symm S T.layout (vector T))

/-- Preparing free slots on the scalar unit gives their fixed-layout source vector. -/
theorem eval_prepareFreeSlots_nil_heq (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (η : ∀ i, U i ⊗[ℂ] V i) :
    HEq ((prepareFreeSlots R U V free η []).eval (1 : ℂ))
      (freeSourceVector R U V free η) := by
  exact (Word.eval_castLayouts_apply_heq _ _ _ HEq.rfl).trans
    ((eval_prepare_nil_heq (selectedSources R U V free η)).trans
      (Layout.memCongr_apply_heq _ _).symm)

/-- Framing preserves equality of the source register list and its input vector. -/
private theorem frameList_apply_heq {a b : Layout P} (w : Word a b)
    {L K : Layout P} (h : L = K)
    {x : Mem (L ++ a)} {y : Mem (K ++ a)} (hxy : HEq x y) :
    HEq ((Word.frameList L w).eval x) ((Word.frameList K w).eval y) := by
  cases h
  exact heq_of_eq (congrArg ((Word.frameList L w).eval) (eq_of_heq hxy))

/-- Framing an actual scalar-input preparation under a fixed source layout
prepares the original input after those exact source vectors. -/
theorem eval_framed_sourceVector {ℓ L : Layout P} (p : Word [] ℓ)
    (S : SourceInventory P) (h : S.layout = L) :
    ((Word.frameList L p).castLayouts (List.append_nil L) rfl).eval
        (Layout.memCongr h (vector S)) =
      Layout.memCongr (congrArg (· ++ ℓ) h) ((prepare S ℓ).eval (p.eval 1)) := by
  rw [Word.eval_castLayouts]
  change (Word.frameList L p).eval
      ((Layout.memCongr (List.append_nil L)).symm (Layout.memCongr h (vector S))) = _
  have hin := Layout.memCongr_apply_heq (List.append_nil L)
    ((Layout.memCongr (List.append_nil L)).symm (Layout.memCongr h (vector S)))
  rw [LinearIsometryEquiv.apply_symm_apply] at hin
  apply eq_of_heq
  exact (frameList_apply_heq p h.symm
    (hin.symm.trans ((Layout.memCongr_apply_heq h (vector S)).trans
      (eval_prepare_nil_heq S).symm))).trans
      ((heq_of_eq (eval_frameList_prepare S p (1 : ℂ))).trans
        (Layout.memCongr_apply_heq (congrArg (· ++ ℓ) h) _).symm)

/-- The joint vector in fixed register layouts is the canonical tensor of its two blocks. -/
theorem vector_append_eq {C D : Layout P} (S T : SourceInventory P)
    (hS : S.layout = C) (hT : T.layout = D) :
    Layout.memCongr (by rw [layout_append, hS, hT] : (S ++ T).layout = C ++ D)
        (vector (S ++ T)) =
      (appendIso C D).symm
        (Layout.memCongr hS (vector S) ⊗ₜ[ℂ] Layout.memCongr hT (vector T)) := by
  cases hS
  cases hT
  exact eq_of_heq ((Layout.memCongr_apply_heq _ _).trans (vector_append_heq S T))

/-- A framed scalar-input preparation acts after two literal source-vector blocks. -/
theorem eval_framed_freeSourceVectors (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (first second : Fin R.length → Bool)
    (η ζ : ∀ i, U i ⊗[ℂ] V i) {ℓ : Layout P} (p : Word [] ℓ) :
    let C := freeSlotLayout R U V first
    let T := freeSlotLayout R U V second
    ((Word.frameList (C ++ T) p).castLayouts
      (List.append_nil _) (List.append_assoc C T ℓ)).eval
        ((appendIso C T).symm
          (freeSourceVector R U V first η ⊗ₜ[ℂ] freeSourceVector R U V second ζ)) =
      (prepareFreeSlots R U V first η (T ++ ℓ)).eval
        ((prepareFreeSlots R U V second ζ ℓ).eval (p.eval 1)) := by
  intro C T
  let S := selectedSources R U V first η
  let D := selectedSources R U V second ζ
  have hS : S.layout = C := layout_selectedSources_eq R U V first η (fun _ ↦ 0)
  have hD : D.layout = T := layout_selectedSources_eq R U V second ζ (fun _ ↦ 0)
  have hSD : (S ++ D).layout = C ++ T := by rw [layout_append, hS, hD]
  have hv := vector_append_eq S D hS hD
  change Layout.memCongr hSD (vector (S ++ D)) =
    (appendIso C T).symm (freeSourceVector R U V first η ⊗ₜ[ℂ]
      freeSourceVector R U V second ζ) at hv
  rw [← hv, Word.eval_castLayouts]
  have hf := eval_framed_sourceVector p (S ++ D) hSD
  rw [Word.eval_castLayouts] at hf
  change (Word.frameList (C ++ T) p).eval
    ((Layout.memCongr (List.append_nil (C ++ T))).symm
      (Layout.memCongr hSD (vector (S ++ D)))) = _ at hf
  change Layout.memCongr (List.append_assoc C T ℓ)
    ((Word.frameList (C ++ T) p).eval
      ((Layout.memCongr (List.append_nil (C ++ T))).symm
        (Layout.memCongr hSD (vector (S ++ D))))) = _
  rw [hf]
  apply eq_of_heq
  apply ((Layout.memCongr_apply_heq _ _).trans (Layout.memCongr_apply_heq _ _)).trans
  apply (eval_prepare_append S D ℓ (p.eval 1)).trans
  apply (prepare_apply_heq S (congrArg (· ++ ℓ) hD)
    (Word.eval_castLayouts_apply_heq _ _ _ HEq.rfl).symm).trans
  exact (Word.eval_castLayouts_apply_heq _ _ _ HEq.rfl).symm

/-- Concatenate the two literal source-vector blocks in their fixed order. -/
def sourceVectorPair (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (first second : Fin R.length → Bool) (η : ∀ i, U i ⊗[ℂ] V i) :
    Mem (freeSlotLayout R U V first ++ freeSlotLayout R U V second) :=
  (appendIso _ _).symm
    (freeSourceVector R U V first η ⊗ₜ[ℂ] freeSourceVector R U V second η)

/-- The actual composite of framed input preparation, register rearrangement,
fixed source preparation, and the residual word. -/
def preparedReorderedWord (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (first second free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i)
    {ℓ out : Layout P} (p : Word [] ℓ) (v : Word (slotLayout R U V ++ ℓ) out)
    (u : Word (freeSlotLayout R U V first ++ (freeSlotLayout R U V second ++ ℓ))
      (freeSlotLayout R U V free ++ ℓ)) :
    Word (freeSlotLayout R U V first ++ freeSlotLayout R U V second) out :=
  let C := freeSlotLayout R U V first
  let T := freeSlotLayout R U V second
  let pf := (Word.frameList (C ++ T) p).castLayouts
    (List.append_nil _) (List.append_assoc C T ℓ)
  .comp (.comp pf u) (.comp (prepareSelected R U V free fixed ℓ) v)

/-- A uniform register rearrangement turns two source-vector blocks into the
full preparation, while a fixed preparation supplies the spectator input. -/
theorem eval_reordered_prepared_vector (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (first second free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i) (η : ∀ i, U i ⊗[ℂ] V i)
    {ℓ out : Layout P} (p : Word [] ℓ) (v : Word (slotLayout R U V ++ ℓ) out)
    (u : Word (freeSlotLayout R U V first ++ (freeSlotLayout R U V second ++ ℓ))
      (freeSlotLayout R U V free ++ ℓ))
    (h : u.eval ∘L (prepareFreeSlots R U V first η
        (freeSlotLayout R U V second ++ ℓ)).eval ∘L
        (prepareFreeSlots R U V second η ℓ).eval = (prepareFreeSlots R U V free η ℓ).eval)
    (ψ : Mem ℓ) (hp : p.eval 1 = ψ) :
    v.eval ((prepareSlots R U V (fillSourceVectors R U V free fixed η) ℓ).eval ψ) =
      (preparedReorderedWord R U V first second free fixed p v u).eval
        (sourceVectorPair R U V first second η) := by
  let C := freeSlotLayout R U V first
  let T := freeSlotLayout R U V second
  rw [← hp]
  symm
  change v.eval ((prepareSelected R U V free fixed ℓ).eval
    (u.eval (((Word.frameList (C ++ T) p).castLayouts
      (List.append_nil _) (List.append_assoc C T ℓ)).eval
        ((appendIso C T).symm
          (freeSourceVector R U V first η ⊗ₜ[ℂ] freeSourceVector R U V second η))))) = _
  rw [eval_framed_freeSourceVectors]
  have huη := DFunLike.congr_fun h (p.eval 1)
  change u.eval ((prepareFreeSlots R U V first η (T ++ ℓ)).eval
    ((prepareFreeSlots R U V second η ℓ).eval (p.eval 1))) = _ at huη
  rw [huη]
  have hsη := DFunLike.congr_fun
    (eval_prepareSelected_prepareFreeSlots R U V free fixed η ℓ) (p.eval 1)
  change (prepareSelected R U V free fixed ℓ).eval
    ((prepareFreeSlots R U V free η ℓ).eval (p.eval 1)) = _ at hsη
  rw [hsη]

end TNLean.PEPS.PairEffect.SourceInventory
