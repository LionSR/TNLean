/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt

/-!
# Canonical residual operations in fixed source coordinates

The residual is the original source-free local part with its input register list
identified with the prescribed common slots. Thus its operations are fixed by
the original word and the register spaces, independently of a recovery witness.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267 and 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
namespace Word
variable {P : Type} {a b : Layout P}

/-- The original local operations in prescribed source coordinates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267. -/
def residualInSlots (w : Word a b) (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (h : w.sources.layout = SourceInventory.slotLayout R U V) :
    Word (SourceInventory.slotLayout R U V ++ a) b :=
  w.localPart.castInput (congrArg (· ++ a) h)

/-- The canonical residual contains no pair sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–251. -/
theorem sources_residualInSlots (w : Word a b) (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (h : w.sources.layout = SourceInventory.slotLayout R U V) :
    (w.residualInSlots R U V h).sources = [] := by
  simp only [residualInSlots, sources_castInput, sources_localPart]

/-- Identifying the source coordinates preserves the allowed local operations.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem isAllowed_residualInSlots (w : Word a b) (hw : w.IsAllowed)
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (h : w.sources.layout = SourceInventory.slotLayout R U V) :
    (w.residualInSlots R U V h).IsAllowed :=
  (isAllowed_castInput _ _).mpr (isAllowed_localPart w hw)

/-- Preparing an exact representation of the original inventory recovers the
original operator through its canonical residual. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 246–267. -/
theorem eval_residualInSlots_prepare (w : Word a b) (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (h : w.sources.layout = SourceInventory.slotLayout R U V)
    (η : ∀ i, U i ⊗[ℂ] V i)
    (hη : SourceInventory.ofSlots R U V η = w.sources) :
    (w.residualInSlots R U V h).eval ∘L
        (SourceInventory.prepareSlots R U V η a).eval = w.eval := by
  have hc (L : Layout P) (hL : w.sources.layout = L) :
      (w.localPart.castInput (congrArg (· ++ a) hL)).eval ∘L
        ((w.sources.prepare a).castLayouts rfl (congrArg (· ++ a) hL)).eval =
          w.eval := by
    cases hL
    exact w.eval_eq_localPart_comp_prepare.symm
  have hs (S : SourceInventory P) (hS : S = w.sources)
      (hL : S.layout = SourceInventory.slotLayout R U V) :
      (w.localPart.castInput (congrArg (· ++ a) h)).eval ∘L
        ((S.prepare a).castLayouts rfl (congrArg (· ++ a) hL)).eval = w.eval := by
    subst S
    exact hc _ h
  exact hs _ hη (SourceInventory.layout_ofSlots_eq R U V η (fun _ ↦ 0))

end Word

namespace SourceCircuit
variable {P : Type}

/-- The common coordinate slots have the actual partial source layout.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–417. -/
theorem slotLayout_partialSlots_eq (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    SourceInventory.slotLayout (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) =
        (partialWord A w ξ).sources.layout := by
  let R := partialSlots A w
  have hU : (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)) =
      (fun i : Fin R.length ↦ (R.get i).leftSpace) :=
    funext fun i ↦ (partialSlot_spec A w i).2.2.1.symm
  have hV : (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) =
      (fun i : Fin R.length ↦ (R.get i).rightSpace) :=
    funext fun i ↦ (partialSlot_spec A w i).2.2.2.symm
  rw [hU, hV]
  have hR : SourceInventory.ofSlots R (fun i ↦ (R.get i).leftSpace)
      (fun i ↦ (R.get i).rightSpace) (fun i ↦ (R.get i).vector) = R := List.ofFn_get R
  exact (SourceInventory.layout_ofSlots_eq R _ _ (fun _ ↦ 0)
    (fun i ↦ (R.get i).vector)).trans
      ((congrArg SourceInventory.layout hR).trans (layout_partialSlots_eq A w ξ))

/-- The actual local part of a partial branch in the common source coordinates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def partialResidual (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    Word (SourceInventory.slotLayout (partialSlots A w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) ++
          Layout.mapOwner (affectedOwner A) a)
      (Layout.mapOwner (affectedOwner A) b) :=
  (partialWord A w ξ).residualInSlots (partialSlots A w) _ _
    (slotLayout_partialSlots_eq A w ξ).symm

/-- The canonical chronological residual contains no pair sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem sources_partialResidual (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    (partialResidual A w ξ).sources = [] :=
  Word.sources_residualInSlots _ _ _ _ _

/-- Every canonical partial residual consists of allowed local operations.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem isAllowed_partialResidual (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsAllowed) (ξ : Choices A w) :
    (partialResidual A w ξ).IsAllowed :=
  Word.isAllowed_residualInSlots _ (isAllowed_partialWord A w hw ξ) _ _ _ _

/-- The original locally selected source vectors recover the actual partial word
through its canonical residual. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–417. -/
theorem eval_partialResidual_prepare (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsAllowed) (ξ : Choices A w) :
    (partialResidual A w ξ).eval ∘L
        (SourceInventory.prepareSlots (partialSlots A w)
          (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
          (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
          (partialSlotVector A w ξ) (Layout.mapOwner (affectedOwner A) a)).eval =
      (partialWord A w ξ).eval :=
  Word.eval_residualInSlots_prepare _ _ _ _ _ _
    ((exists_partial_source_preparation_with_original_vectors A w hw).2.1 ξ)

end SourceCircuit
end TNLean.PEPS.PairEffect
