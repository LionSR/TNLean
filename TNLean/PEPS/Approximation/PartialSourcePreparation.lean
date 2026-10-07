/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitSourceOrder
import TNLean.PEPS.Approximation.PartialSourceInventory
import Mathlib.Data.List.NodupEquivFin

/-!
# Common preparation of the surviving chronological sources

The source slots of a partial expansion are the original ordered positions with
at least one affected endpoint. Their owners and coordinate halfspaces are fixed
before a monomial is chosen; their vectors are the actual vectors of that monomial.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-fixed-preparation-partialpositions
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.partialPositions

Provenance-ID: 8769-fixed-preparation-mem_partialpositions_iff
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.mem_partialPositions_iff

Provenance-ID: 8769-fixed-preparation-partialslots
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.partialSlots

Provenance-ID: 8769-fixed-preparation-partialslotequiv
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.partialSlotEquiv

Provenance-ID: 8769-fixed-preparation-partialslotequiv_apply
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.partialSlotEquiv_apply

Provenance-ID: 8769-fixed-preparation-layout_partialslots
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.layout_partialSlots

Provenance-ID: 8769-fixed-preparation-partialslot_spec
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.partialSlot_spec

Provenance-ID: 8769-fixed-preparation-layout_partialslots_eq
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.layout_partialSlots_eq

Provenance-ID: 8769-fixed-preparation-exists_partial_source_preparation
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.exists_partial_source_preparation
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- Inventories with the same ordered register layout differ only in their vectors.
This identifies the actual source vectors in the common private spaces of
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–417. -/
private theorem exists_ofSlots_of_layout_eq (R S : SourceInventory P)
    (h : R.layout = S.layout) (hS : S.IsNormalized) :
    ∃ η : ∀ i, (R.get i).leftSpace ⊗[ℂ] (R.get i).rightSpace,
      (∀ i, ‖η i‖ = 1) ∧
      ofSlots R (fun i ↦ (R.get i).leftSpace) (fun i ↦ (R.get i).rightSpace) η = S := by
  induction R generalizing S with
  | nil =>
      cases S with
      | nil => exact ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, rfl⟩
      | cons s S => simp [layout_cons, PairSource.layout] at h
  | cons r R ih =>
      cases S with
      | nil => simp [layout_cons, PairSource.layout] at h
      | cons s S =>
          simp only [layout_cons, PairSource.layout, List.cons_append, List.nil_append,
            List.cons.injEq] at h
          rcases r with ⟨p, q, hpq, U, V, η₀⟩
          rcases s with ⟨p', q', hpq', U', V', η₁⟩
          simp only [Reg.mk.injEq] at h
          rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, h⟩
          obtain ⟨η, hη, heq⟩ := ih S h (fun s hs ↦ hS s (List.mem_cons_of_mem _ hs))
          refine ⟨Fin.cons η₁ η, ?_, ?_⟩
          · intro i
            cases i using Fin.cases with
            | zero => exact hS ⟨p, q, hpq', U, V, η₁⟩ List.mem_cons_self
            | succ i => exact hη i
          · rw [ofSlots_cons]
            exact congrArg (List.cons (⟨p, q, hpq, U, V, η₁⟩ : PairSource P)) heq
end TNLean.PEPS.PairEffect.SourceInventory

namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Original source positions retained after grouping all exterior parties.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
def partialPositions (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) :
    List (sourceLocations w) :=
  (sourceOrder w).filter (fun e ↦ A (endpoints w e).1 || A (endpoints w e).2)

/-- Membership in the retained ordered list depends only on the original endpoints.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem mem_partialPositions_iff (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (e : sourceLocations w) :
    e ∈ partialPositions A w ↔
      A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true := by
  simp [partialPositions, mem_sourceOrder]

/-- The grouped endpoint pair of a retained original position is distinct.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
private theorem partialPosition_distinct (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (e : sourceLocations w) (he : e ∈ partialPositions A w) :
    affectedOwner A (endpoints w e).1 ≠ affectedOwner A (endpoints w e).2 := by
  intro h
  rcases (affectedOwner_eq_iff A _ _).mp h with h | ⟨hl, hr⟩
  · exact endpoints_ne w e h
  · simpa [hl, hr] using (mem_partialPositions_iff A w e).mp he

/-- The fixed inventory of retained original slots. The zero vectors specify
only the common owners and halfspaces, not a normalized preparation.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–417. -/
def partialSlots (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) :
    SourceInventory (Option {p // A p = true}) :=
  (partialPositions A w).attach.map fun e ↦
    ⟨affectedOwner A (endpoints w e.1).1, affectedOwner A (endpoints w e.1).2,
      partialPosition_distinct A w e.1 e.2,
      euc (Fin (sourceDims w e.1).1), euc (Fin (sourceDims w e.1).2), 0⟩

/-- The finite slots are canonically the surviving original source positions,
in their preparation order. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–417. -/
def partialSlotEquiv (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) :
    Fin (partialSlots A w).length ≃
      {e : sourceLocations w // A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true} := by
  classical
  exact (finCongr (show (partialSlots A w).length = (partialPositions A w).length by
    simp [partialSlots])).trans
    ((List.Nodup.getEquiv (partialPositions A w) ((nodup_sourceOrder w).filter _)).trans
      (Equiv.subtypeEquivRight (mem_partialPositions_iff A w)))

/-- The forward enumeration reads the ordered list of surviving original positions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem partialSlotEquiv_apply (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (i : Fin (partialSlots A w).length) :
    (partialSlotEquiv A w i).1 =
      (partialPositions A w).get ⟨i.1, by simpa [partialSlots] using i.2⟩ := rfl

/-- The fixed slots have exactly the common surviving register layout.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–417. -/
theorem layout_partialSlots (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) :
    (partialSlots A w).layout = (partialPositions A w).flatMap
      (fun e ↦ [⟨affectedOwner A (endpoints w e).1, euc (Fin (sourceDims w e).1)⟩,
        ⟨affectedOwner A (endpoints w e).2, euc (Fin (sourceDims w e).2)⟩]) := by
  simp only [partialSlots, SourceInventory.layout, List.flatMap_def, List.map_map,
    Function.comp_def, PairSource.layout]
  exact congrArg List.flatten (List.attach_map_val (f := fun e : sourceLocations w ↦
    [Reg.mk (affectedOwner A (endpoints w e).1) (euc (Fin (sourceDims w e).1)),
      Reg.mk (affectedOwner A (endpoints w e).2) (euc (Fin (sourceDims w e).2))]))

/-- The finite enumeration preserves the grouped endpoints and the original
coordinate dimensions at each surviving position. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–417. -/
theorem partialSlot_spec (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (i : Fin (partialSlots A w).length) :
    let e := (partialSlotEquiv A w i).1
    ((partialSlots A w).get i).left = affectedOwner A (endpoints w e).1 ∧
      ((partialSlots A w).get i).right = affectedOwner A (endpoints w e).2 ∧
      ((partialSlots A w).get i).leftSpace = euc (Fin (sourceDims w e).1) ∧
      ((partialSlots A w).get i).rightSpace = euc (Fin (sourceDims w e).2) := by
  dsimp only
  erw [partialSlotEquiv_apply]
  simp only [partialSlots]
  erw [List.get_eq_getElem, List.getElem_map, List.getElem_attach]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every partial monomial has the fixed surviving register layout.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem layout_partialSlots_eq (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    (partialSlots A w).layout = (partialWord A w ξ).sources.layout :=
  (layout_partialSlots A w).trans (layout_sources_partialWord A w ξ).symm

/-- Every partial monomial has an exact preparation in the same original
surviving source slots, followed by actual allowed operations containing no
sources. The Euclidean dimensions and the slot enumeration are independent of
all branch labels. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267 and 342–417. -/
theorem exists_partial_source_preparation (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsAllowed) :
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    ∃ η : Choices A w → ∀ i, U i ⊗[ℂ] V i,
      (∀ ξ i, ‖η ξ i‖ = 1) ∧
      (∀ ξ, SourceInventory.ofSlots R U V (η ξ) = (partialWord A w ξ).sources) ∧
      ∃ v : Choices A w → Word
          (SourceInventory.slotLayout R U V ++ Layout.mapOwner (affectedOwner A) a)
          (Layout.mapOwner (affectedOwner A) b),
        (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
        ∀ ξ, (partialWord A w ξ).eval = (v ξ).eval ∘L
          (SourceInventory.prepareSlots R U V (η ξ)
            (Layout.mapOwner (affectedOwner A) a)).eval := by
  classical
  dsimp only
  let R := partialSlots A w
  let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  have hU : (fun i ↦ (R.get i).leftSpace) = U :=
    funext (fun i ↦ (partialSlot_spec A w i).2.2.1)
  have hV : (fun i ↦ (R.get i).rightSpace) = V :=
    funext (fun i ↦ (partialSlot_spec A w i).2.2.2)
  have hc (ξ : Choices A w) (U' V' : Fin R.length → HSpace)
      (hU' : (fun i ↦ (R.get i).leftSpace) = U')
      (hV' : (fun i ↦ (R.get i).rightSpace) = V') :
      ∃ η : ∀ i, U' i ⊗[ℂ] V' i, (∀ i, ‖η i‖ = 1) ∧
        SourceInventory.ofSlots R U' V' η = (partialWord A w ξ).sources := by
    subst U'
    subst V'
    exact SourceInventory.exists_ofSlots_of_layout_eq R _ (layout_partialSlots_eq A w ξ)
      (Word.isNormalized_sources _ (isAllowed_partialWord A w hw ξ))
  choose η hη hS using fun ξ ↦ hc ξ U V hU hV
  have hE (ξ : Choices A w) :
      (SourceInventory.ofSlots R U V (η ξ)).Expands (partialWord A w ξ).sources := by
    simpa only [hS ξ] using SourceInventory.Expands.refl (partialWord A w ξ).sources
  choose d hd hds hde using fun ξ ↦
    SourceInventory.exists_prepareSlots_recovery R (partialWord A w ξ).sources U V
      (η ξ) (hE ξ) (Layout.mapOwner (affectedOwner A) a)
  refine ⟨η, hη, hS, fun ξ ↦ .comp (d ξ) (partialWord A w ξ).localPart, ?_, ?_, ?_⟩
  · exact fun ξ ↦ ⟨hd ξ, Word.isAllowed_localPart _ (isAllowed_partialWord A w hw ξ)⟩
  · intro ξ
    simp only [Word.sources, Word.sources_localPart, hds, List.nil_append]
  · intro ξ
    rw [Word.eval_comp, comp_assoc, hde, Word.eval_eq_localPart_comp_prepare]

end TNLean.PEPS.PairEffect.SourceCircuit
