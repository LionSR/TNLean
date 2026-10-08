/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartialSourcePreparation

/-!
# Original gate labels and vectors in the partial source preparation

Each surviving source position belongs to a touched gate occurrence. A choice
in the partial expansion therefore determines a branch label at that occurrence.
The vector at the surviving position is exactly the original gate vector for
this label. In particular, it is independent of labels at all other occurrences.

The proof uses the ordered source inventory, so repeated occurrences and source
positions retain their original identities. No label is requested at an untouched
gate, whose branch type may be empty.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–417.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Recover the actual monomial label at a touched gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
def choiceAt (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    Choices A w → (g : gateLocations w) → IsTouched A w g → branchLabels w g
  | _, _, .id _, _, g, _ => nomatch g
  | _, _, .comp w v, ξ, g, h => by
      cases g with
      | inl g => exact choiceAt A w ξ.1 g h
      | inr g => exact choiceAt A v ξ.2 g h
  | _, _, .localMap .., _, g, _ => nomatch g
  | _, _, @SourceCircuit.gate _ C ι _ _ owner a b c G tail, ξ, g, h => by
      classical
      cases g
      have ht := (isTouched_gate_iff A owner G tail).mp h
      exact (Equiv.cast (by simp only [Choices, branchLabels, ite_eq_left ht])) ξ
  | _, _, .swap .., _, g, _ => nomatch g
  | _, _, .frame _ w, ξ, g, h => choiceAt A w ξ g h

/-- The original gate's vector at a source occurrence and a local branch label.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
def sourceVectorAt : {a b : Layout P} → (w : SourceCircuit a b) →
    (e : sourceLocations w) → branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2)
  | _, _, .id _, e => nomatch e.1
  | _, _, .comp w v, ⟨g, i⟩ => by
      cases g with
      | inl g => exact sourceVectorAt w ⟨g, i⟩
      | inr g => exact sourceVectorAt v ⟨g, i⟩
  | _, _, .localMap .., e => nomatch e.1
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ _ G _, e => fun ξ ↦ G.vector ξ e.2
  | _, _, .swap .., e => nomatch e.1
  | _, _, .frame _ w, e => sourceVectorAt w e

/-- Every original local source vector is normalized, independently of other gates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem sourceVectorAt_norm {a b : Layout P} (w : SourceCircuit a b)
    (e : sourceLocations w) (ξ : branchLabels w e.1) :
    ‖sourceVectorAt w e ξ‖ = 1 := by
  induction w with
  | id => rcases e with ⟨g, i⟩; cases g
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact ihw ⟨g, i⟩ ξ
      | inr g => exact ihv ⟨g, i⟩ ξ
  | localMap => rcases e with ⟨g, i⟩; cases g
  | @gate C ι _ _ owner a b c G tail => exact G.vector_norm ξ e.2
  | swap => rcases e with ⟨g, i⟩; cases g
  | frame r w ih => exact ih e ξ

/-- A source incident to an affected party lies at a touched gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem isTouched_of_source_endpoint (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (e : sourceLocations w)
    (he : A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true) :
    IsTouched A w e.1 := by
  rcases he with he | he
  · exact ⟨(endpoints w e).1, (endpoints_mem_participants w e).1, he⟩
  · exact ⟨(endpoints w e).2, (endpoints_mem_participants w e).2, he⟩

/-- The retained record is the original gate vector selected by its local label.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem sourceAt_eq_mapOwner_sourceVectorAt (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) (e : sourceLocations w)
    (he : IsTouched A w e.1) :
    sourceAt A w ξ e =
      (PairSource.mk (endpoints w e).1 (endpoints w e).2 (endpoints_ne w e)
        (euc (Fin (sourceDims w e).1)) (euc (Fin (sourceDims w e).2))
        (sourceVectorAt w e (choiceAt A w ξ e.1 he))).mapOwner (affectedOwner A) := by
  induction w with
  | id => rcases e with ⟨g, i⟩; cases g
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact ihw ξ.1 ⟨g, i⟩ he
      | inr g => exact ihv ξ.2 ⟨g, i⟩ he
  | localMap => rcases e with ⟨g, i⟩; cases g
  | @gate C ι _ _ owner a b c G tail =>
      classical
      rcases e with ⟨⟨⟩, i⟩
      have ht := (isTouched_gate_iff A owner G tail).mp he
      simp only [sourceAt, dite_eq_left ht, choiceAt, sourceVectorAt, endpoints, sourceDims]
      rfl
  | swap => rcases e with ⟨g, i⟩; cases g
  | frame r w ih => exact ih ξ e he

/-- The monomial label selected at the original gate of a surviving source slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
def partialSlotChoice (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (ξ : Choices A w) (i : Fin (partialSlots A w).length) :
    branchLabels w (partialSlotEquiv A w i).1.1 :=
  choiceAt A w ξ (partialSlotEquiv A w i).1.1
    (isTouched_of_source_endpoint A w (partialSlotEquiv A w i).1
      (partialSlotEquiv A w i).2)

/-- Reading the source record at each retained original position, in order, gives the
actual ordered source list of the partial branch, each entry wrapped in `some`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
private theorem map_sourceAt_partialPositions (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    (partialPositions A w).map (sourceAt A w ξ) =
      (partialWord A w ξ).sources.map some := by
  have hp : (fun e ↦ (sourceAt A w ξ e).isSome) =
      (fun e ↦ A (endpoints w e).1 || A (endpoints w e).2) := by
    funext e
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.or_eq_true] using sourceAt_isSome_iff A w ξ e
  rw [sources_partialWord_eq_filterMap,
    List.map_filterMap_some_eq_filter_map_isSome, List.filter_map]
  simp only [Function.comp_def, hp, partialPositions]

/-- The source vector at a fixed surviving slot uses only its owning gate's label.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
def partialSlotVector (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (ξ : Choices A w) (i : Fin (partialSlots A w).length) :
    euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ⊗[ℂ]
      euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2) :=
  sourceVectorAt w (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i)

/-- If a family of vectors in the fixed source slots represents the actual ordered source
list of the partial branch, then the source record at the `i`-th retained original position
is the `i`-th reference slot (its grouped endpoints and fixed halfspaces) carrying the vector
`η i`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
private theorem sourceAt_partialSlot_of_ofSlots_eq (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w)
    (η : ∀ i : Fin (partialSlots A w).length,
      euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ⊗[ℂ]
        euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
    (hη : SourceInventory.ofSlots (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) η =
        (partialWord A w ξ).sources)
    (i : Fin (partialSlots A w).length) :
    sourceAt A w ξ (partialSlotEquiv A w i).1 = some
      ⟨((partialSlots A w).get i).left, ((partialSlots A w).get i).right,
        ((partialSlots A w).get i).distinct,
        euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1),
        euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2), η i⟩ := by
  have hm := (map_sourceAt_partialPositions A w ξ).trans (congrArg (List.map some) hη.symm)
  have hi := congrArg (fun l ↦ l[i.val]?) hm
  simp only [List.getElem?_map, SourceInventory.ofSlots, List.getElem?_ofFn] at hi
  have hiL : i.val < (partialPositions A w).length := by
    simpa only [partialSlots, List.length_map, List.length_attach] using i.isLt
  conv_lhs => rw [partialSlotEquiv_apply, List.get_eq_getElem]
  simpa only [List.getElem?_eq_getElem hiL, dite_eq_left i.isLt, Option.map_some,
    Option.some.injEq] using hi

/-- Any exact inventory representation uses the original locally selected source vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem eq_partialSlotVector_of_inventory_eq (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w)
    (η : ∀ i : Fin (partialSlots A w).length,
      euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ⊗[ℂ]
        euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
    (hη : SourceInventory.ofSlots (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) η =
        (partialWord A w ξ).sources) :
    η = partialSlotVector A w ξ := by
  funext i
  have hi := sourceAt_partialSlot_of_ofSlots_eq A w ξ η hη i
  have he := isTouched_of_source_endpoint A w (partialSlotEquiv A w i).1
    (partialSlotEquiv A w i).2
  rw [sourceAt_eq_mapOwner_sourceVectorAt A w ξ _ he] at hi
  have hne : affectedOwner A (endpoints w (partialSlotEquiv A w i).1).1 ≠
      affectedOwner A (endpoints w (partialSlotEquiv A w i).1).2 := by
    rw [← (partialSlot_spec A w i).1, ← (partialSlot_spec A w i).2.1]
    exact ((partialSlots A w).get i).distinct
  simp only [PairSource.mapOwner, dite_eq_right hne, Option.some.injEq,
    PairSource.mk.injEq, heq_eq_eq, true_and] at hi
  exact hi.2.2.symm

/-- The common preparation uses the original gate vector at each selected local label.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem exists_partial_source_preparation_with_original_vectors (A : P → Bool)
    {a b : Layout P} (w : SourceCircuit a b) (hw : w.IsAllowed) :
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    (∀ ξ i, ‖partialSlotVector A w ξ i‖ = 1) ∧
      (∀ ξ, SourceInventory.ofSlots R U V (partialSlotVector A w ξ) =
        (partialWord A w ξ).sources) ∧
      ∃ v : Choices A w → Word
          (SourceInventory.slotLayout R U V ++ Layout.mapOwner (affectedOwner A) a)
          (Layout.mapOwner (affectedOwner A) b),
        (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
        ∀ ξ, (partialWord A w ξ).eval = (v ξ).eval ∘L
          (SourceInventory.prepareSlots R U V (partialSlotVector A w ξ)
            (Layout.mapOwner (affectedOwner A) a)).eval := by
  obtain ⟨η, hη, hS, v, hv, hvs, he⟩ := exists_partial_source_preparation A w hw
  have hηeq : η = partialSlotVector A w :=
    funext fun ξ ↦ eq_partialSlotVector_of_inventory_eq A w ξ (η ξ) (hS ξ)
  subst η
  exact ⟨hη, hS, v, hv, hvs, he⟩

end TNLean.PEPS.PairEffect.SourceCircuit
