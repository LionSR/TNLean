/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitLocations

/-!
# Ordered source positions in a chronological partial expansion

The common source positions have the same order as the actual source inventory:
slots of later gates come first, and each gate retains its original slot order.
The dimensions of these positions do not depend on a monomial choice.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-order-sourcecircuit.sourceorder
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sourceOrder

Provenance-ID: 8769-chronological-order-sourcecircuit.mem_sourceorder
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.mem_sourceOrder

Provenance-ID: 8769-chronological-order-sourcecircuit.nodup_sourceorder
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.nodup_sourceOrder

Provenance-ID: 8769-chronological-order-sourcecircuit.sourcedims
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sourceDims

Provenance-ID: 8769-chronological-order-sourcecircuit.sourceat
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sourceAt

Provenance-ID: 8769-chronological-order-sourcecircuit.sourceat_issome_iff
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sourceAt_isSome_iff

Provenance-ID: 8769-chronological-order-sourcecircuit.sourceat_eq_some_spec
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sourceAt_eq_some_spec

Provenance-ID: 8769-chronological-order-sourcecircuit.sources_partialword_eq_filtermap
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sources_partialWord_eq_filterMap

Provenance-ID: 8769-chronological-order-sourcecircuit.layout_sources_partialword
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.layout_sources_partialWord
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- All source positions in preparation order, retaining the order of slots
within every gate. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
def sourceOrder : {a b : Layout P} → (w : SourceCircuit a b) → List (sourceLocations w)
  | _, _, .id _ => []
  | _, _, .comp w v =>
      (sourceOrder v).map (fun e ↦ (⟨Sum.inr e.1, e.2⟩ : sourceLocations (.comp w v))) ++
        (sourceOrder w).map (fun e ↦ (⟨Sum.inl e.1, e.2⟩ : sourceLocations (.comp w v)))
  | _, _, .localMap .. => []
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ _ G _ =>
      List.ofFn (fun i : Fin G.slots.length ↦ ⟨(), i⟩)
  | _, _, .swap .. => []
  | _, _, .frame _ w => sourceOrder w

/-- Each original source position occurs in the ordered list.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–355. -/
theorem mem_sourceOrder {a b : Layout P} (w : SourceCircuit a b)
    (e : sourceLocations w) : e ∈ sourceOrder w := by
  induction w with
  | id => exact nomatch e.1
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨g, i⟩, ihw _, rfl⟩)
      | inr g => exact List.mem_append_left _ (List.mem_map.mpr ⟨⟨g, i⟩, ihv _, rfl⟩)
  | localMap => exact nomatch e.1
  | @gate C ι _ _ owner a b c G tail =>
      rcases e with ⟨⟨⟩, i⟩
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
  | swap => exact nomatch e.1
  | frame r w ih => exact ih e

/-- No source occurrence is repeated, even if its pair of endpoint parties
occurs at several gates. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
theorem nodup_sourceOrder {a b : Layout P} (w : SourceCircuit a b) :
    (sourceOrder w).Nodup := by
  induction w with
  | id => exact List.nodup_nil
  | comp w v ihw ihv =>
      refine (ihv.map (Sum.inr_injective.sigma_map
          (β₁ := fun g ↦ Fin (slotCount v g))
          (β₂ := fun g ↦ Fin (slotCount (.comp w v) g))
          (fun _ ↦ Function.injective_id))).append
        (ihw.map (Sum.inl_injective.sigma_map
          (β₁ := fun g ↦ Fin (slotCount w g))
          (β₂ := fun g ↦ Fin (slotCount (.comp w v) g))
          (fun _ ↦ Function.injective_id))) ?_
      rintro e hv hw
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
      obtain ⟨y, _, h⟩ := List.mem_map.mp hw
      have htag := congrArg (fun e : sourceLocations (.comp w v) ↦ e.1) h
      cases htag
  | localMap => exact List.nodup_nil
  | @gate C ι _ _ owner a b c G tail =>
      exact List.nodup_ofFn_ofInjective
        (sigma_mk_injective (β := fun g ↦ Fin (slotCount (.gate owner G tail) g)))
  | swap => exact List.nodup_nil
  | frame r w ih => exact ih

/-- The two coordinate dimensions at an original source position are fixed
before any monomial choices. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267 and 342–355. -/
def sourceDims : {a b : Layout P} → (w : SourceCircuit a b) → sourceLocations w → ℕ × ℕ
  | _, _, .id _ => fun e ↦ nomatch e.1
  | _, _, .comp w v => by
      rintro ⟨g, i⟩
      cases g with
      | inl g => exact sourceDims w ⟨g, i⟩
      | inr g => exact sourceDims v ⟨g, i⟩
  | _, _, .localMap .. => fun e ↦ nomatch e.1
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ _ G _ => fun e ↦
      (G.leftDim e.2, G.rightDim e.2)
  | _, _, .swap .. => fun e ↦ nomatch e.1
  | _, _, .frame _ w => sourceDims w

/-- The actual source record at an original position, when that position remains
nonlocal after grouping the exterior parties. Untouched gates need no branch
label. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def sourceAt (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    Choices A w → sourceLocations w → Option (PairSource (Option {p // A p = true}))
  | _, _, .id _, _ => fun e ↦ nomatch e.1
  | _, _, .comp w v, ξ => by
      rintro ⟨g, i⟩
      cases g with
      | inl g => exact sourceAt A w ξ.1 ⟨g, i⟩
      | inr g => exact sourceAt A v ξ.2 ⟨g, i⟩
  | _, _, .localMap .., _ => fun e ↦ nomatch e.1
  | _, _, @SourceCircuit.gate _ C ι _ _ owner _ _ _ G _, ξ => by
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · have j : ι := by simpa only [Choices, ite_eq_left h] using ξ
        exact fun e ↦ (PairSource.mk (owner (G.slots.get e.2).left)
          (owner (G.slots.get e.2).right)
          (fun h ↦ (G.slots.get e.2).distinct (owner.injective h))
          (euc (Fin (G.leftDim e.2))) (euc (Fin (G.rightDim e.2)))
          (G.vector j e.2)).mapOwner (affectedOwner A)
      · exact fun _ ↦ none
  | _, _, .swap .., _ => fun e ↦ nomatch e.1
  | _, _, .frame _ w, ξ => sourceAt A w ξ

/-- A position survives exactly when at least one of its original endpoints is
affected. This criterion does not depend on the monomial choices. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem sourceAt_isSome_iff (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) (e : sourceLocations w) :
    (sourceAt A w ξ e).isSome = true ↔
      A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true := by
  induction w with
  | id => exact nomatch e.1
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact ihw ξ.1 ⟨g, i⟩
      | inr g => exact ihv ξ.2 ⟨g, i⟩
  | localMap => exact nomatch e.1
  | @gate C ι _ _ owner a b c G tail =>
      classical
      rcases e with ⟨⟨⟩, i⟩
      by_cases h : ∃ p : C, A (owner p) = true
      · have hs (s : PairSource P) : (s.mapOwner (affectedOwner A)).isSome = true ↔
            A s.left = true ∨ A s.right = true := by
          simp [PairSource.mapOwner, ← s.affectedOwner_ne_iff A]
        simp only [sourceAt, dite_eq_left h]
        exact hs _
      · have hp : ∀ p : C, A (owner p) ≠ true := fun p hp ↦ h ⟨p, hp⟩
        simp [sourceAt, endpoints, hp]
  | swap => exact nomatch e.1
  | frame r w ih => exact ih ξ e

/-- Surviving records have the original endpoints, fixed coordinate halfspaces,
and normalized branch vectors. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267 and 383–417. -/
theorem sourceAt_eq_some_spec (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) (e : sourceLocations w)
    {s : PairSource (Option {p // A p = true})} (h : sourceAt A w ξ e = some s) :
    s.left = affectedOwner A (endpoints w e).1 ∧
      s.right = affectedOwner A (endpoints w e).2 ∧
      s.leftSpace = euc (Fin (sourceDims w e).1) ∧
      s.rightSpace = euc (Fin (sourceDims w e).2) ∧ ‖s.vector‖ = 1 := by
  induction w with
  | id => exact nomatch e.1
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact ihw ξ.1 ⟨g, i⟩ h
      | inr g => exact ihv ξ.2 ⟨g, i⟩ h
  | localMap => exact nomatch e.1
  | @gate C ι _ _ owner a b c G tail =>
      classical
      rcases e with ⟨⟨⟩, i⟩
      by_cases ht : ∃ p : C, A (owner p) = true
      · simp only [sourceAt, dite_eq_left ht, PairSource.mapOwner] at h
        split_ifs at h with heq
        cases Option.some.inj h
        exact ⟨rfl, rfl, rfl, rfl, G.vector_norm _ _⟩
      · simp [sourceAt, ht] at h
  | swap => exact nomatch e.1
  | frame r w ih => exact ih ξ e h

/-- The actual source inventory of every partial monomial is obtained from the
fixed ordered positions by retaining exactly their surviving records. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem sources_partialWord_eq_filterMap (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    (partialWord A w ξ).sources = (sourceOrder w).filterMap (sourceAt A w ξ) := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simp only [partialWord, Word.sources, sourceOrder, ihw, ihv]
      erw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      rfl
  | localMap => simp [partialWord, Word.sources_mapOwner, Word.sources, sourceOrder]
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases ht : ∃ p : C, A (owner p) = true
      · simp only [partialWord, dite_eq_left ht, Word.sources_mapOwner,
          Word.sources_appendTail, G.sources_branchWord, sourceOrder,
          SourceInventory.ofSlots, SourceInventory.mapOwner, List.ofFn_eq_map,
          List.filterMap_map, List.filterMap_filterMap]
        erw [List.ofFn_eq_map, List.filterMap_map]
        apply List.filterMap_congr
        intro i hi
        simp only [Function.comp_apply, PairSource.mapOwner]
        have hn : owner (G.slots.get i).left ≠ owner (G.slots.get i).right :=
          fun h ↦ (G.slots.get i).distinct (owner.injective h)
        rw [dite_eq_right hn]
        simp only [sourceAt, dite_eq_left ht]
        rfl
      · simp only [partialWord, dite_eq_right ht, Word.groupedBlockMap,
          Word.sources_castLayouts, Word.sources, sourceOrder]
        symm
        apply List.filterMap_eq_nil_iff.mpr
        intro e he
        simp [sourceAt, ht]
  | swap => simp [partialWord, Word.sources_mapOwner, Word.sources, sourceOrder]
  | frame r w ih => exact ih ξ

/-- The common source register layout of a partial expansion is obtained by
filtering the original ordered positions by their affected endpoints. In
particular this layout is independent of the monomial labels. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem layout_sources_partialWord (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    (partialWord A w ξ).sources.layout =
      ((sourceOrder w).filter (fun e ↦ A (endpoints w e).1 || A (endpoints w e).2)).flatMap
        (fun e ↦ [⟨affectedOwner A (endpoints w e).1, euc (Fin (sourceDims w e).1)⟩,
          ⟨affectedOwner A (endpoints w e).2, euc (Fin (sourceDims w e).2)⟩]) := by
  rw [sources_partialWord_eq_filterMap, SourceInventory.layout]
  generalize sourceOrder w = L
  induction L with
  | nil => rfl
  | cons e L ih =>
      have he := sourceAt_isSome_iff A w ξ e
      cases hs : sourceAt A w ξ e with
      | none =>
          have hf : (A (endpoints w e).1 || A (endpoints w e).2) = false := by
            simpa [hs] using he.not.mp (by simp [hs])
          simp only [List.filterMap_cons, hs, List.filter_cons, hf, Bool.false_eq_true,
            ↓reduceIte]
          exact ih
      | some s =>
          have ht : (A (endpoints w e).1 || A (endpoints w e).2) = true := by
            simpa only [Bool.or_eq_true] using he.mp (by simp [hs])
          obtain ⟨hl, hr, hU, hV, _⟩ := sourceAt_eq_some_spec A w ξ e hs
          simp only [List.filterMap_cons, hs, List.filter_cons, ht, ↓reduceIte,
            List.flatMap_cons, PairSource.layout, hl, hr, hU, hV, ih]

end TNLean.PEPS.PairEffect.SourceCircuit
