/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceSubstitutionResidual

/-!
# Exact source inventories under local substitutions

Substituted vectors retain their original source positions and gate labels.
The canonical residual therefore evaluates every such substitution in the same
ordered coordinate spaces.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-sourcesubstitutioninventory-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.ofSlots_partialWithSources

Provenance-ID: 8769-source-corrections-sourcesubstitutioninventory-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.eval_partialResidual_prepare_substituted

-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

private def substitutedSourceAt (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (ξ : Choices A w) (e : sourceLocations w) :
    Option (PairSource (Option {p // A p = true})) := by
  classical
  exact if h : IsTouched A w e.1 then
    (PairSource.mk (endpoints w e).1 (endpoints w e).2 (endpoints_ne w e)
      (euc (Fin (sourceDims w e).1)) (euc (Fin (sourceDims w e).2))
      (η e (choiceAt A w ξ e.1 h))).mapOwner (affectedOwner A)
  else none

private theorem substitutedSourceAt_isSome_iff (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (ξ : Choices A w) (e : sourceLocations w) :
    (substitutedSourceAt A w η ξ e).isSome = true ↔
      A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true := by
  classical
  by_cases ht : IsTouched A w e.1
  · simp only [substitutedSourceAt, dite_eq_left ht]
    have hs (s : PairSource P) : (s.mapOwner (affectedOwner A)).isSome = true ↔
        A s.left = true ∨ A s.right = true := by
      simp [PairSource.mapOwner, ← s.affectedOwner_ne_iff A]
    exact hs _
  · have he : ¬ (A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true) :=
      fun he ↦ ht (isTouched_of_source_endpoint A w e he)
    simp [substitutedSourceAt, ht, he]

private theorem sources_branchWithSources {C ι : Type} [Fintype ι]
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b) (ξ : ι)
    (η : ∀ i, euc (Fin (G.leftDim i)) ⊗[ℂ] euc (Fin (G.rightDim i))) :
    (G.branchWithSources ξ η).sources = SourceInventory.ofSlots G.slots
      (fun i ↦ euc (Fin (G.leftDim i))) (fun i ↦ euc (Fin (G.rightDim i))) η := by
  simp only [PreparedSourceGate.branchWithSources, Word.sources, G.remaining_sources,
    SourceInventory.prepareSlots, Word.sources_castLayouts, Word.sources_prepare,
    List.nil_append]

private theorem sources_partialWithSources_eq_filterMap (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (ξ : Choices A w) :
    (partialWithSources A w η ξ).sources =
      (sourceOrder w).filterMap (substitutedSourceAt A w η ξ) := by
  classical
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simp only [partialWithSources, Word.sources, sourceOrder]
      erw [ihv, ihw]
      erw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      rfl
  | localMap => simp [partialWithSources, Word.sources_mapOwner, Word.sources, sourceOrder]
  | @gate C ι _ _ owner a b c G tail =>
      by_cases ht : ∃ p : C, A (owner p) = true
      · simp only [partialWithSources, dite_eq_left ht, Word.sources_mapOwner,
          Word.sources_appendTail, sourceOrder]
        erw [sources_branchWithSources]
        simp only [SourceInventory.ofSlots, SourceInventory.mapOwner, List.ofFn_eq_map,
          List.filterMap_map, List.filterMap_filterMap]
        erw [List.ofFn_eq_map, List.filterMap_map]
        apply List.filterMap_congr
        intro i hi
        simp only [Function.comp_apply, PairSource.mapOwner]
        have hn : owner (G.slots.get i).left ≠ owner (G.slots.get i).right :=
          fun h ↦ (G.slots.get i).distinct (owner.injective h)
        rw [dite_eq_right hn]
        have htouch : IsTouched A (.gate owner G tail) () :=
          (isTouched_gate_iff A owner G tail).mpr ht
        change _ = substitutedSourceAt A (.gate owner G tail) η ξ ⟨(), i⟩
        unfold substitutedSourceAt
        rw [dite_eq_left htouch]
        dsimp only [choiceAt]
        rfl
      · simp only [partialWithSources, dite_eq_right ht, Word.groupedBlockMap,
          Word.sources_castLayouts, Word.sources, sourceOrder]
        symm
        apply List.filterMap_eq_nil_iff.mpr
        intro e he
        have htouch : ¬ IsTouched A (.gate owner G tail) e.1 := by
          cases e.1
          exact fun h ↦ ht ((isTouched_gate_iff A owner G tail).mp h)
        simp [substitutedSourceAt, htouch]
  | swap => simp [partialWithSources, Word.sources_mapOwner, Word.sources, sourceOrder]
  | frame r w ih => exact ih η ξ

/-- The substituted partial word retains exactly the original ordered occurrences,
with the vector supplied at each occurrence's chosen local label. Normalization
is not required. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 338–417. -/
theorem ofSlots_partialWithSources (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (ξ : Choices A w) :
    SourceInventory.ofSlots (partialSlots A w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
        (fun i ↦ η (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i)) =
      (partialWithSources A w η ξ).sources := by
  classical
  have hp : (fun e ↦ (substitutedSourceAt A w η ξ e).isSome) =
      (fun e ↦ A (endpoints w e).1 || A (endpoints w e).2) := by
    funext e
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.or_eq_true] using substitutedSourceAt_isSome_iff A w η ξ e
  have hm : (partialPositions A w).map (substitutedSourceAt A w η ξ) =
      (partialWithSources A w η ξ).sources.map some := by
    rw [sources_partialWithSources_eq_filterMap,
      List.map_filterMap_some_eq_filter_map_isSome, List.filter_map]
    simp only [Function.comp_def, hp, partialPositions]
  have he : List.ofFn (fun i : Fin (partialSlots A w).length ↦
      (partialSlotEquiv A w i).1) = partialPositions A w := by
    apply List.ext_getElem
    · simp [partialSlots]
    · intro j hj hk
      simp only [List.getElem_ofFn, partialSlotEquiv_apply, List.get_eq_getElem]
  apply (List.map_inj_right (fun _ _ h ↦ Option.some.inj h)).mp
  rw [← hm, ← he, List.map_ofFn]
  simp only [SourceInventory.ofSlots, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have ht := isTouched_of_source_endpoint A w (partialSlotEquiv A w i).1
    (partialSlotEquiv A w i).2
  have hne : affectedOwner A (endpoints w (partialSlotEquiv A w i).1).1 ≠
      affectedOwner A (endpoints w (partialSlotEquiv A w i).1).2 := by
    rw [← (partialSlot_spec A w i).1, ← (partialSlot_spec A w i).2.1]
    exact ((partialSlots A w).get i).distinct
  simp only [Function.comp_apply, substitutedSourceAt, dite_eq_left ht,
    PairSource.mapOwner, dite_eq_right hne,
    (partialSlot_spec A w i).1, (partialSlot_spec A w i).2.1, partialSlotChoice]

/-- The same canonical residual evaluates every retained-source substitution.
Only source vectors absorbed into exterior local operations must remain original;
all retained vectors may be arbitrary. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–434. -/
theorem eval_partialResidual_prepare_substituted (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (hη : ∀ e ξ, A (endpoints w e).1 = false → A (endpoints w e).2 = false →
      η e ξ = sourceVectorAt w e ξ) (ξ : Choices A w) :
    (partialResidual A w ξ).eval ∘L
        (SourceInventory.prepareSlots (partialSlots A w)
          (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
          (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
          (fun i ↦ η (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i))
          (Layout.mapOwner (affectedOwner A) a)).eval =
      (partialWithSources A w η ξ).eval := by
  rw [← residualInSlots_partialWithSources A w η hη ξ]
  exact Word.eval_residualInSlots_prepare _ _ _ _ _ _
    (ofSlots_partialWithSources A w η ξ)

end TNLean.PEPS.PairEffect.SourceCircuit
