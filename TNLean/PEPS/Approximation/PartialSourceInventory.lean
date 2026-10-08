/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedSourceComposition

/-! # Allowed partial branches and their original source occurrences -/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Every partial branch is allowed: expanded gates use their normalized source
branches, and untouched gates use their complete contractions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem isAllowed_partialWord (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsAllowed) (ξ : Choices A w) :
    (partialWord A w ξ).IsAllowed := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw hw.1 ξ.1, ihv hw.2 ξ.2⟩
  | localMap p ha hb T tail =>
      exact Word.isAllowed_mapOwner _ (.localMap p ha hb T tail) hw
  | @gate C ι _ _ owner a b c G tail =>
      classical
      dsimp only [partialWord]
      split
      · apply Word.isAllowed_mapOwner
        apply Word.isAllowed_appendTail
        apply Word.isAllowed_mapOwner
        exact G.branchWord_isAllowed _
      · exact (Word.groupedBlockMap_spec _ _ _ _ _ _ _
          (G.norm_evalAtOwners_le_one owner) _).1
  | swap r s tail => exact Word.isAllowed_mapOwner _ (.swap r s tail) trivial
  | frame r w ih => exact ih hw ξ

/-- The original ordered sources of just the gates whose branches are chosen.
The gate inventory uses its actual common source positions and vector family.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def expandedSources (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    Choices A w → SourceInventory P
  | _, _, .id _, _ => []
  | _, _, .comp w v, ξ => expandedSources A v ξ.2 ++ expandedSources A w ξ.1
  | _, _, .localMap .., _ => []
  | _, _, @SourceCircuit.gate _ C ι _ _ owner _ _ _ G _, ξ => by
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · have i : ι := by simpa only [Choices, ite_eq_left h] using ξ
        exact SourceInventory.mapOwner owner (SourceInventory.ofSlots G.slots
          (fun e ↦ euc (Fin (G.leftDim e))) (fun e ↦ euc (Fin (G.rightDim e)))
          (G.vector i))
      · exact []
  | _, _, .swap .., _ => []
  | _, _, .frame _ w, ξ => expandedSources A w ξ

/-- The partial branch retains exactly the original expanded-gate sources whose
owners remain distinct, in their original occurrence order.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem sources_partialWord (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    (partialWord A w ξ).sources =
      SourceInventory.mapOwner (affectedOwner A) (expandedSources A w ξ) := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simp only [partialWord, Word.sources, expandedSources,
        SourceInventory.mapOwner_append, ihw, ihv]
  | localMap p ha hb T tail =>
      simp only [partialWord, Word.sources_mapOwner, Word.sources, expandedSources]
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · simp only [partialWord, expandedSources, dite_eq_left h,
          Word.sources_mapOwner, Word.sources_appendTail, G.sources_branchWord]
      · simp only [partialWord, expandedSources, dite_eq_right h,
          SourceInventory.mapOwner_nil]
        exact (Word.groupedBlockMap_spec _ _ _ _ _ _ _
          (G.norm_evalAtOwners_le_one owner) _).2
  | swap => rfl
  | frame r w ih => exact ih ξ

/-- Every surviving occurrence comes from an expanded gate, has an affected
endpoint, and retains its complete source vector and halfspaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem mem_sources_partialWord (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w)
    (t : PairSource (Option {p // A p = true})) :
    t ∈ (partialWord A w ξ).sources ↔
      ∃ s ∈ expandedSources A w ξ,
        ∃ h : A s.left = true ∨ A s.right = true,
          t = ⟨affectedOwner A s.left, affectedOwner A s.right,
            (s.affectedOwner_ne_iff A).mpr h, s.leftSpace, s.rightSpace, s.vector⟩ := by
  rw [sources_partialWord]
  exact SourceInventory.mem_mapOwner_affectedOwner A (expandedSources A w ξ) t

end TNLean.PEPS.PairEffect.SourceCircuit
