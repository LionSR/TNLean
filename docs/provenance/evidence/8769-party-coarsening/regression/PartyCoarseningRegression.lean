import TNLean.PEPS.Approximation.WordOwnerMap
import TNLean.PEPS.Approximation.UnitPairSource

/-!
# Regressions for grouping parties

Distinct source occurrences can acquire the same endpoint pair. They must remain
separate occurrences, while sources internal to one new party become local.
-/

noncomputable section
open scoped TensorProduct

namespace TNLean.PEPS.PairEffect.PartyCoarseningRegression

abbrev mergeLastTwo (p : Fin 3) : Bool := decide (p ≠ 0)
abbrev originalSources : SourceInventory (Fin 3) :=
  [PairSource.unit 0 1 (by decide), PairSource.unit 1 2 (by decide),
    PairSource.unit 0 2 (by decide)]
abbrev crossingUnit : PairSource Bool := PairSource.unit false true (by decide)

/-- The first and third occurrences survive in their original order, even though
both now join the same two parties. The middle source becomes internal. -/
theorem two_occurrences_one_pair :
    SourceInventory.mapOwner mergeLastTwo originalSources = [crossingUnit, crossingUnit] := by
  simp [SourceInventory.mapOwner, PairSource.mapOwner, originalSources,
    crossingUnit, PairSource.unit, mergeLastTwo]

abbrev collapse : Bool → Unit := fun _ ↦ ()
abbrev phaseWord : Word ([] : Layout Bool)
    [⟨false, HSpace.of ℂ⟩, ⟨true, HSpace.of ℂ⟩] :=
  .source (by decide) (HSpace.of ℂ) (HSpace.of ℂ) ((Complex.I : ℂ) ⊗ₜ (1 : ℂ)) []

/-- A source that becomes internal retains its nonreal phase and both prepared
registers, although its nonlocal pair-source inventory is empty. -/
theorem internal_phase_source :
    (phaseWord.mapOwner collapse).sources = [] ∧
      (phaseWord.mapOwner collapse).eval (1 : ℂ) =
        (Complex.I : ℂ) ⊗ₜ ((1 : ℂ) ⊗ₜ (1 : ℂ)) := by
  constructor
  · rw [Word.sources_mapOwner]
    simp [Word.sources, SourceInventory.mapOwner, PairSource.mapOwner, collapse]
  · simp only [Word.mapOwner, collapse, ↓reduceDIte, Word.eval_castLayouts]
    change (Word.localPairSource () (HSpace.of ℂ) (HSpace.of ℂ)
      ((Complex.I : ℂ) ⊗ₜ (1 : ℂ)) []).eval (1 : ℂ) = _
    rw [Word.eval_localPairSource]
    rfl

end TNLean.PEPS.PairEffect.PartyCoarseningRegression
