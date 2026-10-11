/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceRegisters

/-!
# Absence of source registers at the exterior owner

When every original party is selected, the fixed source preparation assigns
both registers of each source to selected parties. The exterior owner therefore
has no source registers. This concerns the fixed register layout and is
independent of any choice of monomial or source vector.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 253–267, 342–417 and 409–434.
-/

namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The fixed all-party source layout has no registers at the exterior owner.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267, 342–417 and 409–434. -/
theorem restrict_allResidualSourceLayout_isNone {a b : Layout P}
    (w : SourceCircuit a b) :
    Layout.restrict Option.isNone w.allResidualSourceLayout = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r hr hnone
  obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  simp only [PairSource.layout, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [(partialSlot_spec (fun _ ↦ true) w i).1, affectedOwner,
      ↓reduceDIte, Option.isNone_some, Bool.false_eq_true] at hnone
  · simp only [(partialSlot_spec (fun _ ↦ true) w i).2.1, affectedOwner,
      ↓reduceDIte, Option.isNone_some, Bool.false_eq_true] at hnone

end TNLean.PEPS.PairEffect.SourceCircuit
