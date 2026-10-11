/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AffectedOwners
import TNLean.PEPS.Approximation.LayoutOwnerMap

/-! # Exterior registers of an untouched gate -/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.PairEffect.Layout

/-- If no participating party is affected, every placed register has exterior owner.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem affectedOwner_mapOwner_eq_none {P C : Type} (A : P → Bool) (owner : C → P)
    (h : ¬ ∃ p, A (owner p) = true) (a : Layout C) :
    ∀ r ∈ Layout.mapOwner owner a, affectedOwner A r.owner = none := by
  rintro r hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
  exact (affectedOwner_eq_none A _).mpr
    (Bool.eq_false_iff.mpr (fun hp ↦ h ⟨s.owner, hp⟩))

end TNLean.PEPS.PairEffect.Layout
