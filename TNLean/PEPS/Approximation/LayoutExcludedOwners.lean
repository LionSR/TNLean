/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutOwnerMap

/-!
# Empty restrictions after changing owners

If a selector excludes every new owner, none of the original registers is
retained. The spaces and order of those registers are arbitrary.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 233–251 and 351–381.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Layout
variable {P : Type}

/-- A selector excluding every mapped owner retains no register.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 233–251 and 351–381. -/
theorem restrict_mapOwner_eq_nil {Q : Type} (owner : P → Q) (f : Q → Bool)
    (a : Layout P) (hf : ∀ p, f (owner p) = false) :
    Layout.restrict f (Layout.mapOwner owner a) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  obtain ⟨hr, hsel⟩ := List.mem_filter.mp hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
  simp only [hf s.owner, Bool.false_eq_true] at hsel

end TNLean.PEPS.PairEffect.Layout
