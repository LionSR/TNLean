/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyGrouping

/-!
# Canonical party grouping under equality of register lists

Equal register lists determine the same grouping isometry. This statement is
shared by the physical/private concatenation, owner relabelling, and empty-owner
coordinate arguments.

## References

* *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
  September 24, 2026; `04-compression.tex`, lines 409–417 and 565–588.
-/

namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- Identifying equal register lists preserves the canonical grouped vector. -/
theorem groupByPartyIso_apply_heq (ps : List P) {a b : Layout P}
    (h : a = b) (hn : ps.Nodup) (ha : ∀ r ∈ a, r.owner ∈ ps)
    (hb : ∀ r ∈ b, r.owner ∈ ps) {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq (groupByPartyIso ps a hn ha x) (groupByPartyIso ps b hn hb y) := by
  cases h
  cases hxy
  rfl

end TNLean.PEPS.PairEffect
