/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartialSourcePreparation
import TNLean.PEPS.Approximation.CommonSourcePreparation

/-!
# Fixed source registers of the all-party preparation

Each retained source occurrence contributes its two endpoint registers in the
original preparation order. Their owners and Euclidean coordinate spaces are
fixed before a monomial is chosen.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 253–267, 342–417 and 409–434.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The actual fixed registers supplied by the all-party source preparation.
Source: polynomial-PEPS 04-compression.tex, lines 253–267 and 409–434. -/
abbrev allResidualSourceLayout {a b : Layout P} (w : SourceCircuit a b) :
    Layout (Option {p : P // (fun _ : P => true) p = true}) :=
  SourceInventory.slotLayout (partialSlots (fun _ => true) w)
    (fun i => euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1))
    (fun i => euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2))

end TNLean.PEPS.PairEffect.SourceCircuit
