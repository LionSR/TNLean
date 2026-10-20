/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualSourceRegisters
import TNLean.Lattice.Compression.SourceSlotBasis

/-! # Coordinates of the actual chronological source input

The source slots and their endpoint dimensions are fixed by the original
chronology. At each slot, take the standard Euclidean bases of the two
endpoint spaces and tensor them in the original slot order. The basis of the
input to the private preparation is obtained by the canonical identification
of the source layout with that same layout followed by the empty layout.

These definitions use neither a branch choice nor a sample. In particular,
they do not replace a source vector or make an assumption about a sampled
source matrix.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 253–267, 279–355 and 565–588.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect.SourceCircuit

variable {P : Type} {a b : Layout P}

/-- The actual first endpoint space at each all-party source slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
abbrev allSourceU (w : SourceCircuit a b)
    (i : Fin (partialSlots (fun _ => true) w).length) : HSpace :=
  euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1)

/-- The actual second endpoint space at each all-party source slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
abbrev allSourceV (w : SourceCircuit a b)
    (i : Fin (partialSlots (fun _ => true) w).length) : HSpace :=
  euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2)

variable (w : SourceCircuit a b)

/-- The literal source-slot coordinate type, independent of branch choices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
abbrev allSourceLabels := ∀ i : Fin (partialSlots (fun _ => true) w).length,
  Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1 ×
    Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2

/-- The actual source-slot basis, with the original endpoint order retained.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
def allSourceBasis : OrthonormalBasis w.allSourceLabels ℂ (Mem w.allResidualSourceLayout) :=
  SourceInventory.slotBasis (partialSlots (fun _ => true) w) w.allSourceU w.allSourceV
    (fun _i => EuclideanSpace.basisFun _ ℂ) (fun _i => EuclideanSpace.basisFun _ ℂ)

/-- The actual fixed source basis on the unit-memory input of the private
preparation. Source: polynomial-PEPS 04-compression.tex, lines 253–267 and 279–355. -/
def actualSourceInputBasis (w : SourceCircuit a b) :
    OrthonormalBasis w.allSourceLabels ℂ (Mem (w.allResidualSourceLayout ++ [])) :=
  w.allSourceBasis.map (Layout.memCongr (List.append_nil w.allResidualSourceLayout).symm)

end TNLean.PEPS.PairEffect.SourceCircuit
