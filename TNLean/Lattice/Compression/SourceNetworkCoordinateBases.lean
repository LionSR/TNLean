/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualSourceRegisters
import TNLean.Lattice.Compression.AuxiliaryRegisterFiniteness
import TNLean.Lattice.PartyCircuit.PartyTensorMaps
import TNLean.Lattice.Compression.SourcePreparationCoordinates

/-!
# Finite orthonormal coordinates for the source and discarded memories

The original Euclidean endpoint spaces give finite-dimensional source registers.
Selecting the registers at one owner preserves finite dimensionality. The same
argument applies to the original discarded registers under their register-wise
finite-dimensionality assumption. The resulting orthonormal bases are indexed
by the dimension of the actual memory; no bound on private dimensions is used.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 17–19, 253–267, 409–434 and 565–588.
-/

noncomputable section

namespace TNLean
open TNLean.Lattice.PartyCircuit

variable {P : Type}

namespace Lattice.PartyCircuit.SourceInventory

/-- Fixed source slots retain finite-dimensional endpoint registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
theorem finiteDimensional_registers_slotLayout (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (hU : ∀ i, FiniteDimensional ℂ (U i))
    (hV : ∀ i, FiniteDimensional ℂ (V i)) :
    ∀ r ∈ slotLayout R U V, FiniteDimensional ℂ r.space := by
  induction R with
  | nil =>
      intro r hr
      change r ∈ ([] : Layout P) at hr
      cases hr
  | cons r R ih =>
      intro t ht
      rw [slotLayout_cons] at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hU 0
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact hV 0
        · exact ih (fun i ↦ U i.succ) (fun i ↦ V i.succ)
            (fun i ↦ hU i.succ) (fun i ↦ hV i.succ) t ht

end Lattice.PartyCircuit.SourceInventory

namespace PEPS.PairEffect
private theorem finiteDimensional_mem_atParty_of_registers {Q : Type}
    (q : Q) (ℓ : Layout Q)
    (h : ∀ r ∈ ℓ, FiniteDimensional ℂ r.space) :
    FiniteDimensional ℂ (Mem (Layout.atParty q ℓ)) := by
  classical
  apply Layout.finiteDimensional_mem_of_registers
  intro r hr
  change r ∈ ℓ.filter (fun s ↦ decide (s.owner = q)) at hr
  exact h r (List.mem_filter.mp hr).1

end PEPS.PairEffect
namespace Lattice.PartyCircuit.SourceCircuit
open TNLean.PEPS.PairEffect

/-- Every retained source register has its original finite Euclidean endpoint space.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 409–434. -/
theorem finiteDimensional_allResidualSource_registers {a b : Layout P}
    (w : SourceCircuit a b) :
    ∀ r ∈ w.allResidualSourceLayout, FiniteDimensional ℂ r.space := by
  exact SourceInventory.finiteDimensional_registers_slotLayout _ _ _
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)

/-- A dimension-indexed orthonormal basis of one owner's actual retained source memory.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
def allResidualSourceBasis {a b : Layout P} (w : SourceCircuit a b)
    (q : Option {p : P // (fun _ : P ↦ true) p = true}) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (Mem (Layout.atParty q (w.allResidualSourceLayout ++ [])))))
      ℂ (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))) := by
  letI := finiteDimensional_mem_atParty_of_registers q
    (w.allResidualSourceLayout ++ [])
    (by simpa only [List.append_nil] using w.finiteDimensional_allResidualSource_registers)
  exact stdOrthonormalBasis ℂ _

/-- A dimension-indexed orthonormal basis of one owner's original discarded memory.
Only the original per-register finite-dimensionality is required.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19 and 565–588. -/
def allPartyDiscardBasis (garbage : Layout P)
    (hfinite : ∀ r ∈ garbage, FiniteDimensional ℂ r.space)
    (q : Option {p : P // (fun _ : P ↦ true) p = true}) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage)))))
      ℂ (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))) := by
  letI := finiteDimensional_mem_atParty_of_registers q
    (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage)
    (Layout.finiteDimensional_registers_mapOwner _ garbage hfinite)
  exact stdOrthonormalBasis ℂ _

end Lattice.PartyCircuit.SourceCircuit

end TNLean
