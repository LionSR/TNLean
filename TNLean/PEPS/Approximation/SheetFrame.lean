/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Defs
import TNLean.PEPS.Approximation.HomogeneousOwnership
import TNLean.PEPS.Approximation.SheetStack

/-!
# Sheets as encoded frames without holes

A sheet of `TNLean.Lattice.Sheet.Defs` is an owner function on the sites. Placed in the plane by
positions of the sites, it is the encoded frame without holes with the same owners
(`Sheet.toFrame`, Definition 6.1 of the polynomial-PEPS manuscript with an empty list of holes).
This file records that the two agree: the registers of the frame are those of the sheet, its
canonical coordinates are those of the sheet with the trivial tag coordinate, its reference
vector on the registers is that of the sheet, and handing a set of sites to another party
commutes with the passage to frames.

These are original proofs; no OpenAI Lean code is copied or adapted.

## Main results

* `Lattice.Sheet.toFrame`, `Lattice.Sheet.toFrame_regs`, `Lattice.Sheet.toFrame_regIso`,
  `Lattice.Sheet.toFrame_regRef`, `Lattice.Sheet.toFrame_changeOwner`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 13–20 (sheets) and
  Definition 6.1 `def:frame`, lines 71–82.
* One-dimensional note, `docs/notes/one_dimensional_note/part2b_mps_protocol.tex`, lines 67–68
  and 165–171 (sheets without encoded holes).
-/

noncomputable section

open TNLean.PEPS.EncodedFrame TNLean.PEPS.PairEffect

namespace TNLean.Lattice.Sheet

variable {ι Party : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} (pos : ι → ℝ × ℝ)
  (S : Sheet ι Party)

/-- **A sheet as an encoded frame.** The frame without holes with the owners of the sheet. -/
abbrev toFrame : Frame pos q Party := Frame.raw S.owner

theorem toFrame_regs : (S.toFrame (q := q) pos).regs = S.regs q := rfl

/-- The canonical coordinates of the frame of a sheet are those of the sheet with the trivial tag
coordinate. -/
theorem toFrame_regIso (z : Mem (S.regs q)) :
    (S.toFrame (q := q) pos).regIso z = (unitProdIso _).symm (S.regIso q z) := by
  rw [regIso_eq_frontLayoutIso, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- The reference vector of the frame of a sheet, on its registers, is that of the sheet. -/
theorem toFrame_regRef [NeZero q] (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    (S.toFrame (q := q) pos).regRef Ω = S.regRef Ω := by
  apply (S.regIso q).injective
  rw [regRef, LinearIsometryEquiv.apply_symm_apply]
  refine (regIso_eq_frontLayoutIso q S ((S.toFrame pos).regRef Ω)).trans ?_
  change unitProdIso _ ((S.toFrame pos).regIso ((S.toFrame pos).regIso.symm
    ((S.toFrame pos).refVec Ω))) = Ω
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext c
  refine (unitProdIso_apply ((S.toFrame (q := q) pos).refVec Ω) c).trans ?_
  change (Matrix.mulVec (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) Ω.ofLp) c = Ω c
  rw [Matrix.one_mulVec]

/-- Handing the sites of `T` to `Q` commutes with the passage to frames. -/
theorem toFrame_changeOwner (T : Finset ι) (Q : Party) :
    (S.toFrame (q := q) pos).changeOwner T Q = (S.changeOwner T Q).toFrame pos := rfl

end TNLean.Lattice.Sheet
