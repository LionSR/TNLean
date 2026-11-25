/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Sheet.Defs
import TNLean.PEPS.Approximation.Frames.TagRegisters

/-!
# The registers of an encoded frame

A sheet has one raw register `ℂ^q` at each site, with a specified owner for each register, and
an encoded frame has in addition one tag register for each hole, held by a specified party
(`05-frames.tex`, lines 13–20 and Definition 6.1). This file reads these registers as a system
of the parties: at every party, the tags of the holes it holds and the raw configurations of the
sites it owns (`layoutSystem`, `Frame.system`). The configurations of this system are the
canonical coordinates `TagSpace × (Λ → Fin q)` in which the encodings and the operators of the
frame act (`layoutConfigEquiv`, `Frame.configEquiv`), and the reference vector `Ω_F` is read on
the system along them (`Frame.regRef`).

## Main definitions

* `EncodedFrame.layoutSystem`, `EncodedFrame.layoutConfigEquiv`: the registers of a list of
  holes and an ownership assignment, and their canonical coordinates.
* `EncodedFrame.Frame.sheet`, `EncodedFrame.Frame.system`, `EncodedFrame.Frame.configEquiv`,
  `EncodedFrame.Frame.regRef`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 13–20, 84–96, and
  Definition 6.1 `def:frame`, lines 71–82.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} [DecidableEq Party]
  {pos : ι → ℝ × ℝ}

/-! ### The registers of a frame -/

variable (q) in
/-- **The registers of a frame.** At every party, the tags of the holes of `l` it holds and the
raw configurations `ℂ^q` of the sites it owns under `own`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 13–20 (a sheet has one raw register `ℂ^q` at
each site and a specified owner for each register) and Definition 6.1 `def:frame`, lines 71–82
(a specified party holds each hole's tag). -/
abbrev layoutSystem (l : List (Hole pos q Party)) (own : ι → Party) : Party → Type :=
  fun p ↦ tagSystem l p × Sheet.system q ⟨own⟩ p

/-- **The registers of a frame in canonical coordinates.** A configuration of the registers of a
frame is a tag configuration of its holes and a configuration of all sites.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 15–19 (canonical raw reference vectors with
sites indexed by position) and 94–96 (vectors are compared in their canonical site and sheet
coordinates while the owners of their registers are specified separately). -/
def layoutConfigEquiv (l : List (Hole pos q Party)) (own : ι → Party) :
    Config (layoutSystem q l own) ≃ TagSpace l × (ι → Fin q) :=
  (Equiv.arrowProdEquivProdArrow Party (tagSystem l) (Sheet.system q ⟨own⟩)).trans
    ((tagConfigEquiv l).prodCongr (blockConfigEquiv own fun _ ↦ Fin q))

@[simp] theorem layoutConfigEquiv_apply (l : List (Hole pos q Party)) (own : ι → Party)
    (z : Config (layoutSystem q l own)) :
    layoutConfigEquiv l own z =
      (tagConfigEquiv l fun p ↦ (z p).1, fun x ↦ (z (own x)).2 ⟨x, by simp⟩) :=
  rfl

namespace Frame

variable (F : Frame pos q Party)

/-- The sheet of a frame: its raw ownership assignment. -/
abbrev sheet : Sheet ι Party := ⟨F.owner⟩

/-- **The registers of an encoded frame**: at every party, the tags of the holes it holds and
the raw configurations of the sites it owns.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 13–20 and Definition 6.1 `def:frame`,
lines 71–82. -/
abbrev system : Party → Type := layoutSystem q F.holes F.owner

/-- The registers of a frame identified with the canonical coordinates `F.Layout` of its tags
and raw sites (`05-frames.tex`, lines 94–96). -/
abbrev configEquiv : Config F.system ≃ F.Layout := layoutConfigEquiv F.holes F.owner

variable [Fintype Party]

/-- The reference vector `Ω_F` of a frame, read on the registers of the frame.
Polynomial-PEPS manuscript, `05-frames.tex`, lines 84–96. -/
def regRef [NeZero q] (Ω : EuclideanSpace ℂ (ι → Fin q)) : EuclideanSpace ℂ (Config F.system) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ F.configEquiv.symm (F.refVec Ω)

@[simp] theorem regRef_apply [NeZero q] (Ω : EuclideanSpace ℂ (ι → Fin q))
    (z : Config F.system) : F.regRef Ω z = F.refVec Ω (F.configEquiv z) := by
  simp [regRef, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

theorem norm_regRef [NeZero q] (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ‖F.regRef Ω‖ = ‖F.refVec Ω‖ :=
  LinearIsometryEquiv.norm_map _ _

theorem norm_regRef_le [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) :
    ‖F.regRef Ω‖ ≤ 1 :=
  (F.norm_regRef Ω).trans_le ((F.norm_refVec_le Ω).trans hΩ)

end Frame

end TNLean.PEPS.EncodedFrame
