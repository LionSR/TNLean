/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Defs
import TNLean.Lattice.Sheet.StackSourceBoundedChange

/-!
# Stacks of sheets

In the protocol of the one-dimensional note the memory is a list of sheets followed by idle
registers, and its reference vector is the product of the reference vectors of the sheets; a
change of one sheet, or of two adjacent sheets, is lifted to the whole stack with the other
sheets left untouched. The stack layer of `TNLean.Lattice.Sheet.Stack` and its bounded changes
are stated for any type of sheets with registers and reference vectors. This file reads them at
the sheets of `TNLean.Lattice.Sheet.Defs`, whose reference vector is `Ω` placed in the raw
registers, and records that this reference vector has the norm of `Ω`.

* `Sheet.refFamily Ω`: the reference vector of each sheet.
* `Sheet.HasBoundedChange`, `Sheet.HasSourceBoundedChange`: bounded changes of a stack of
  sheets, the general predicates read at `Sheet.refFamily Ω`.
* `Sheet.norm_framesVec`: for a unit vector `Ω`, the reference vector of a stack of sheets is a
  unit vector.
* `Sheet.pairRef_eq_twoRegIso_symm`: the reference vector of two adjacent sheets is `Ω ⊗ Ω` in
  the canonical coordinates of the two sheets, the vector compared in `Sheet.exchange_bounded`.

These are original proofs; no OpenAI Lean code is copied or adapted.

## References

* One-dimensional note, `docs/notes/one_dimensional_note/part2b_mps_protocol.tex`, lines 47–68
  (distributed constructions, bounded changes, sheets and their reference vectors).
* Polynomial-PEPS manuscript (September 24, 2026), `06-geometry.tex`, lines 39–41, 572–583 and
  658–667.
-/

noncomputable section

open EuclideanSpace
open scoped TensorProduct
open TNLean.PEPS.EncodedFrame TNLean.PEPS.PairEffect

namespace TNLean.Lattice

namespace Sheet

variable {ι Party : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- The reference vector `Ω` placed in the registers of each sheet. -/
abbrev refFamily (Ω : EuclideanSpace ℂ (ι → Fin q)) : (S : Sheet ι Party) → Mem (S.regs q) :=
  fun S => S.regRef Ω

/-- **A bounded change of a stack of sheets**: `Lattice.HasBoundedChange` at the reference
vectors `Ω` of the sheets.

One-dimensional note, `part2b_mps_protocol.tex`, lines 47–64. -/
abbrev HasBoundedChange (Ω : EuclideanSpace ℂ (ι → Fin q)) (Ss Ss' : List (Sheet ι Party))
    {ℓ : Layout Party} (ξ : Mem ℓ) (S : Set Party) (r K : ℕ) (ε : ℝ) : Prop :=
  Lattice.HasBoundedChange (refFamily Ω) Ss Ss' ξ S r K ε

/-- **A bounded change of a stack of sheets with bounded pair sources**:
`Lattice.HasSourceBoundedChange` at the reference vectors `Ω` of the sheets.

One-dimensional note, `part2b_mps_protocol.tex`, lines 47–64. -/
abbrev HasSourceBoundedChange (Ω : EuclideanSpace ℂ (ι → Fin q)) (Ss Ss' : List (Sheet ι Party))
    {ℓ : Layout Party} (ξ : Mem ℓ) (S : Set Party) (r K rs : ℕ) (ε : ℝ) : Prop :=
  Lattice.HasSourceBoundedChange (refFamily Ω) Ss Ss' ξ S r K rs ε

/-- The reference vector of every sheet has norm at most one when `‖Ω‖ ≤ 1`, the hypothesis of
the norm-dependent results of the stack layer. -/
theorem norm_refFamily_le {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (S : Sheet ι Party) : ‖refFamily Ω S‖ ≤ 1 :=
  S.norm_regRef_le hΩ

/-- **Normalized sheets.** If `‖Ω‖ = 1`, the reference vector of a stack of sheets without idle
registers has norm one. -/
theorem norm_framesVec {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (Ss : List (Sheet ι Party)) : ‖framesVec (refFamily Ω) Ss‖ = 1 := by
  rw [norm_stackVec, List.map_congr_left fun S _ => by rw [refFamily, S.norm_regRef, hΩ]]
  simp

/-- The reference vector of two adjacent sheets is `Ω ⊗ Ω` in their canonical coordinates. -/
theorem pairRef_eq_twoRegIso_symm (S₁ S₂ : Sheet ι Party) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    pairRef (refFamily Ω) S₁ S₂ = (twoRegIso q S₁ S₂).symm (vecKron Ω Ω) :=
  appendIso_symm_regRef q S₁ S₂ Ω

end Sheet

end TNLean.Lattice
