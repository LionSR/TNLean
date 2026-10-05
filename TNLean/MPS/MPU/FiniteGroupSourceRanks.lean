/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.GroupIndex
import TNLean.MPS.MPU.InjectiveSourceIndex

/-!
# Source-leg dimensions in a finite-group MPU representation

Every simple injective tensor in an exact finite-group representation has
right and left source-cut ranks equal to its physical dimension. Finite order
first forces its index to vanish. Injectivity identifies the public index
with the logarithmic expression in the original source cuts, and simplicity
gives their product \(r\ell=d^2\). Thus \(r=\ell=d\).

Source: arXiv:2502.20257, the simple injective representation at
lines 1403--1407 and the finite-order remark at line 1547.
-/

namespace MPOTensor.GroupFamily

universe u

variable {G : Type u} [Group G] [Finite G] {d : ℕ}

/-- The two source-leg dimensions of each tensor in a finite-group
representation by simple injective MPUs equal the physical dimension.
No canonical-form presentation or rank-product identity is supplied.
Source: arXiv:2502.20257, lines 1403--1407 and 1547. -/
theorem IsRepresentation.sourceRanks_eq_physDim
    (F : GroupFamily G d) (hF : F.IsRepresentation) (g : G) :
    r[F.tensor g] = d ∧ ℓ[F.tensor g] = d := by
  let : NeZero d := hF.toIsRawRepresentation.neZero_phys F
  have hU := (hF.isMPUPos g).isMPU
  have hprod := hU.rightRank_mul_leftRank_of_isInjective_of_isMPUSimple
    (hF.isInjective g) (hF.isSimple g)
  have hpos : 0 < r[F.tensor g] * ℓ[F.tensor g] := by
    rw [hprod]
    exact Nat.pow_pos (NeZero.pos d)
  have hr := Nat.pos_of_mul_pos_right hpos
  have hℓ := Nat.pos_of_mul_pos_left hpos
  apply sourceRanks_eq_physDim_of_sourceIndexValue_eq_zero
    (F.tensor g) hr hℓ (NeZero.pos d) hprod
  change (1 / 2 : ℝ) *
    (Real.logb 2 r[F.tensor g] - Real.logb 2 ℓ[F.tensor g]) = 0
  rw [← hU.index_eq_logb_of_isInjective_of_isMPUSimple
    (hF.isInjective g) (hF.isSimple g)]
  exact hF.toIsRawRepresentation.index_eq_zero F g

end MPOTensor.GroupFamily
