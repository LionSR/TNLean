/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Index.CompositionIndex
import TNLean.MPS.CanonicalForm.SimpleMPU.GroupRepresentation
import TNLean.MPS.MPU.Index.RepresentativeIndexTensorProduct
import TNLean.MPS.MPU.Index.RepresentativeIndex

/-!
# The MPU index of a finite-group representation

The public index of an MPU representation is additive under group multiplication
and vanishes at the identity. For a finite group, every element has finite order,
so its index is zero. Simplicity and a supplied canonical-form representative are
not needed: the operator representation laws and the existing public index
suffice. The physical dimension is positive because the tensor family is
injective and each bond dimension is positive.

Reference: arXiv:2502.20257, lines 1403–1407 and the finite-order remark at line 1547.

## Source-leg dimensions in a finite-group MPU representation

Every simple injective tensor in an exact finite-group representation has
right and left source-cut ranks equal to its physical dimension. Finite order
first forces its index to vanish. Injectivity identifies the public index
with the logarithmic expression in the original source cuts, and simplicity
gives their product \(r\ell=d^2\). Thus \(r=\ell=d\).

Source: arXiv:2502.20257, the simple injective representation at
lines 1403--1407 and the finite-order remark at line 1547.
-/

section

open scoped Matrix

namespace MPOTensor.GroupFamily

universe u

variable {G : Type u} [Group G] {d : ℕ}

/-- Injectivity and the positive bond dimension force a nonzero physical dimension.
This is the nonzero-dimensional convention of arXiv:2502.20257, lines 198–209,
derived here from its injective representation hypotheses. -/
theorem IsRawRepresentation.neZero_phys (F : GroupFamily G d)
    (hF : F.IsRawRepresentation) : NeZero d := by
  have h : NeZero (d * d) := Kraus.neZero_d_of_isInjective
    ((MPOTensor.isInjective_toMPSTensor_iff _).2 (hF.isInjective 1))
  exact ⟨fun hd => h.out (by simp [hd])⟩

/-- The identity element has public MPU index zero.
Source: arXiv:2502.20257, finite-order remark at line 1547. -/
theorem IsRawRepresentation.index_one (F : GroupFamily G d) (hF : F.IsRawRepresentation) :
    letI : NeZero d := hF.neZero_phys F
    ((hF.isMPUPos 1).isMPU).index = 0 := by
  let : NeZero d := hF.neZero_phys F
  rw [((hF.isMPUPos 1).isMPU).index_eq_of_mpo_eq
    (identityMPUTensor_isMPU d) (by
      intro N hN
      rw [hF.operator_one N (by omega), mpo_identityMPUTensor]),
    IsMPU.index_identityMPUTensor]

/-- The public MPU index is additive on the represented group.
Source: arXiv:2502.20257, operator multiplication at lines 1403–1407 and
finite-order remark at line 1547; CPSV17, Theorem `IndexTh` (ii), lines 824–845. -/
theorem IsRawRepresentation.index_mul (F : GroupFamily G d)
    (hF : F.IsRawRepresentation) (g h : G) :
    letI : NeZero d := hF.neZero_phys F
    ((hF.isMPUPos (g * h)).isMPU).index =
      ((hF.isMPUPos g).isMPU).index + ((hF.isMPUPos h).isMPU).index := by
  let : NeZero d := hF.neZero_phys F
  rw [((hF.isMPUPos (g * h)).isMPU).index_eq_of_mpo_eq
    (((hF.isMPUPos g).isMPU).mulTensor ((hF.isMPUPos h).isMPU)) (by
      intro N hN
      rw [mpo_mulTensor]
      exact (hF.operator_mul g h N (by omega)).symm),
    IsMPU.index_mulTensor]

/-- Finite order forces the public representative-defined MPU index to vanish.
Source: arXiv:2502.20257, line 1547. No simplicity or canonical-form datum is assumed. -/
theorem IsRawRepresentation.index_eq_zero [Finite G]
    (F : GroupFamily G d) (hF : F.IsRawRepresentation) (g : G) :
    letI : NeZero d := hF.neZero_phys F
    ((hF.isMPUPos g).isMPU).index = 0 := by
  let : NeZero d := hF.neZero_phys F
  let idx : G → ℝ := fun x => ((hF.isMPUPos x).isMPU).index
  have hi1 : idx 1 = 0 := hF.index_one F
  have himul (x y : G) : idx (x * y) = idx x + idx y := hF.index_mul F x y
  have hpow (n : ℕ) : idx (g ^ n) = (n : ℝ) * idx g := by
    induction n with
    | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, hi1]
    | succ n ih =>
      rw [pow_succ, himul, ih, Nat.cast_add, Nat.cast_one]
      ring
  have h := hpow (orderOf g)
  rw [pow_orderOf_eq_one, hi1] at h
  have hn : (orderOf g : ℝ) ≠ 0 := by
    exact_mod_cast (isOfFinOrder_of_finite g).orderOf_pos.ne'
  exact (mul_eq_zero.mp h.symm).resolve_left hn

end MPOTensor.GroupFamily

end

section

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

end
