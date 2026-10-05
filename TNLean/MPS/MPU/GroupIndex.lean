/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CompositionIndex
import TNLean.MPS.MPU.GroupRepresentation
import TNLean.MPS.MPU.RepresentativeIndexTensorProduct

/-!
# The MPU index of a finite-group representation

The public index of an MPU representation is additive under group multiplication
and vanishes at the identity. For a finite group, every element has finite order,
so its index is zero. Simplicity and a supplied canonical-form representative are
not needed: the operator representation laws and the existing public index
suffice. The physical dimension is positive because the tensor family is
injective and each bond dimension is positive.

Reference: arXiv:2502.20257, lines 1403–1407 and the finite-order remark at line 1547.
-/

open scoped Matrix

namespace MPOTensor.GroupFamily

universe u

variable {G : Type u} [Group G] {d : ℕ}

/-- Injectivity and the positive bond dimension force a nonzero physical dimension.
This is the nonzero-dimensional convention of arXiv:2502.20257, lines 198–209,
derived here from its injective representation hypotheses. -/
theorem IsRawRepresentation.neZero_phys (F : GroupFamily G d)
    (hF : F.IsRawRepresentation) : NeZero d := by
  have h : NeZero (d * d) := Kraus.neZero_d_of_isInjective (hF.isInjective 1)
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
