/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Common-period assembly helpers for cyclic-sector blocks

This file provides lightweight helpers used to align periodic blocks to a
single global period and to transport per-block primitivity witnesses to that
common blocking level.
-/

namespace MPSTensor

variable {d k : ℕ}

/-- LCM of a finite family of periods indexed by `Fin k`. -/
noncomputable def lcmPeriod (periods : Fin k → ℕ) : ℕ :=
  Finset.univ.lcm periods

/-- Block each family member to the common `lcmPeriod`.

This keeps a uniform physical dimension across the assembled family while
allowing the bond dimension to vary with the index. The
resulting family is the basic input for common-period cyclic-sector assembly.
-/
noncomputable def commonPeriodBlocking
    {dim : Fin k → ℕ}
    (blocks : (i : Fin k) → MPSTensor d (dim i)) (periods : Fin k → ℕ) :
    (i : Fin k) → MPSTensor (blockPhysDim d (lcmPeriod periods)) (dim i) :=
  fun i => blockTensor (d := d) (D := dim i) (blocks i) (lcmPeriod periods)

/-- If each block has a primitive transfer map at its own period, then blocking the whole family
to the common LCM period preserves that primitivity witness for every member. -/
theorem isPrimitive_transferMap_commonPeriodBlocking
    {dim : Fin k → ℕ} [∀ i, NeZero (dim i)]
    (blocks : (i : Fin k) → MPSTensor d (dim i)) (periods : Fin k → ℕ)
    (hPeriodsPos : ∀ i, 0 < periods i)
    (hPrim : ∀ i,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (periods i)) (D := dim i)
          (blockTensor (d := d) (D := dim i) (blocks i) (periods i)))) :
    ∀ i,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (lcmPeriod periods)) (D := dim i)
          (commonPeriodBlocking (d := d) blocks periods i)) := by
  have hlcmPos : 0 < lcmPeriod periods := by
    have hne : lcmPeriod periods ≠ 0 := by
      refine Finset.lcm_ne_zero_iff.2 ?_
      intro i _
      exact Nat.ne_of_gt (hPeriodsPos i)
    exact Nat.pos_of_ne_zero hne
  intro i
  have hi_dvd : periods i ∣ lcmPeriod periods := Finset.dvd_lcm (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := hi_dvd
  have hm_pos : 0 < m := by
    have hmul : 0 < periods i * m := by simpa [hm] using hlcmPos
    exact Nat.pos_of_mul_pos_left hmul
  rw [show commonPeriodBlocking (d := d) blocks periods i =
      blockTensor (d := d) (D := dim i) (blocks i) (lcmPeriod periods) from rfl, hm]
  rw [← transferMap_blockTensor_blockTensor (A := blocks i) (m := periods i) (n := m)]
  rw [transferMap_blockTensor]
  exact isPrimitive_pow_of_isPrimitive _ m hm_pos (hPrim i)

/-- The common-period blocked family has the expected physical dimension. -/
theorem commonPeriodBlocking_apply
    {dim : Fin k → ℕ}
    (blocks : (i : Fin k) → MPSTensor d (dim i)) (periods : Fin k → ℕ) (i : Fin k) :
    commonPeriodBlocking (d := d) blocks periods i =
      blockTensor (d := d) (D := dim i) (blocks i) (lcmPeriod periods) := rfl

end MPSTensor
