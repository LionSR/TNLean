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
common blocking level. The underlying `lcmPeriod` abbreviation and its basic
positivity / divisibility facts live in `TNLean.MPS.Core.BlockingInfrastructure`.
-/

namespace MPSTensor

variable {d k : ℕ}

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
    {dim : Fin k → ℕ}
    (hDim : ∀ i, 0 < dim i)
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
  intro i
  letI : NeZero (dim i) := ⟨Nat.ne_of_gt (hDim i)⟩
  simpa [commonPeriodBlocking] using
    isPrimitive_transferMap_blockTensor_of_dvd
      (d := d) (D := dim i)
      (A := blocks i)
      (p := periods i) (q := lcmPeriod periods)
      (dvd_lcmPeriod periods i) (lcmPeriod_pos hPeriodsPos) (hPrim i)

/-- The common-period blocked family has the expected physical dimension. -/
lemma commonPeriodBlocking_apply
    {dim : Fin k → ℕ}
    (blocks : (i : Fin k) → MPSTensor d (dim i)) (periods : Fin k → ℕ) (i : Fin k) :
    commonPeriodBlocking (d := d) blocks periods i =
      blockTensor (d := d) (D := dim i) (blocks i) (lcmPeriod periods) := rfl

end MPSTensor
