import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Common-period assembly helpers for cyclic-sector blocks

This file provides lightweight helpers used to align periodic blocks to a
single global period and to transport per-block primitivity witnesses to that
common blocking level.
-/

namespace MPSTensor

variable {d D k : ℕ}

/-- LCM of a finite family of periods indexed by `Fin k`. -/
noncomputable def lcmPeriod (periods : Fin k → ℕ) : ℕ :=
  Finset.univ.lcm periods

/-- Block each family member to the common `lcmPeriod`.

This keeps a uniform physical dimension across the assembled family. The
resulting family is the basic input for common-period cyclic-sector assembly.
-/
noncomputable def commonPeriodBlocking
    (blocks : Fin k → MPSTensor d D) (periods : Fin k → ℕ) :
    Fin k → MPSTensor (blockPhysDim d (lcmPeriod periods)) D :=
  fun i => blockTensor (d := d) (D := D) (blocks i) (lcmPeriod periods)

/-- If each block has a primitive transfer map at its own period, then blocking the whole family
to the common LCM period preserves that primitivity witness for every member. -/
theorem isPrimitive_transferMap_commonPeriodBlocking
    [NeZero D]
    (blocks : Fin k → MPSTensor d D) (periods : Fin k → ℕ)
    (hPeriodsPos : ∀ i, 0 < periods i)
    (hPrim : ∀ i,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (periods i)) (D := D)
          (blockTensor (d := d) (D := D) (blocks i) (periods i)))) :
    ∀ i,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (lcmPeriod periods)) (D := D)
          (commonPeriodBlocking (d := d) (D := D) blocks periods i)) := by
  have hlcmPos : 0 < lcmPeriod periods := by
    have hne : lcmPeriod periods ≠ 0 := by
      refine Finset.lcm_ne_zero_iff.2 ?_
      intro i _
      exact Nat.ne_of_gt (hPeriodsPos i)
    exact Nat.pos_of_ne_zero hne
  intro i
  have hi_dvd : periods i ∣ lcmPeriod periods := Finset.dvd_lcm (Finset.mem_univ i)
  simpa [commonPeriodBlocking, lcmPeriod] using
    isPrimitive_transferMap_blockTensor_of_dvd
      (A := blocks i) (p := periods i) (q := lcmPeriod periods) hi_dvd hlcmPos (hPrim i)

/-- The common-period blocked family has the expected physical dimension. -/
theorem commonPeriodBlocking_apply
    (blocks : Fin k → MPSTensor d D) (periods : Fin k → ℕ) (i : Fin k) :
    commonPeriodBlocking (d := d) (D := D) blocks periods i =
      blockTensor (d := d) (D := D) (blocks i) (lcmPeriod periods) := rfl

end MPSTensor
