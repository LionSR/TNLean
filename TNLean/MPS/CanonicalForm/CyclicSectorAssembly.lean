import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Common-period assembly helpers for cyclic-sector blocks

This file provides lightweight definitions used to align periodic blocks to a
single global period.
-/

namespace MPSTensor

variable {d D k : ℕ}

/-- LCM of a finite family of periods indexed by `Fin k`. -/
noncomputable def lcmPeriod (periods : Fin k → ℕ) : ℕ :=
  Finset.univ.lcm periods

/-- Block each family member to the common `lcmPeriod`.

This keeps a uniform physical dimension across the assembled family. The
periodicity witness is carried as input because this is the intended API point
for cyclic-sector assembly.
-/
noncomputable def commonPeriodBlocking
    (blocks : Fin k → MPSTensor d D) (periods : Fin k → ℕ)
    (_hPeriodic : ∀ i, IsPeriodic (periods i) (blocks i)) :
    Fin k → MPSTensor (blockPhysDim d (lcmPeriod periods)) D :=
  fun i => blockTensor (d := d) (D := D) (blocks i) (lcmPeriod periods)

/-- Blocking a sector-irreducible witness transfers to any multiple period. -/
def IsSectorIrreducible (A : MPSTensor d D) (p : ℕ) (_u : Fin p) : Prop :=
  _root_.IsPrimitive
    (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p))

theorem sectorIrreducible_of_blocked
    (A : MPSTensor d D) {p : ℕ} [NeZero D] (u : Fin p)
    (hIrr : IsSectorIrreducible (d := d) (D := D) A p u) (m : ℕ) (hm : 0 < m) :
    IsSectorIrreducible (d := d) (D := D)
      A (p * m) ⟨0, Nat.mul_pos (Nat.zero_lt_of_lt u.is_lt) hm⟩ := by
  dsimp [IsSectorIrreducible] at hIrr ⊢
  have hp : 0 < p := Nat.zero_lt_of_lt u.is_lt
  have hpm : 0 < p * m := Nat.mul_pos hp hm
  exact isPrimitive_transferMap_blockTensor_of_dvd
    (A := A) (p := p) (q := p * m) (dvd_mul_right p m) hpm hIrr

end MPSTensor
