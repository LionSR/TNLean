/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.GCD.Basic

/-!
# Periodic-sector helper definitions

Small shared definitions for periodic-sector/blocking statements in the MPS canonical-form
pipeline.
-/

namespace MPSTensor

/-- Number of sectors that remain after blocking an `m`-periodic object by `p`. -/
def periodicBlockCount (m p : ℕ) : ℕ := Nat.gcd m p

/-- Period of each resulting blocked sector. -/
def periodicBlockPeriod (m p : ℕ) : ℕ := m / Nat.gcd m p

@[simp] theorem periodicBlockCount_comm (m p : ℕ) :
    periodicBlockCount m p = periodicBlockCount p m := by
  simp [periodicBlockCount, Nat.gcd_comm]

@[simp] theorem periodicBlockCount_self (m : ℕ) :
    periodicBlockCount m m = m := by
  simp [periodicBlockCount]

end MPSTensor
