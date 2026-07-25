/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.CyclicDecomposition

open scoped BigOperators

/-!
# Periodic-sector blocking constructions

This module defines the elementary blocking data used by periodic-sector arguments:

* the gcd-based block count for blocking by an arbitrary `p`;
* a concrete orbit-sum projection builder (`∑ l, T^[l](Q)`).
-/

namespace MPSTensor

/-! ## GCD blocking arithmetic (Lemma 2.5) -/

/-- Number of periodic blocks after blocking period-`m` data by `p`: `gcd(m,p)`. -/
def periodicBlockCount (m p : ℕ) : ℕ := Nat.gcd m p

@[simp] theorem periodicBlockCount_comm (m p : ℕ) :
    periodicBlockCount m p = periodicBlockCount p m := by
  simp [periodicBlockCount, Nat.gcd_comm]

@[simp] theorem periodicBlockCount_self (m : ℕ) :
    periodicBlockCount m m = m := by
  simp [periodicBlockCount]

/-! ## Orbit-sum projection builder (Lemma 2.4 lift pattern) -/

/-- Orbit sum `R = ∑_{l < m} (T^[l]) Q` used in the cyclic-sector lift. -/
noncomputable def orbitSumProjection {D m : ℕ} (T : MatrixEnd D) (Q : MatrixAlg D) :
    MatrixAlg D :=
  ∑ l : Fin m, (T ^ (l : ℕ)) Q

end MPSTensor
