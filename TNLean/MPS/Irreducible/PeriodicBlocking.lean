/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition

open scoped BigOperators

/-!
# Periodic-sector blocking helpers

This module records lightweight definitions used by periodic-sector arguments:

* the gcd-based block count/period for blocking by an arbitrary `p`;
* a concrete orbit-sum projection builder (`∑ l, T^[l](Q)`);
* bundled predicates describing non-repetition before/after blocking.
-/

namespace MPSTensor

/-! ## GCD blocking numerics (Lemma 2.5 bookkeeping) -/

/-- Number of periodic blocks after blocking period-`m` data by `p`: `gcd(m,p)`. -/
def periodicBlockCount (m p : ℕ) : ℕ := Nat.gcd m p

/-- Period of each blocked sector: `m / gcd(m,p)`. -/
def periodicBlockPeriod (m p : ℕ) : ℕ := m / periodicBlockCount m p

@[simp] theorem periodicBlockCount_comm (m p : ℕ) :
    periodicBlockCount m p = periodicBlockCount p m := by
  simp [periodicBlockCount, Nat.gcd_comm]

@[simp] theorem periodicBlockCount_self (m : ℕ) :
    periodicBlockCount m m = m := by
  simp [periodicBlockCount]

theorem periodicBlockCount_dvd_left (m p : ℕ) :
    periodicBlockCount m p ∣ m := by
  simpa [periodicBlockCount] using Nat.gcd_dvd_left m p

theorem periodicBlockPeriod_mul_count (m p : ℕ) :
    periodicBlockPeriod m p * periodicBlockCount m p = m := by
  have hdiv : periodicBlockCount m p ∣ m := periodicBlockCount_dvd_left m p
  simpa [periodicBlockPeriod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.div_mul_cancel hdiv

/-! ## Orbit-sum projection builder (Lemma 2.4 lift pattern) -/

/-- Orbit sum `R = ∑_{l < m} (T^[l]) Q` used in the cyclic-sector lift. -/
noncomputable def orbitSumProjection {D m : ℕ} (T : MatrixEnd D) (Q : MatrixAlg D) :
    MatrixAlg D :=
  ∑ l : Fin m, (T ^ (l : ℕ)) Q

/-! ## Non-repetition predicates for sectors -/

/-- Pairwise non-repetition for a family of sector projections. -/
def NonrepeatingSectors {D m : ℕ} (P : Fin m → MatrixAlg D) : Prop :=
  Pairwise fun i j => P i ≠ P j

/-- Sector index map used by blocking with arbitrary `p`. -/
def blockedSectorIndex {m : ℕ} [NeZero m] (p : ℕ) (α : ℕ) (k : ℕ) : Fin m :=
  ⟨(α + p * k) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

/-- Blocked sector projection `P̃_α = ∑_k P_[α+pk mod m]` with `k < m / gcd(m,p)`. -/
noncomputable def blockedSectorProjection {D m : ℕ} [NeZero m]
    (P : Fin m → MatrixAlg D) (p : ℕ) (α : ℕ) : MatrixAlg D :=
  ∑ k : Fin (periodicBlockPeriod m p), P (blockedSectorIndex (m := m) p α k)

/-- Pairwise non-repetition predicate for blocked sectors. -/
def NonrepeatingBlockedSectors {D m : ℕ} [NeZero m]
    (P : Fin m → MatrixAlg D) (p : ℕ) : Prop :=
  Pairwise fun α β : Fin (periodicBlockCount m p) =>
    blockedSectorProjection (m := m) P p α ≠ blockedSectorProjection (m := m) P p β

end MPSTensor
