/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitDecomposition

/-!
# Periods of roots with irreducible powers

If a periodic tensor remains irreducible after blocking by `p` sites, its
period is coprime to `p`. This necessary condition restricts the root
selection problem in arXiv:1708.00029, Theorem 4.1, converse. It follows
from the orbit decomposition in Section 4.1, lines 765--806, and does not
assert existence of a root with a prescribed number of Kraus operators.
-/

open scoped Matrix

namespace MPSTensor

/-- An irreducible blocked tensor has only one orbit of cyclic sectors.
Thus its original period is coprime to the blocking length.
Source: arXiv:1708.00029, Section 4.1, lines 765--806; used in the
root-selection problem of Theorem 4.1, lines 812--818. -/
theorem IsPeriodic.coprime_of_isIrreducibleFamily_blockTensor
    {d D m : ℕ} (A : MPSTensor d D) (hA : IsPeriodic m A)
    (p : ℕ) (hIrr : Kraus.IsIrreducibleFamily (blockTensor A p)) :
    Nat.Coprime m p := by
  classical
  have : NeZero m := ⟨hA.period_pos.ne'⟩
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨dim, C, Q, V, α, P, hP, hPne, hPsum, hPorth,
    hshift, hα, hsurj, hQorbit, hQproj, hQsum, hQorth, hQcomm, rest⟩ :=
    exists_blockTensor_orbit_compression A hA p
  have hQne (j : Fin (Nat.gcd m p)) : Q j ≠ 0 := by
    rw [hQorbit j]
    exact orbitProjection_ne_zero α P hP hPorth hPne hsurj j
  have hQone (j : Fin (Nat.gcd m p)) : Q j = 1 := by
    by_contra hj
    apply hIrr
    refine ⟨Q j, hQproj j, hQne j, hj, ?_⟩
    intro i
    rw [Matrix.mul_assoc, ← hQcomm j i, ← Matrix.mul_assoc,
      sub_mul, Matrix.one_mul, (hQproj j).2, sub_self, Matrix.zero_mul]
  have hsub : Subsingleton (Fin (Nat.gcd m p)) := by
    constructor
    intro j k
    by_contra hjk
    have h := hQorth j k hjk
    rw [hQone j, hQone k, Matrix.one_mul] at h
    exact one_ne_zero h
  have hle : Nat.gcd m p ≤ 1 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_one_iff.mpr hsub.allEq)
  have hpos : 0 < Nat.gcd m p := Nat.gcd_pos_of_pos_left p hA.period_pos
  exact Nat.le_antisymm hle hpos

end MPSTensor
