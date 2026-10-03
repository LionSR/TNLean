/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.StateVectorDecomposition
import TNLean.MPS.Periodic.StepOrbitSectors

/-!
# Periods of roots with irreducible powers

If a periodic tensor remains irreducible after blocking by `p` sites, its
period is coprime to `p`. This necessary condition restricts the root
selection problem in arXiv:1708.00029, Theorem 4.1, converse. It follows
from the step-orbit sectors of Section 4.1, lines 765--806, and does not
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
  obtain ⟨P, hproj, hsum, hne, hshift⟩ := exists_paper_cyclic_projectors_of_isPeriodic A hA
  let Q := stepOrbitProjection P p
  have hQproj (j : Fin (m.gcd p)) : IsOrthogonalProjection (Q j) :=
    stepOrbitProjection_isOrthogonalProjection P hproj hsum p j
  have hQone (j : Fin (m.gcd p)) : Q j = 1 := by
    by_contra hj
    apply hIrr
    refine ⟨Q j, hQproj j, stepOrbitProjection_ne_zero P hproj hsum hne p j, hj, ?_⟩
    intro i
    rw [Matrix.mul_assoc, ← stepOrbitProjection_mul_blockTensor P A hshift p j i,
      ← Matrix.mul_assoc, sub_mul, Matrix.one_mul, (hQproj j).2, sub_self, Matrix.zero_mul]
  have hsub : Subsingleton (Fin (m.gcd p)) := by
    constructor
    intro j k
    by_contra hjk
    have h := stepOrbitProjection_mul_eq_zero P hproj hsum p hjk
    change Q j * Q k = 0 at h
    rw [hQone j, hQone k, Matrix.one_mul] at h
    have : NeZero D := ⟨hA.bondDim_ne_zero⟩
    exact one_ne_zero h
  have hle : m.gcd p ≤ 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_one_iff.mpr hsub.allEq
  exact Nat.le_antisymm hle (Nat.gcd_pos_of_pos_left p hA.period_pos)

end MPSTensor
