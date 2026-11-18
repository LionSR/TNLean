/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Balanced recursive interval spaces

An interval is divided into two adjacent intervals until its length is at
most a prescribed positive width. The retained space is the full local
space at a leaf and the actual chosen merge operation at an internal node.
This is an auxiliary recursive construction for ALVV,
arXiv:1602.08828v2, the merge algorithm, lines 1662–1677, and the
degenerate-ground-space analysis, lines 1777–1817.

The operation is not assumed to have any analytic property in the
definition. An induction transfers a separately proved leaf and merge
invariant to the actual recursively constructed spaces. No probability or
efficient representation is asserted.
-/

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- The actual intervals whose lengths exceed the leaf width. Supporting
ALVV, arXiv:1602.08828v2, merge geometry, lines 1662–1677. -/
abbrev LongIntervalIndex (L width : ℕ) :=
  {J : ℕ × ℕ // J.1 ≤ J.2 ∧ J.2 ≤ L ∧ width < J.2 - J.1}

/-- A retained-space operation on actual adjacent interval coordinates.
Supporting ALVV, arXiv:1602.08828v2, merge algorithm, lines 1662–1677. -/
abbrev IntervalMergeOperation (L q : ℕ) :=
  ∀ (p k r : ℕ), p ≤ k → k ≤ r →
    Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)) →
    Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)) →
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))

/-- The actual balanced recursion, with the whole local space retained at
short leaves. Supporting ALVV, arXiv:1602.08828v2, merge algorithm,
lines 1662–1677. The leaf width and operation are fixed before the recursion. -/
noncomputable def balancedIntervalSpace {L q : ℕ} (operation : IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width) (p r : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  if hshort : r - p ≤ width then ⊤ else
    let k := p + (r - p) / 2
    operation p k r (by omega) (by omega)
      (balancedIntervalSpace operation width hwidth p k)
      (balancedIntervalSpace operation width hwidth k r)
termination_by r - p
decreasing_by all_goals omega

/-- A short leaf is exactly the full local space. Supporting ALVV,
arXiv:1602.08828v2, merge initialization, lines 1650–1662. -/
theorem balancedIntervalSpace_of_short {L q width p r : ℕ}
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ width)
    (hshort : r - p ≤ width) :
    balancedIntervalSpace operation width hwidth p r = ⊤ := by
  rw [balancedIntervalSpace]
  split
  · rfl
  · contradiction

/-- A leaf and parent invariant holds for every actual recursively selected
space, when the parent step may use that the cut is the actual midpoint.
Supporting ALVV, arXiv:1602.08828v2, merge algorithm, lines 1662–1677.
The midpoint lets an invariant depend on the level of a node through its
length, as for the shrinking low-density windows of `t:alg2`, lines 1869–1878. -/
theorem balancedIntervalSpace_invariant_of_midpoint {L q width : ℕ}
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (hnode : ∀ (p r : ℕ) (hpk : p ≤ p + (r - p) / 2) (hkr : p + (r - p) / 2 ≤ r),
      r ≤ L → width < r - p →
      ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p (p + (r - p) / 2) → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L (p + (r - p) / 2) r → Fin q))),
      P p (p + (r - p) / 2) S1 → P (p + (r - p) / 2) r S2 →
        P p r (operation p (p + (r - p) / 2) r hpk hkr S1 S2))
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    P p r (balancedIntervalSpace operation width hwidth p r) := by
  suffices ∀ n p r : ℕ, r - p = n → p ≤ r → r ≤ L →
      P p r (balancedIntervalSpace operation width hwidth p r) from
    this (r - p) p r rfl hpr hrL
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen hpr hrL
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalSpace_of_short operation hwidth hshort]
      exact hleaf p r hpr hrL hshort
    · have hpk : p ≤ p + (r - p) / 2 := by omega
      have hkr : p + (r - p) / 2 ≤ r := by omega
      have hS1 := ih (p + (r - p) / 2 - p) (by omega) p (p + (r - p) / 2) rfl hpk
        (hkr.trans hrL)
      have hS2 := ih (r - (p + (r - p) / 2)) (by omega) (p + (r - p) / 2) r rfl hkr hrL
      have hdef : balancedIntervalSpace operation width hwidth p r =
          operation p (p + (r - p) / 2) r hpk hkr
            (balancedIntervalSpace operation width hwidth p (p + (r - p) / 2))
            (balancedIntervalSpace operation width hwidth (p + (r - p) / 2) r) := by
        rw [balancedIntervalSpace]
        split
        · contradiction
        · rfl
      rw [hdef]
      exact hnode p r hpk hkr hrL (by omega) _ _ hS1 hS2

/-- A leaf and parent invariant holds for every actual recursively selected
space. Supporting ALVV, arXiv:1602.08828v2, merge algorithm,
lines 1662–1677. The conclusion concerns the defined recursion, rather than
a supplied family of final viable spaces. -/
theorem balancedIntervalSpace_invariant {L q width : ℕ}
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (hnode : ∀ (p k r : ℕ) (hpk : p ≤ k) (hkr : k ≤ r), r ≤ L → width < r - p →
      ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))),
      P p k S1 → P k r S2 → P p r (operation p k r hpk hkr S1 S2))
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    P p r (balancedIntervalSpace operation width hwidth p r) :=
  balancedIntervalSpace_invariant_of_midpoint operation hwidth P hleaf
    (fun p r hpk hkr hrL hlong ↦ hnode p _ r hpk hkr hrL hlong) p r hpr hrL

end TNLean.MPS.AreaLaw
