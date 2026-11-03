/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalTree
import TNLean.MPS.AreaLaw.AdjacentIntervalMerge

/-!
# Interval operations with arbitrary independent coordinates

Each long interval uses its own coordinate and the actual tensor product
of its two adjacent child spaces. The coordinate may contain several
successive samples. The retained spaces are those of the existing balanced
interval recursion. This is an auxiliary construction for ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- The genuine finite endpoint coordinate of a valid long interval.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
def LongIntervalIndex.coordinate {L width : ℕ} (J : LongIntervalIndex L width) :
    Fin (L + 1) × Fin (L + 1) :=
  (⟨J.val.1, Nat.lt_succ_of_le (J.property.1.trans J.property.2.1)⟩,
    ⟨J.val.2, Nat.lt_succ_of_le J.property.2.1⟩)

/-- Apply the prescribed parent map to its actual adjacent child merge
and its own interval coordinate. Short and out-of-range parents are set
to the full space and are unused inside a valid balanced root.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
noncomputable def independentIntervalOperation {L q width : ℕ}
    {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
    (parent : ∀ J : LongIntervalIndex L width,
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) →
      Ω (LongIntervalIndex.coordinate J) →
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
    (U : ∀ J, Ω J) : IntervalMergeOperation L q :=
  fun p k r hpk hkr S1 S2 ↦
    if hrL : r ≤ L then
      if hlong : width < r - p then
        parent ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
          (U (LongIntervalIndex.coordinate
            (⟨(p, r), hpk.trans hkr, hrL, hlong⟩ : LongIntervalIndex L width)))
      else ⊤
    else ⊤

end TNLean.MPS.AreaLaw
