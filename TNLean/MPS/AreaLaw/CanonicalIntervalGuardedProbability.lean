/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalSamplingSections

/-!
# True guarded sections of the actual sampled parent

A fixed whole seed determines the two baseline child spaces. Replacing
their longer parent's coordinate leaves both children unchanged and uses
that coordinate in the same literal parent operation. Consequently a
fixed-child failure estimate bounds the actual guarded section. If either
baseline child fails, the guarded section is empty.

This is a conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817. The fixed-child failure estimate
is an explicit premise to be established for the physical family; no
measurability, independent comparison event, or basis-law identification
is assumed.
-/

open MeasureTheory
open scoped ENNReal

namespace TNLean.MPS.AreaLaw

/-- The true own-coordinate guarded section is bounded by the actual
fixed-child canonical-parent failure estimate. The children come from
the same baseline whole seed and are unchanged by the update. This is a
conditional probability auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817. -/
theorem rankUnitaryHaar_guarded_canonicalIntervalSamplingTree_update_le
    {L q width : ℕ} (D s : ℕ) (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (hlong : width < r - p) (U : IntervalSamplingChoices L q) (beta : ℝ≥0∞) :
    let k := p + (r - p) / 2
    let hpk : p ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    let J : LongIntervalIndex L width := ⟨(p, r), hpr, hrL, hlong⟩
    let coord : Fin (L + 1) × Fin (L + 1) :=
      (⟨p, Nat.lt_succ_of_le (hpr.trans hrL)⟩, ⟨r, Nat.lt_succ_of_le hrL⟩)
    let operation := canonicalIntervalSamplingOperation D s N F xi
    let left := balancedIntervalSpace (operation U) width hwidth p k
    let right := balancedIntervalSpace (operation U) width hwidth k r
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    (P p k left → P k r right →
      Matrix.rankUnitaryHaar (Fintype.card (interval L p r → Fin q))
        {v | ¬P p r (canonicalSampledIntervalInterleavedTrim L q p r D s (F J) xi
          (adjacentIntervalMerge L q p k r hpk hkr left right) v)} ≤ beta) →
    Matrix.rankUnitaryHaar (Fintype.card (interval L p r → Fin q))
      {v | Function.update U coord v ∈ guardedIntervalFailure operation width hwidth P (p, r)} ≤
        beta := by
  intro k hpk hkr J coord operation left right P hfixed
  have hleft (v : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
      balancedIntervalSpace (operation (Function.update U coord v)) width hwidth p k = left :=
    canonicalIntervalSamplingTree_update_of_length_lt D s hwidth N F xi
      p k hpk (hkr.trans hrL) U coord v (by dsimp only [k, coord]; omega)
  have hright (v : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
      balancedIntervalSpace (operation (Function.update U coord v)) width hwidth k r = right :=
    canonicalIntervalSamplingTree_update_of_length_lt D s hwidth N F xi
      k r hkr hrL U coord v (by dsimp only [k, coord]; omega)
  have hparent (v : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
      balancedIntervalSpace (operation (Function.update U coord v)) width hwidth p r =
        canonicalSampledIntervalInterleavedTrim L q p r D s (F J) xi
          (adjacentIntervalMerge L q p k r hpk hkr left right) v :=
    canonicalIntervalSamplingTree_update_parent D s hwidth N F xi p r hpr hrL hlong U v
  by_cases hchildren : P p k left ∧ P k r right
  · apply (measure_mono ?_).trans (hfixed hchildren.1 hchildren.2)
    intro v hfailure
    change P p k (balancedIntervalSpace (operation (Function.update U coord v))
      width hwidth p k) ∧ P k r (balancedIntervalSpace
        (operation (Function.update U coord v)) width hwidth k r) ∧
      ¬P p r (balancedIntervalSpace (operation (Function.update U coord v))
        width hwidth p r) at hfailure
    simpa only [Set.mem_ofPred_eq, hparent] using hfailure.2.2
  · have hempty :
        {v | Function.update U coord v ∈ guardedIntervalFailure operation width hwidth P (p, r)} =
          ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hfailure
      apply hchildren
      change P p k (balancedIntervalSpace (operation (Function.update U coord v))
        width hwidth p k) ∧ P k r (balancedIntervalSpace
          (operation (Function.update U coord v)) width hwidth k r) ∧
        ¬P p r (balancedIntervalSpace (operation (Function.update U coord v))
          width hwidth p r) at hfailure
      exact ⟨(hleft v) ▸ hfailure.1, (hright v) ▸ hfailure.2.1⟩
    rw [hempty, measure_empty]
    exact bot_le

end TNLean.MPS.AreaLaw
