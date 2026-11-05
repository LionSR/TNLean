/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import QICLean.Probability.RankUnitaryProductHaar

/-!
# Independent Haar choices for interval endpoints

One fixed finite product supplies independent sampling variables for every
pair of possible interval endpoints. A balanced recursion uses only the
coordinates belonging to its actual internal intervals. Keeping the unused
coordinates permits one probability space to be fixed before the retained
subspace ranks are known. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.
-/

open MeasureTheory

namespace TNLean.MPS.AreaLaw

/-- A rank-independent sampling variable for each possible pair of interval
endpoints. The individual variable contains a Haar-unitary coordinate for
each possible rank of that interval's physical space. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
abbrev IntervalSamplingChoices (L q : ℕ) :=
  (J : Fin (L + 1) × Fin (L + 1)) →
    Matrix.rankUnitaryProduct (Fintype.card (interval L J.1.val J.2.val → Fin q))

/-- The fixed independent probability law of the interval sampling choices.
It precedes every retained subspace and every input rank. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
noncomputable def intervalSamplingMeasure (L q : ℕ) : Measure (IntervalSamplingChoices L q) :=
  Measure.pi (fun J : Fin (L + 1) × Fin (L + 1) ↦
    Matrix.rankUnitaryHaar (Fintype.card (interval L J.1.val J.2.val → Fin q)))

instance instIsProbabilityMeasureIntervalSamplingMeasure (L q : ℕ) :
    IsProbabilityMeasure (intervalSamplingMeasure L q) := by
  unfold intervalSamplingMeasure
  infer_instance

/-- Every interval coordinate has its prescribed rank-independent Haar
product marginal. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817. -/
theorem measurePreserving_intervalSamplingChoice (L q : ℕ)
    (J : Fin (L + 1) × Fin (L + 1)) :
    MeasurePreserving (fun U : IntervalSamplingChoices L q ↦ U J)
      (intervalSamplingMeasure L q)
      (Matrix.rankUnitaryHaar (Fintype.card (interval L J.1.val J.2.val → Fin q))) :=
  measurePreserving_eval (fun J : Fin (L + 1) × Fin (L + 1) ↦
    Matrix.rankUnitaryHaar (Fintype.card (interval L J.1.val J.2.val → Fin q))) J

end TNLean.MPS.AreaLaw
