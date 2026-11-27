/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.Probability.Sampling.RankUnitaryProductHaar
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.BalancedIntervalTree
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.CanonicalSampledIntervalInterleaved
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalGenerators

/-!
# Independent Haar choices for interval endpoints

One fixed finite product supplies independent sampling variables for every
pair of possible interval endpoints. A balanced recursion uses only the
coordinates belonging to its actual internal intervals. Keeping the unused
coordinates permits one probability space to be fixed before the retained
subspace ranks are known. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.

## The sampled operation for the existing balanced recursion

A single family of independent interval choices determines an operation
for the existing balanced interval recursion. Every valid long parent uses
its own coordinate, the actual adjacent child merge, and the specified
family's literal interleaved iteration. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.

## Recorded size bounds throughout the actual canonical sampled tree

The existing balanced recursion consumes the canonical sampled operation.
Full short leaves and every actual sampled parent satisfy one common
dimension and recorded-rank bound for every global seed, without viability
assumptions. Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1777–1817, and Figure `fig:merge-prime`, lines 1668–1670.

The bounds concern recorded spanning vectors. Joint viability probability,
all-span MPS bounds and runtime are separate conclusions.
-/

section

open ManyBody (interval)

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

end

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- One realization of the independent interval choices fixes the actual
sampled operation. The targets and families precede these choices. Short
or out-of-range parents are set to the full space; they are never used as
internal nodes of a valid balanced root. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
noncomputable def canonicalIntervalSamplingOperation {L q width : ℕ}
    (D s : ℕ) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (U : IntervalSamplingChoices L q) : IntervalMergeOperation L q :=
  independentIntervalOperation
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v) U

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- Every actually retained interval space has the common dimension and
recorded-generator rank bounds for every global seed, including histories
where viability fails. The existing balanced recursion is unchanged. -/
theorem canonicalIntervalSamplingTree_profile {L q width D s : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hleaf : q ^ width ≤ D ^ 6 * s ^ 3)
    (U : IntervalSamplingChoices L q) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
      width hwidth p r
    Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
      IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S := by
  let P := fun (p r : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L p r → Fin q))) ↦
    Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
      IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S
  apply balancedIntervalSpace_invariant (canonicalIntervalSamplingOperation D s N F xi U)
    hwidth P ?_ ?_ p r hpr hrL
  · intro p r _hpr _hrL hshort
    exact interval_top_dimension_and_rank_bounds hq hxi.le hxi1 hleaf hshort
  · intro p k r hpk hkr hrL hlong S1 S2 _hS1 _hS2
    let J : LongIntervalIndex L width := ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
    have hop : canonicalIntervalSamplingOperation D s N F xi U p k r hpk hkr S1 S2 =
        canonicalSampledIntervalInterleavedTrim L q p r D s (F J) xi
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
          (U (⟨p, Nat.lt_succ_of_le ((hpk.trans hkr).trans hrL)⟩,
            ⟨r, Nat.lt_succ_of_le hrL⟩)) := by
      dsimp only [canonicalIntervalSamplingOperation, independentIntervalOperation]
      rw [dite_eq_left hrL, dite_eq_left hlong]
      rfl
    rw [hop]
    exact canonicalSampledIntervalInterleavedTrim_profile hD hs (hN J) (F J) hxi _ _

end TNLean.MPS.AreaLaw

end
