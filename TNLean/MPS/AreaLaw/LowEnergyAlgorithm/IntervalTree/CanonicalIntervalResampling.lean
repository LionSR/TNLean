/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalCollectiveTrimming
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IndependentIntervalProbability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalGenerators

/-!
# The actual finite-resampling operation on balanced intervals

Every possible endpoint pair receives an independent finite sequence of
rank-independent Haar coordinates. A long parent uses its own sequence
in the literal stopped half-sampling parent of the actual adjacent child
merge. The operator families and scalar parameters precede all sequences.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817.

**Local fix (repeated sampling and terminal amplification):** The parent
is the corrected repeated-sampling operation with terminal image and trim.
It is not identified with the sample-once Figure `fig:merge-prime`; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.

## Unconditional size profiles of the actual finite-resampling tree

Full leaves and every literal complete parent satisfy the same recorded
count and internal-cut rank bound for all global sequences. The number
of rounds bounds every physical interval dimension before any candidate
or sample is chosen. These are size bounds, without a viability premise.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817.

**Local fix (repeated sampling and terminal amplification):** The actual
operation is the corrected parent with its terminal full image and trim;
see https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
-/

section

open ManyBody (interval)

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

namespace TNLean.MPS.AreaLaw

/-- A finite sequence of rank-independent unitary coordinates at every
possible interval. Supporting ALVV, arXiv:1602.08828v2, lines 749–755. -/
abbrev IntervalResamplingChoices (L q rounds : ℕ) :=
  (J : Fin (L + 1) × Fin (L + 1)) →
    Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q))

/-- The fixed independent finite product Haar law, chosen before all
retained ranks and subspaces. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
noncomputable def intervalResamplingMeasure (L q rounds : ℕ) :
    Measure (IntervalResamplingChoices L q rounds) :=
  Measure.pi (fun J : Fin (L + 1) × Fin (L + 1) ↦
    Measure.pi (fun _ : Fin rounds ↦
      Matrix.rankUnitaryHaar (Fintype.card (interval L J.1.val J.2.val → Fin q))))

instance instIsProbabilityMeasureIntervalResamplingMeasure (L q rounds : ℕ) :
    IsProbabilityMeasure (intervalResamplingMeasure L q rounds) := by
  unfold intervalResamplingMeasure
  infer_instance

/-- The actual parent operation uses its own finite sequence and the same
adjacent child spaces. All interval families precede the sequences.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
noncomputable def canonicalIntervalResamplingOperation {L q width : ℕ}
    (D rounds : ℕ) (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (U : IntervalResamplingChoices L q rounds) : IntervalMergeOperation L q :=
  independentIntervalOperation
    (Ω := fun J ↦ Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalHalfSampledIntervalParent L q J.val.1 J.val.2
      D (threshold J) rounds (F J) xi W v) U

/-- The actual corrected resampling tree has measurable projection and
uses no coordinate longer than its interval. Measurability of its literal
native parent is derived, without an event or sampling-success premise.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem measurable_projectionMatrix_and_dependsOn_canonicalIntervalResamplingTree
    {L q width : ℕ} (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := fun U : IntervalResamplingChoices L q rounds ↦ balancedIntervalSpace
      (canonicalIntervalResamplingOperation D rounds threshold N F xi U) width hwidth p r
    Measurable (fun U ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S U).starProjection) ∧
    DependsOn S {J : Fin (L + 1) × Fin (L + 1) | J.2.val - J.1.val ≤ r - p} := by
  unfold canonicalIntervalResamplingOperation
  exact measurable_projectionMatrix_and_dependsOn_independentIntervalTree
    (Ω := fun J ↦ Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalHalfSampledIntervalParent L q J.val.1 J.val.2
      D (threshold J) rounds (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalHalfSampledIntervalParent
      D (threshold J) rounds (F J) xi W hW) hwidth p r hpr hrL

/-- The true viability event of the actual resampling tree is measurable
for the same fixed global target with the full interval exterior retained.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem measurableSet_isViable_canonicalIntervalResamplingTree
    {L q width : ℕ} (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    MeasurableSet {U : IntervalResamplingChoices L q rounds | Submodule.IsViable delta
      (balancedIntervalSpace (canonicalIntervalResamplingOperation
        D rounds threshold N F xi U) width hwidth p r)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)} :=
  Submodule.measurableSet_isViable_of_measurable_projectionMatrix
    (σ := interval L p r → Fin q) (β := {v // v ∉ interval L p r} → Fin q)
    (fun U ↦ balancedIntervalSpace (canonicalIntervalResamplingOperation
      D rounds threshold N F xi U) width hwidth p r)
    (measurable_projectionMatrix_and_dependsOn_canonicalIntervalResamplingTree
      D rounds hwidth threshold N F xi p r hpr hrL).1 delta _

/-- True fixed-child estimates for the literal finite-resampling parents
imply the joint failure bound at the actual root and its internal list.
Measurability and unchanged-child sections are derived; the analytic
fixed-child failure bound remains explicit. Conditional auxiliary for
ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem intervalResamplingMeasure_canonical_tree_joint_failure_le
    {L q width : ℕ} (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (hdelta : 0 ≤ delta) (beta : ℝ≥0∞)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let operation := canonicalIntervalResamplingOperation D rounds threshold N F xi
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    (∀ (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L) (hlong : width < b - a)
      (U : IntervalResamplingChoices L q rounds),
      let k := a + (b - a) / 2
      let hak : a ≤ k := by dsimp only [k]; omega
      let hkb : k ≤ b := by dsimp only [k]; omega
      let J : LongIntervalIndex L width := ⟨(a, b), hab, hbL, hlong⟩
      let left := balancedIntervalSpace (operation U) width hwidth a k
      let right := balancedIntervalSpace (operation U) width hwidth k b
      P a k left → P k b right →
        Measure.pi (fun _ : Fin rounds ↦
          Matrix.rankUnitaryHaar (Fintype.card (interval L a b → Fin q)))
          {v | ¬P a b (canonicalHalfSampledIntervalParent L q a b D (threshold J) rounds (F J) xi
            (adjacentIntervalMerge L q a k b hak hkb left right) v)} ≤ beta) →
    intervalResamplingMeasure L q rounds
      {U | ¬(P p r (balancedIntervalSpace (operation U) width hwidth p r) ∧
        ∀ J ∈ balancedIntervalMergeList width hwidth p r,
          P J.1 J.2 (balancedIntervalSpace (operation U) width hwidth J.1 J.2))} ≤
      ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  unfold canonicalIntervalResamplingOperation intervalResamplingMeasure
  exact pi_independentIntervalTree_joint_failure_le
    (Ω := fun J ↦ Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalHalfSampledIntervalParent L q J.val.1 J.val.2
      D (threshold J) rounds (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalHalfSampledIntervalParent
      D (threshold J) rounds (F J) xi W hW) hwidth
    (fun J ↦ Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar
      (Fintype.card (interval L J.1.val J.2.val → Fin q))))
    G delta hdelta beta p r hpr hrL

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- Every actual retained interval space has the same dimension and
recorded-generator rank ceiling on every sequence. No successful sample
or child viability is assumed. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem canonicalIntervalResamplingTree_profile {L q width D rounds count : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) (hthreshold : ∀ J, 2 ≤ threshold J)
    (hcount : ∀ J, N J * threshold J ≤ count)
    (hrounds : ∀ J : LongIntervalIndex L width,
      Fintype.card (interval L J.val.1 J.val.2 → Fin q) ≤ 2 ^ rounds)
    {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hleaf : q ^ width ≤ count)
    (U : IntervalResamplingChoices L q rounds)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := balancedIntervalSpace
      (canonicalIntervalResamplingOperation D rounds threshold N F xi U) width hwidth p r
    Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S := by
  let P := fun (p r : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L p r → Fin q))) ↦
    Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S
  apply balancedIntervalSpace_invariant
    (canonicalIntervalResamplingOperation D rounds threshold N F xi U)
    hwidth P ?_ ?_ p r hpr hrL
  · intro p r _hpr _hrL hshort
    exact interval_top_dimension_and_rank_bounds hq hxi.le hxi1 hleaf hshort
  · intro p k r hpk hkr hrL hlong S1 S2 _hS1 _hS2
    let J : LongIntervalIndex L width := ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
    have hop : canonicalIntervalResamplingOperation D rounds threshold N F xi U
        p k r hpk hkr S1 S2 =
        canonicalHalfSampledIntervalParent L q p r D (threshold J) rounds (F J) xi
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
          (U (LongIntervalIndex.coordinate J)) := by
      simp only [canonicalIntervalResamplingOperation, independentIntervalOperation,
        dite_eq_left hrL, dite_eq_left hlong]
      rfl
    rw [hop]
    have h := isIntervalSpanWithRankBound_canonicalHalfSampledIntervalParent
      hxi (F J) (hN J) (hthreshold J) (hcount J) (hrounds J)
      (adjacentIntervalMerge L q p k r hpk hkr S1 S2) (U (LongIntervalIndex.coordinate J))
    exact ⟨h.finrank_le, h⟩

end TNLean.MPS.AreaLaw

end
