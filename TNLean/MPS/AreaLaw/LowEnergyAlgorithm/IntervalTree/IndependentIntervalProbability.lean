/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IndependentIntervalSections
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.BalancedIntervalFailureProbability
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.BalancedIntervalFailure

/-!
# True failure sections under independent interval laws

An actual fixed-child parent estimate bounds the corresponding guarded
failure section of the same balanced tree. The independent coordinate
laws may contain repeated samples. Measurability and shorter-child
independence follow from the parent construction. The fixed-child failure
estimate remains an explicit analytic hypothesis. This is a conditional
auxiliary for ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817.

## True guarded sections of the actual sampled parent

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.intervalSamplingMeasure_canonical_tree_joint_failure_le`: joint probability
  from actual fixed-child parent estimates.
-/

section IndependentIntervalProbability

section

open ManyBody (interval)

open MeasureTheory
open scoped ENNReal

namespace TNLean.MPS.AreaLaw

variable
  {L q width : ℕ} {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
  [∀ J, MeasurableSpace (Ω J)]
  (parent : ∀ J : LongIntervalIndex L width,
    Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) →
    Ω (LongIntervalIndex.coordinate J) →
    Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
  (hparent : ∀ (J : LongIntervalIndex L width)
    (W : (∀ I, Ω I) →
    Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))),
    Measurable (fun U ↦ (Matrix.toEuclideanCLM
    (n := interval L J.val.1 J.val.2 → Fin q) (𝕜 := ℂ)).symm (W U).starProjection) →
    Measurable (fun x : (∀ I, Ω I) × Ω (LongIntervalIndex.coordinate J) ↦
    (Matrix.toEuclideanCLM (n := interval L J.val.1 J.val.2 → Fin q) (𝕜 := ℂ)).symm
      (parent J (W x.1) x.2).starProjection))
  (hwidth : 1 ≤ width)

include hparent

/-- The actual fresh-coordinate guarded failure is bounded by the same
parent's true fixed-child failure. No comparison event or alternative
retained space is selected. Conditional auxiliary for ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem measure_guarded_independentIntervalTree_update_le
    (μ : ∀ I, Measure (Ω I))
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (hlong : width < r - p) (U : ∀ I, Ω I) (beta : ℝ≥0∞) :
    let k := p + (r - p) / 2
    let hpk : p ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    let J : LongIntervalIndex L width := ⟨(p, r), hpr, hrL, hlong⟩
    let coord := LongIntervalIndex.coordinate J
    let operation := independentIntervalOperation parent
    let left := balancedIntervalSpace (operation U) width hwidth p k
    let right := balancedIntervalSpace (operation U) width hwidth k r
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    (P p k left → P k r right →
      μ coord {v | ¬P p r (parent J
        (adjacentIntervalMerge L q p k r hpk hkr left right) v)} ≤ beta) →
    μ coord
      {v | Function.update U coord v ∈ guardedIntervalFailure operation width hwidth P (p, r)} ≤
        beta := by
  intro k hpk hkr J coord operation left right P hfixed
  have hleft (v : Ω coord) :
      balancedIntervalSpace (operation (Function.update U coord v)) width hwidth p k = left :=
    independentIntervalTree_update_of_length_lt parent hparent hwidth
      p k hpk (hkr.trans hrL) U coord v
      (by dsimp only [k, coord, J, LongIntervalIndex.coordinate]; omega)
  have hright (v : Ω coord) :
      balancedIntervalSpace (operation (Function.update U coord v)) width hwidth k r = right :=
    independentIntervalTree_update_of_length_lt parent hparent hwidth
      k r hkr hrL U coord v (by dsimp only [k, coord, J, LongIntervalIndex.coordinate]; omega)
  have hnode (v : Ω coord) :
      balancedIntervalSpace (operation (Function.update U coord v)) width hwidth p r =
        parent J
          (adjacentIntervalMerge L q p k r hpk hkr left right) v :=
    independentIntervalTree_update_parent parent hparent hwidth p r hpr hrL hlong U v
  by_cases hchildren : P p k left ∧ P k r right
  · apply (measure_mono ?_).trans (hfixed hchildren.1 hchildren.2)
    intro v hfailure
    change P p k (balancedIntervalSpace (operation (Function.update U coord v))
      width hwidth p k) ∧ P k r (balancedIntervalSpace
        (operation (Function.update U coord v)) width hwidth k r) ∧
      ¬P p r (balancedIntervalSpace (operation (Function.update U coord v))
        width hwidth p r) at hfailure
    simpa only [Set.mem_ofPred_eq, hnode] using hfailure.2.2
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

/-- Independent true fixed-child parent bounds imply the joint root and
listed-descendant failure bound for the same actual balanced tree.
The fixed-child estimates and parent measurability remain explicit
analytic hypotheses. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817. -/
theorem pi_independentIntervalTree_joint_failure_le
    (μ : ∀ I, Measure (Ω I)) [∀ I, IsProbabilityMeasure (μ I)]
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (hdelta : 0 ≤ delta) (beta : ℝ≥0∞)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let operation := independentIntervalOperation parent
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    (∀ (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L) (hlong : width < b - a)
      (U : ∀ I, Ω I),
      let k := a + (b - a) / 2
      let hak : a ≤ k := by dsimp only [k]; omega
      let hkb : k ≤ b := by dsimp only [k]; omega
      let J : LongIntervalIndex L width := ⟨(a, b), hab, hbL, hlong⟩
      let left := balancedIntervalSpace (operation U) width hwidth a k
      let right := balancedIntervalSpace (operation U) width hwidth k b
      P a k left → P k b right →
        μ (LongIntervalIndex.coordinate J)
          {v | ¬P a b (parent J (adjacentIntervalMerge L q a k b hak hkb left right) v)} ≤ beta) →
    Measure.pi μ
      {U | ¬(P p r (balancedIntervalSpace (operation U) width hwidth p r) ∧
        ∀ J ∈ balancedIntervalMergeList width hwidth p r,
          P J.1 J.2 (balancedIntervalSpace (operation U) width hwidth J.1 J.2))} ≤
      ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  intro operation P hfixed
  have hE (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r}) :
      MeasurableSet (guardedIntervalFailure operation width hwidth P J.val) := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    exact measurableSet_guardedIntervalFailure_independentIntervalTree
      parent hparent hwidth G delta
      J.val.1 J.val.2 hb.2.1 (hb.2.2.1.trans hrL)
  have hsections (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r})
      (U : ∀ I, Ω I) :
      μ (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J)
        {v | Function.update U (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) v ∈
          guardedIntervalFailure operation width hwidth P J.val} ≤ beta := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    exact measure_guarded_independentIntervalTree_update_le parent hparent hwidth μ G
      delta J.val.1 J.val.2 hb.2.1 (hb.2.2.1.trans hrL) hb.2.2.2 U beta
      (hfixed J.val.1 J.val.2 hb.2.1 (hb.2.2.1.trans hrL) hb.2.2.2 U)
  have hleaf (a b : ℕ) (_hab : a ≤ b) (_hbL : b ≤ L) (_hshort : b - a ≤ width) :
      P a b ⊤ := Submodule.isViable_top delta hdelta _
  exact pi_balancedIntervalSpace_joint_failure_le μ
    operation width hwidth P hleaf p r hpr hrL beta hE hsections

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

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
  unfold canonicalIntervalSamplingOperation
  exact measure_guarded_independentIntervalTree_update_le
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim
      D s (F J) xi W hW) hwidth
    (fun J ↦ Matrix.rankUnitaryHaar
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    G delta p r hpr hrL hlong U beta

end TNLean.MPS.AreaLaw

end

end IndependentIntervalProbability

section CanonicalIntervalJointProbability

/-!
## Joint probability from actual fixed-child parent estimates

An estimate for every valid long parent and every fixed baseline seed
implies simultaneous viability at the root and all its actual internal
descendants. The recursion, its sampling law and all its improving
families are the existing ones. Guarded-event measurability and fresh
coordinate sections are derived, rather than assumed.

This is a conditional analytic auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817. The true fixed-child parent failure
estimate remains an explicit premise; the theorem does not assert that
estimate for arbitrary operator families.
-/

open ManyBody (interval)

open MeasureTheory
open scoped ENNReal

namespace TNLean.MPS.AreaLaw

/-- Fixed-child bounds for the literal canonical parents imply a joint
failure bound for one actual root hierarchy. Only nonnegative viability
error and the fixed-child analytic estimates are required; short leaves,
listed Borel events and true coordinate sections are derived. Conditional
auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem intervalSamplingMeasure_canonical_tree_joint_failure_le
    {L q width : ℕ} (D s : ℕ) (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (hdelta : 0 ≤ delta) (beta : ℝ≥0∞)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let operation := canonicalIntervalSamplingOperation D s N F xi
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    (∀ (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L) (hlong : width < b - a)
      (U : IntervalSamplingChoices L q),
      let k := a + (b - a) / 2
      let hak : a ≤ k := by dsimp only [k]; omega
      let hkb : k ≤ b := by dsimp only [k]; omega
      let J : LongIntervalIndex L width := ⟨(a, b), hab, hbL, hlong⟩
      let left := balancedIntervalSpace (operation U) width hwidth a k
      let right := balancedIntervalSpace (operation U) width hwidth k b
      P a k left → P k b right →
        Matrix.rankUnitaryHaar (Fintype.card (interval L a b → Fin q))
          {v | ¬P a b (canonicalSampledIntervalInterleavedTrim L q a b D s (F J) xi
            (adjacentIntervalMerge L q a k b hak hkb left right) v)} ≤ beta) →
    intervalSamplingMeasure L q
      {U | ¬(P p r (balancedIntervalSpace (operation U) width hwidth p r) ∧
        ∀ J ∈ balancedIntervalMergeList width hwidth p r,
          P J.1 J.2 (balancedIntervalSpace (operation U) width hwidth J.1 J.2))} ≤
      ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  unfold canonicalIntervalSamplingOperation intervalSamplingMeasure
  exact pi_independentIntervalTree_joint_failure_le
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim
      D s (F J) xi W hW) hwidth
    (fun J ↦ Matrix.rankUnitaryHaar
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    G delta hdelta beta p r hpr hrL

end TNLean.MPS.AreaLaw

end CanonicalIntervalJointProbability
