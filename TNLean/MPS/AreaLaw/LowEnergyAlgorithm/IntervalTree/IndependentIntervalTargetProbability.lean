/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IndependentIntervalProbability

/-!
# Joint failure of an independent interval tree with one target per interval

The joint failure bound of `IndependentIntervalProbability` measures viability of every node for
one global target. The low-density tree of ALVV, arXiv:1602.08828v2, Theorem `t:alg2`,
lines 1869–1878, measures each node `[p, r)` against its own window, shortened with the level of
the node. This file states the same bound for a family of global targets `T p r`: fixed-child
bounds `β` for the parents give failure at most `(r - p - 1) β` for the root `[p, r)` and its
internal intervals, each for its own target.

**Source comparison (composition along the tree):** in the maintainer's reading of the arXiv v2
text, §6.2, the proof of Theorem 6.1 (`t:alg1`) obtains its overall success probability by this
union bound over the merges, from a per-merge failure probability at most `1/n²`. Here the
per-parent bound `β` is arbitrary. See `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw

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

/-- The guarded failure event of a parent, measured against one target per interval, is Borel.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem measurableSet_guardedIntervalFailure_independentIntervalTree_of_targets
    (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        ((T a b).map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    MeasurableSet (guardedIntervalFailure
      (independentIntervalOperation parent) width hwidth P (p, r)) := by
  intro P
  dsimp only [guardedIntervalFailure]
  have hleft := measurableSet_isViable_independentIntervalTree parent hparent hwidth
    (T p (p + (r - p) / 2)) delta p (p + (r - p) / 2) (by omega) (by omega)
  have hright := measurableSet_isViable_independentIntervalTree parent hparent hwidth
    (T (p + (r - p) / 2) r) delta (p + (r - p) / 2) r (by omega) hrL
  have hnode := measurableSet_isViable_independentIntervalTree parent hparent hwidth
    (T p r) delta p r hpr hrL
  exact hleft.inter (hright.inter hnode.compl)

/-- The fresh-coordinate section of the guarded failure is bounded by the parent's fixed-child
failure, for one target per interval. Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1777–1817. -/
theorem measure_guarded_independentIntervalTree_update_le_of_targets
    (μ : ∀ I, Measure (Ω I))
    (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
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
        ((T a b).map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
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
        parent J (adjacentIntervalMerge L q p k r hpk hkr left right) v :=
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

/-- Independent fixed-child parent bounds imply the joint failure bound of the root and its
internal intervals, each measured against its own target. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817, under the marker of this module. -/
theorem pi_independentIntervalTree_joint_failure_le_of_targets
    (μ : ∀ I, Measure (Ω I)) [∀ I, IsProbabilityMeasure (μ I)]
    (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (hdelta : 0 ≤ delta) (beta : ℝ≥0∞)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let operation := independentIntervalOperation parent
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        ((T a b).map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
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
    exact measurableSet_guardedIntervalFailure_independentIntervalTree_of_targets
      parent hparent hwidth T delta J.val.1 J.val.2 hb.2.1 (hb.2.2.1.trans hrL)
  have hsections (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r})
      (U : ∀ I, Ω I) :
      μ (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J)
        {v | Function.update U (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) v ∈
          guardedIntervalFailure operation width hwidth P J.val} ≤ beta := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    exact measure_guarded_independentIntervalTree_update_le_of_targets parent hparent hwidth μ T
      delta J.val.1 J.val.2 hb.2.1 (hb.2.2.1.trans hrL) hb.2.2.2 U beta
      (hfixed J.val.1 J.val.2 hb.2.1 (hb.2.2.1.trans hrL) hb.2.2.2 U)
  have hleaf (a b : ℕ) (_hab : a ≤ b) (_hbL : b ≤ L) (_hshort : b - a ≤ width) :
      P a b ⊤ := Submodule.isViable_top delta hdelta _
  exact pi_balancedIntervalSpace_joint_failure_le μ
    operation width hwidth P hleaf p r hpr hrL beta hE hsections

end TNLean.MPS.AreaLaw.ALVV
