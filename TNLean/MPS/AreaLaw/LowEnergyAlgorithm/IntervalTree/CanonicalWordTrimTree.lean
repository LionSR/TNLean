/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalWordTrim
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IndependentIntervalProbability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalGenerators
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IntervalSamplingChoices

/-!
# The joint failure of the canonical merge tree with `k` rounds

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, samples afresh at every merge of the
tree. This file runs the balanced tree whose long parents are the canonical sampled parents with
`k` rounds and one collective trim, with one independent rank-independent Haar coordinate per
interval. If every parent of viable children of dimension at most `count` fails to be viable on
a set of coordinates of measure at most `β`, then the root and its internal nodes are all viable
outside a measurable set of measure at most `(L - 1) β`. Every node has dimension at most `count`
for every coordinate.

**Source comparison (composition along the tree):** in the maintainer's reading of the arXiv v2
text, §6.2, the proof of Theorem 6.1 (`t:alg1`) obtains its overall success probability by this
union bound over the merges, from a per-merge failure probability at most `1/n²`. Here the
per-parent bound `β` is arbitrary. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw

/-- The balanced merge tree whose long parents are the canonical sampled parents with `power`
rounds and one collective trim, run on one independent coordinate per interval. Supporting
ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818. -/
noncomputable def canonicalWordTrimOperation {L q width : ℕ} (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (power s : ℕ) (xi : ℝ) (U : IntervalSamplingChoices L q) : IntervalMergeOperation L q :=
  independentIntervalOperation
    (Ω := fun J ↦ Matrix.rankUnitaryProduct (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) power s xi W v) U

/-- Viability of the root `[0, L)` and of all its internal intervals in the canonical tree.
Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818. -/
def canonicalWordTrimTreeGood {L q width : ℕ} (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (power s : ℕ) (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (delta : ℝ) :
    Set (IntervalSamplingChoices L q) :=
  {U | Submodule.IsViable delta
      (balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U) width hwidth 0 L)
      (G.map (Entropy.regionTensorCoordinates q (interval L 0 L)).toLinearEquiv.toLinearMap) ∧
    ∀ J ∈ balancedIntervalMergeList width hwidth 0 L,
      Submodule.IsViable delta
        (balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U) width hwidth J.1 J.2)
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.1 J.2)).toLinearEquiv.toLinearMap)}

/-- Every node of the canonical tree has dimension at most `count`, for every coordinate, when
the leaves have dimension at most `count` and every family has at most `D²` operators with
`D^{2k} s ≤ count`. -/
theorem finrank_balancedIntervalSpace_canonicalWordTrimOperation_le {L q width D power s count : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hleaf : q ^ width ≤ count) (hcount : D ^ (2 * power) * s ≤ count)
    (U : IntervalSamplingChoices L q) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    Module.finrank ℂ (balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U)
      width hwidth p r) ≤ count := by
  refine balancedIntervalSpace_invariant (canonicalWordTrimOperation N F power s xi U) hwidth
    (fun p r S ↦ Module.finrank ℂ S ≤ count) ?_ ?_ p r hpr hrL
  · intro p r _ _ hshort
    exact (interval_top_dimension_and_rank_bounds (L := L) (xi := xi) hq hxi0 hxi1
      hleaf hshort).1
  · intro p j r hpj hjr hrL' hlong S1 S2 _ _
    change Module.finrank ℂ (independentIntervalOperation _ U p j r hpj hjr S1 S2) ≤ count
    unfold independentIntervalOperation
    rw [dite_eq_left hrL', dite_eq_left hlong]
    refine (finrank_canonicalSampledIntervalWordTrim_le _ power s xi _ _).trans
      (le_trans ?_ hcount)
    calc N ⟨(p, r), hpj.trans hjr, hrL', hlong⟩ ^ power * s ≤ (D ^ 2) ^ power * s :=
          Nat.mul_le_mul_right s (Nat.pow_le_pow_left (hN _) power)
      _ = D ^ (2 * power) * s := by rw [← pow_mul]

/-- The viability event of the root and its internal intervals in the canonical tree is Borel.
Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818. -/
theorem measurableSet_canonicalWordTrimTreeGood {L q width : ℕ} (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (power s : ℕ) (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (delta : ℝ) :
    MeasurableSet (canonicalWordTrimTreeGood hwidth N F power s xi G delta) := by
  have hnode (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
      MeasurableSet {U : IntervalSamplingChoices L q | Submodule.IsViable delta
        (balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U) width hwidth p r)
        (G.map (Entropy.regionTensorCoordinates q
          (interval L p r)).toLinearEquiv.toLinearMap)} :=
    Submodule.measurableSet_isViable_of_measurable_projectionMatrix
      (σ := interval L p r → Fin q) (β := {v // v ∉ interval L p r} → Fin q)
      (fun U ↦ balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U)
        width hwidth p r)
      (measurable_projectionMatrix_and_dependsOn_independentIntervalTree
        (Ω := fun J ↦ Matrix.rankUnitaryProduct
          (Fintype.card (interval L J.1.val J.2.val → Fin q)))
        (fun J W v ↦ canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) power s xi W v)
        (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalWordTrim
          (F J) power s xi W hW) hwidth p r hpr hrL).1 _ _
  have hnodes (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth 0 L}) :=
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth 0 L (Nat.zero_le L)
      J.property
    hnode J.val.1 J.val.2 hb.2.1 hb.2.2.1
  convert (hnode 0 L (Nat.zero_le L) le_rfl).inter (MeasurableSet.iInter hnodes) using 1
  ext U
  simp only [canonicalWordTrimTreeGood, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
    Subtype.forall]

/-- **The joint failure of the canonical tree.** If every canonical parent of `δ`-viable children
of dimension at most `count` fails to be `δ`-viable on a set of coordinates of measure at most
`β`, then the root `[0, L)` and its internal intervals are all `δ`-viable outside a set of
measure at most `(L - 1) β`. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:alg1`,
lines 1777–1818, under the marker of this module. -/
theorem intervalSamplingMeasure_canonicalWordTrimTreeGood_compl_le
    {L q width D power s count : ℕ} (hwidth : 1 ≤ width) (hq : 1 ≤ q)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hleaf : q ^ width ≤ count) (hcount : D ^ (2 * power) * s ≤ count)
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) {delta : ℝ} (hdelta : 0 ≤ delta)
    (beta : ℝ≥0∞)
    (hnode : ∀ (J : LongIntervalIndex L width) (j : ℕ) (hpj : J.val.1 ≤ j) (hjr : j ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 j → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L j J.val.2 → Fin q))),
      Submodule.IsViable delta S1
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 j)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable delta S2
        (G.map (Entropy.regionTensorCoordinates q
          (interval L j J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      Matrix.rankUnitaryHaar (Fintype.card (interval L J.val.1 J.val.2 → Fin q))
        {v | ¬Submodule.IsViable delta
          (canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) power s xi
            (adjacentIntervalMerge L q J.val.1 j J.val.2 hpj hjr S1 S2) v)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)} ≤ beta) :
    intervalSamplingMeasure L q (canonicalWordTrimTreeGood hwidth N F power s xi G delta)ᶜ ≤
      ((L - 1 : ℕ) : ℝ≥0∞) * beta := by
  have hprofile := finrank_balancedIntervalSpace_canonicalWordTrimOperation_le hwidth hq N F hN
    hxi0 hxi1 hleaf hcount
  have hroot := pi_independentIntervalTree_joint_failure_le
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) power s xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalWordTrim
      (F J) power s xi W hW) hwidth
    (fun J ↦ Matrix.rankUnitaryHaar (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    G delta hdelta beta 0 L (Nat.zero_le L) le_rfl (by
      intro a b hab hbL hlong U j haj hjb J left right hleft hright
      exact hnode J j haj hjb left right hleft hright
        (hprofile U a j haj (hjb.trans hbL)) (hprofile U j b hjb hbL))
  simpa only [canonicalWordTrimTreeGood, Set.compl_ofPred, Nat.sub_zero, intervalSamplingMeasure,
    canonicalWordTrimOperation] using hroot

end TNLean.MPS.AreaLaw.ALVV
