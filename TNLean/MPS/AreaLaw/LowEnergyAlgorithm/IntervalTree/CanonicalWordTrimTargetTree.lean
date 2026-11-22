/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalWordTrimTree
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IndependentIntervalTargetProbability

/-!
# The joint failure of the canonical tree with one target per interval

The canonical merge tree of `CanonicalWordTrimTree`, measured against one global target `T p r`
for every interval, as for the shrinking windows of the low-density tree of ALVV,
arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878. If every canonical parent of viable
children of dimension at most `count`, cut at the midpoint, fails on a set of measure at most
`β`, then the root and its internal nodes are all viable for their own targets outside a set of
measure at most `(L - 1) β`.

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

/-- Viability of the root `[0, L)` and of all its internal intervals in the canonical tree, each
for its own target. Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878. -/
def canonicalWordTrimTreeGoodOfTargets {L q width : ℕ} (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (power s : ℕ) (xi : ℝ) (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) : Set (IntervalSamplingChoices L q) :=
  {U | Submodule.IsViable delta
      (balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U) width hwidth 0 L)
      ((T 0 L).map (Entropy.regionTensorCoordinates q (interval L 0 L)).toLinearEquiv.toLinearMap) ∧
    ∀ J ∈ balancedIntervalMergeList width hwidth 0 L,
      Submodule.IsViable delta
        (balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U) width hwidth J.1 J.2)
        ((T J.1 J.2).map (Entropy.regionTensorCoordinates q
          (interval L J.1 J.2)).toLinearEquiv.toLinearMap)}

/-- The viability event of the canonical tree with one target per interval is Borel.
Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878. -/
theorem measurableSet_canonicalWordTrimTreeGoodOfTargets {L q width : ℕ} (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (power s : ℕ) (xi : ℝ) (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) :
    MeasurableSet (canonicalWordTrimTreeGoodOfTargets hwidth N F power s xi T delta) := by
  have hnode (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :=
    measurableSet_isViable_independentIntervalTree
      (Ω := fun J ↦ Matrix.rankUnitaryProduct
        (Fintype.card (interval L J.1.val J.2.val → Fin q)))
      (fun J W v ↦ canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) power s xi W v)
      (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalWordTrim
        (F J) power s xi W hW) hwidth (T p r) delta p r hpr hrL
  have hnodes (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth 0 L}) :=
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth 0 L (Nat.zero_le L)
      J.property
    hnode J.val.1 J.val.2 hb.2.1 hb.2.2.1
  convert (hnode 0 L (Nat.zero_le L) le_rfl).inter (MeasurableSet.iInter hnodes) using 1
  ext U
  simp only [canonicalWordTrimTreeGoodOfTargets, canonicalWordTrimOperation, Set.mem_ofPred_eq,
    Set.mem_inter_iff, Set.mem_iInter, Subtype.forall]

/-- **The joint failure of the canonical tree with one target per interval.** If every canonical
parent of `δ`-viable children of dimension at most `count`, cut at the midpoint and each viable
for its own target, fails to be `δ`-viable for the parent's target on a set of measure at most
`β`, then the root `[0, L)` and its internal intervals are all `δ`-viable for their own targets
outside a set of measure at most `(L - 1) β`. Auxiliary to ALVV, arXiv:1602.08828v2,
Theorem `t:alg2`, lines 1869–1878, under the marker of this module. -/
theorem intervalSamplingMeasure_canonicalWordTrimTreeGoodOfTargets_compl_le
    {L q width D power s count : ℕ} (hwidth : 1 ≤ width) (hq : 1 ≤ q)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hleaf : q ^ width ≤ count) (hcount : D ^ (2 * power) * s ≤ count)
    (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) {delta : ℝ}
    (hdelta : 0 ≤ delta) (beta : ℝ≥0∞)
    (hnode : ∀ (J : LongIntervalIndex L width),
      let j := J.val.1 + (J.val.2 - J.val.1) / 2
      ∀ (hpj : J.val.1 ≤ j) (hjr : j ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 j → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L j J.val.2 → Fin q))),
      Submodule.IsViable delta S1
        ((T J.val.1 j).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 j)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable delta S2
        ((T j J.val.2).map (Entropy.regionTensorCoordinates q
          (interval L j J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      Matrix.rankUnitaryHaar (Fintype.card (interval L J.val.1 J.val.2 → Fin q))
        {v | ¬Submodule.IsViable delta
          (canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) power s xi
            (adjacentIntervalMerge L q J.val.1 j J.val.2 hpj hjr S1 S2) v)
          ((T J.val.1 J.val.2).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)} ≤ beta) :
    intervalSamplingMeasure L q
        (canonicalWordTrimTreeGoodOfTargets hwidth N F power s xi T delta)ᶜ ≤
      ((L - 1 : ℕ) : ℝ≥0∞) * beta := by
  have hprofile := finrank_balancedIntervalSpace_canonicalWordTrimOperation_le hwidth hq N F hN
    hxi0 hxi1 hleaf hcount
  have hroot := pi_independentIntervalTree_joint_failure_le_of_targets
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) power s xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalWordTrim
      (F J) power s xi W hW) hwidth
    (fun J ↦ Matrix.rankUnitaryHaar (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    T delta hdelta beta 0 L (Nat.zero_le L) le_rfl (by
      intro a b hab hbL hlong U j haj hjb J left right hleft hright
      exact hnode J haj hjb left right hleft hright
        (hprofile U a j haj (hjb.trans hbL)) (hprofile U j b hjb hbL))
  simpa only [canonicalWordTrimTreeGoodOfTargets, Set.compl_ofPred, Nat.sub_zero,
    intervalSamplingMeasure, canonicalWordTrimOperation] using hroot

end TNLean.MPS.AreaLaw.ALVV
