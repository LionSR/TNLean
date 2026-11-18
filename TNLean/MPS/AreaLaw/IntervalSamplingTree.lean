/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalTree
import TNLean.MPS.AreaLaw.IntervalSampledImage
import TNLean.MPS.AreaLaw.IntervalFullSpaceProfile
import QICLean.Analysis.ViableNodeSamplingParameters

/-!
# A recursively selected sampled interval tree

A fixed family is recorded for each long parent before all child spaces
and the sampling-size choice. Certified fixed-input Haar events then
select actual successful unitaries and give an actual balanced recursion.
The conclusion retains the original global target, the generator counts
and the ranks of the recorded generators. This supports ALVV,
arXiv:1602.08828v2, merge algorithm, lines 1662–1677, and the
degenerate-ground-space analysis, lines 1777–1817.

This auxiliary theorem assumes the fixed-input node events; the physical
construction must supply them. It proves existence of a recursively chosen
tree. It does not assert measurable dependence on earlier choices or a
joint success probability for an adaptive algorithm. The leaves are full
spaces at a prescribed positive width, and long nodes use one final trim.
-/

open MeasureTheory
open scoped ENNReal

namespace TNLean.MPS.AreaLaw

/-- Certified fixed-input node events and the actual word families construct
one balanced tree, rather than assuming its final viable spaces. Each
interval `[p, r)` carries its own global target `T p r`, as for the windows
that shrink with the level in Theorem `t:alg2`, lines 1869–1878, for any
word length `power` and node budget `count` with `count² ≤ D¹² s⁶` and
`D^{2 power} s ≤ count`. Supporting
ALVV, arXiv:1602.08828v2, merge analysis, lines 1777–1817. The event premise
is an explicit hypothesis of this auxiliary composition. -/
theorem exists_balanced_sampled_interval_tree_of_targets_power {L q width D rG : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q) (hD : 2 ≤ D) (hrG : 1 ≤ rG)
    (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (cut : ℕ → ℕ → ℕ → Prop) (hcut : ∀ p r : ℕ, cut p (p + (r - p) / 2) r) {xi : ℝ}
    (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta < 1)
    (power count : ℕ) :
    let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
    let s := Nat.ceil (4096 * (rG : ℝ) * A)
    let failure : ℕ → ℝ := fun Q ↦ if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * rG) * Q *
        Real.exp (-(s / 16 : ℝ))
    count * count ≤ D ^ 12 * s ^ 6 → D ^ (2 * power) * s ≤ count →
    q ^ width ≤ count →
    (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (_hcutk : cut J.val.1 k J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        ((T J.val.1 k).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        ((T k J.val.2).map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2
      ∃ Good : Set (Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ),
        Matrix.unitaryHaar (Fin (Module.finrank ℂ W)) Goodᶜ ≤
          ENNReal.ofReal (failure (Module.finrank ℂ W)) ∧
        ∀ U ∈ Good, Submodule.IsViable (3 / 200 : ℝ)
          (sampledIntervalTrim L q J.val.1 J.val.2 (F J)
            power s xi W U)
          ((T J.val.1 J.val.2).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∃ operation : IntervalMergeOperation L q,
      (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (_hcutk : cut J.val.1 k J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
        Submodule.IsViable (3 / 200 : ℝ) S1
          ((T J.val.1 k).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
        Submodule.IsViable (3 / 200 : ℝ) S2
          ((T k J.val.2).map (Entropy.regionTensorCoordinates q
            (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
        Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
        ∃ U : Matrix.unitaryGroup
          (Fin (Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
          operation J.val.1 k J.val.2 hpk hkr S1 S2 =
            sampledIntervalTrim L q J.val.1 J.val.2 (F J) power s xi
              (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace operation width hwidth p r
        Submodule.IsViable (3 / 200 : ℝ) S
          ((T p r).map
            (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
        Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S := by
  classical
  intro A s failure hcount hword hleaf hEvents
  obtain ⟨hs, _hscount, htail, hfailure⟩ :=
    Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1.le
  let P := fun (p r : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L p r → Fin q))) ↦
    Submodule.IsViable (3 / 200 : ℝ) S
      ((T p r).map
            (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
    Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S
  have hchoice : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (hcutk : cut J.val.1 k J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        ((T J.val.1 k).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        ((T k J.val.2).map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      ∃ U : Matrix.unitaryGroup
        (Fin (Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
        P J.val.1 J.val.2 (sampledIntervalTrim L q J.val.1 J.val.2 (F J)
          power s xi
          (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) := by
    intro J k hpk hkr hcutk S1 S2 hS1 hS2 hd1 hd2
    let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2
    obtain ⟨Good, hbad, hout⟩ := hEvents J k hpk hkr hcutk S1 S2 hS1 hS2 hd1 hd2
    have hQ : Module.finrank ℂ W ≤ D ^ 12 * s ^ 6 := by
      calc
        _ ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
          finrank_adjacentIntervalMerge_le hpk hkr S1 S2
        _ ≤ count * count := Nat.mul_le_mul hd1 hd2
        _ ≤ D ^ 12 * s ^ 6 := hcount
    have heta : failure (Module.finrank ℂ W) < 1 :=
      (hfailure _ hQ).trans_lt (htail.trans_lt hbeta1)
    have hGood : Good.Nonempty := by
      by_contra hempty
      have heq : Good = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
      have hbad1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (failure (Module.finrank ℂ W)) := by
        simpa only [heq, Set.compl_empty, measure_univ] using hbad
      exact (not_le_of_gt (ENNReal.ofReal_lt_one.mpr heta)) hbad1
    obtain ⟨U, hU⟩ := hGood
    have hV : Module.finrank ℂ (Submodule.sampledWordImage (F J) power s W U) ≤ count := by
      calc
        _ ≤ Fintype.card (Fin (N J)) ^ power * min s (Module.finrank ℂ W) :=
          Submodule.finrank_sampledWordImage_le (F J) power s W U
        _ ≤ (D ^ 2) ^ power * s := Nat.mul_le_mul
          (Nat.pow_le_pow_left (by simpa only [Fintype.card_fin] using hN J) power)
          (Nat.min_le_left _ _)
        _ = D ^ (2 * power) * s := by rw [← pow_mul]
        _ ≤ count := hword
    have hspan : IsIntervalSpanWithRankBound L q J.val.1 J.val.2 count xi
        (sampledIntervalTrim L q J.val.1 J.val.2 (F J) power s xi W U) :=
      isIntervalSpanWithRankBound_intervalTrimSubspace hxi _ hV
    exact ⟨U, hout U hU, hspan.finrank_le, hspan⟩
  let operation : IntervalMergeOperation L q := fun p k r hpk hkr S1 S2 ↦
    if hJ : p ≤ r ∧ r ≤ L ∧ width < r - p then
      if hS : cut p k r ∧ Submodule.IsViable (3 / 200 : ℝ) S1
          ((T p k).map
            (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap) ∧
        Submodule.IsViable (3 / 200 : ℝ) S2
          ((T k r).map
            (Entropy.regionTensorCoordinates q (interval L k r)).toLinearEquiv.toLinearMap) ∧
        Module.finrank ℂ S1 ≤ count ∧ Module.finrank ℂ S2 ≤ count then
        sampledIntervalTrim L q p r (F ⟨(p, r), hJ⟩) power s xi
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
          (Classical.choose (hchoice ⟨(p, r), hJ⟩ k hpk hkr hS.1 S1 S2
            hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2))
      else ⊤
    else ⊤
  have hoperation : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (hcutk : cut J.val.1 k J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        ((T J.val.1 k).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        ((T k J.val.2).map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      ∃ U : Matrix.unitaryGroup
        (Fin (Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
        operation J.val.1 k J.val.2 hpk hkr S1 S2 =
          sampledIntervalTrim L q J.val.1 J.val.2 (F J) power s xi
            (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U ∧
        P J.val.1 J.val.2 (operation J.val.1 k J.val.2 hpk hkr S1 S2) := by
    intro J k hpk hkr hcutk S1 S2 hS1 hS2 hd1 hd2
    let U := Classical.choose (hchoice J k hpk hkr hcutk S1 S2 hS1 hS2 hd1 hd2)
    have hU := Classical.choose_spec (hchoice J k hpk hkr hcutk S1 S2 hS1 hS2 hd1 hd2)
    have heq : operation J.val.1 k J.val.2 hpk hkr S1 S2 =
        sampledIntervalTrim L q J.val.1 J.val.2 (F J) power s xi
          (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U := by
      dsimp only [operation]
      split_ifs with hJ hS
      · rfl
      · exact False.elim (hS ⟨hcutk, hS1, hS2, hd1, hd2⟩)
      · exact False.elim (hJ J.property)
    exact ⟨U, heq, heq.symm ▸ hU⟩
  clear_value operation
  refine ⟨operation, ?_, ?_⟩
  · intro J k hpk hkr hcutk S1 S2 hS1 hS2 hd1 hd2
    obtain ⟨U, heq, _⟩ := hoperation J k hpk hkr hcutk S1 S2 hS1 hS2 hd1 hd2
    exact ⟨U, heq⟩
  · intro p r hpr hrL
    apply balancedIntervalSpace_invariant_of_midpoint operation hwidth P ?_ ?_ p r hpr hrL
    · intro p r _hpr _hrL hshort
      have hprofile := interval_top_dimension_and_rank_bounds (L := L) hq hxi.le hxi1 hleaf hshort
      exact ⟨Submodule.isViable_top _ (by norm_num) _, hprofile⟩
    · intro p r hpk hkr hrL hlong S1 S2 hS1 hS2
      let J : LongIntervalIndex L width := ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
      obtain ⟨_U, _heq, hP⟩ := hoperation J _ hpk hkr (hcut p r) S1 S2
        hS1.1 hS2.1 hS1.2.1 hS2.2.1
      exact hP


/-- Certified fixed-input node events and the actual word families construct
one balanced tree, rather than assuming its final viable spaces. Each
interval `[p, r)` carries its own global target `T p r`, as for the windows
that shrink with the level in Theorem `t:alg2`, lines 1869–1878. Supporting
ALVV, arXiv:1602.08828v2, merge analysis, lines 1777–1817. The event premise
is an explicit hypothesis of this auxiliary composition. -/
theorem exists_balanced_sampled_interval_tree_of_targets {L q width D rG : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q) (hD : 2 ≤ D) (hrG : 1 ≤ rG)
    (T : ℕ → ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (cut : ℕ → ℕ → ℕ → Prop) (hcut : ∀ p r : ℕ, cut p (p + (r - p) / 2) r) {xi : ℝ}
    (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta < 1) :
    let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
    let s := Nat.ceil (4096 * (rG : ℝ) * A)
    let count := D ^ 6 * s ^ 3
    let failure : ℕ → ℝ := fun Q ↦ if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * rG) * Q *
        Real.exp (-(s / 16 : ℝ))
    q ^ width ≤ count →
    (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (_hcutk : cut J.val.1 k J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        ((T J.val.1 k).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        ((T k J.val.2).map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2
      ∃ Good : Set (Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ),
        Matrix.unitaryHaar (Fin (Module.finrank ℂ W)) Goodᶜ ≤
          ENNReal.ofReal (failure (Module.finrank ℂ W)) ∧
        ∀ U ∈ Good, Submodule.IsViable (3 / 200 : ℝ)
          (sampledIntervalTrim L q J.val.1 J.val.2 (F J)
            (Nat.clog D (D ^ 2 * s)) s xi W U)
          ((T J.val.1 J.val.2).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∃ operation : IntervalMergeOperation L q,
      (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (_hcutk : cut J.val.1 k J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
        Submodule.IsViable (3 / 200 : ℝ) S1
          ((T J.val.1 k).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
        Submodule.IsViable (3 / 200 : ℝ) S2
          ((T k J.val.2).map (Entropy.regionTensorCoordinates q
            (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
        Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
        ∃ U : Matrix.unitaryGroup
          (Fin (Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
          operation J.val.1 k J.val.2 hpk hkr S1 S2 =
            sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
              (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace operation width hwidth p r
        Submodule.IsViable (3 / 200 : ℝ) S
          ((T p r).map
            (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
        Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S := by
  intro A s count failure hleaf hEvents
  obtain ⟨hs, -⟩ := Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1.le
  have hpow := (Nat.viable_node_power_bounds hD hs).2.2.2
  exact exists_balanced_sampled_interval_tree_of_targets_power hwidth hq hD hrG T cut hcut hxi hxi1
    N F hN hbeta hbeta1 (Nat.clog D (D ^ 2 * s)) count (le_of_eq (by dsimp only [count]; ring))
    (by rw [pow_mul']; exact hpow) hleaf hEvents

/-- Certified fixed-input node events and the actual word families construct
one balanced tree for any word length `power` and node budget `count` with
`count² ≤ D¹² s⁶` and `D^{2 power} s ≤ count`. Supporting ALVV,
arXiv:1602.08828v2, merge analysis, lines 1662–1677 and 1777–1817. The event
premise is an explicit hypothesis of this auxiliary composition. -/
theorem exists_balanced_sampled_interval_tree_of_power {L q width D rG : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q) (hD : 2 ≤ D) (hrG : 1 ≤ rG)
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) {xi : ℝ}
    (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta < 1)
    (power count : ℕ) :
    let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
    let s := Nat.ceil (4096 * (rG : ℝ) * A)
    let failure : ℕ → ℝ := fun Q ↦ if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * rG) * Q *
        Real.exp (-(s / 16 : ℝ))
    count * count ≤ D ^ 12 * s ^ 6 → D ^ (2 * power) * s ≤ count →
    q ^ width ≤ count →
    (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        (G.map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2
      ∃ Good : Set (Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ),
        Matrix.unitaryHaar (Fin (Module.finrank ℂ W)) Goodᶜ ≤
          ENNReal.ofReal (failure (Module.finrank ℂ W)) ∧
        ∀ U ∈ Good, Submodule.IsViable (3 / 200 : ℝ)
          (sampledIntervalTrim L q J.val.1 J.val.2 (F J)
            power s xi W U)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∃ operation : IntervalMergeOperation L q,
      (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
        Submodule.IsViable (3 / 200 : ℝ) S1
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
        Submodule.IsViable (3 / 200 : ℝ) S2
          (G.map (Entropy.regionTensorCoordinates q
            (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
        Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
        ∃ U : Matrix.unitaryGroup
          (Fin (Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
          operation J.val.1 k J.val.2 hpk hkr S1 S2 =
            sampledIntervalTrim L q J.val.1 J.val.2 (F J) power s xi
              (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace operation width hwidth p r
        Submodule.IsViable (3 / 200 : ℝ) S
          (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
        Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S := by
  intro A s failure hcount hword hleaf hEvents
  obtain ⟨operation, hliteral, htree⟩ :=
    exists_balanced_sampled_interval_tree_of_targets_power hwidth hq hD hrG (fun _ _ ↦ G)
      (fun _ _ _ ↦ True) (fun _ _ ↦ trivial) hxi hxi1 N F hN hbeta hbeta1 power count
      hcount hword hleaf (fun J k hpk hkr _ ↦ hEvents J k hpk hkr)
  exact ⟨operation, fun J k hpk hkr ↦ hliteral J k hpk hkr trivial, htree⟩

/-- Certified fixed-input node events and the actual word families construct
one balanced tree, rather than assuming its final viable spaces. Supporting
ALVV, arXiv:1602.08828v2, merge analysis, lines 1777–1817. The event premise
is an explicit hypothesis of this auxiliary composition. -/
theorem exists_balanced_sampled_interval_tree {L q width D rG : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q) (hD : 2 ≤ D) (hrG : 1 ≤ rG)
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) {xi : ℝ}
    (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta < 1) :
    let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
    let s := Nat.ceil (4096 * (rG : ℝ) * A)
    let count := D ^ 6 * s ^ 3
    let failure : ℕ → ℝ := fun Q ↦ if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * rG) * Q *
        Real.exp (-(s / 16 : ℝ))
    q ^ width ≤ count →
    (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        (G.map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2
      ∃ Good : Set (Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ),
        Matrix.unitaryHaar (Fin (Module.finrank ℂ W)) Goodᶜ ≤
          ENNReal.ofReal (failure (Module.finrank ℂ W)) ∧
        ∀ U ∈ Good, Submodule.IsViable (3 / 200 : ℝ)
          (sampledIntervalTrim L q J.val.1 J.val.2 (F J)
            (Nat.clog D (D ^ 2 * s)) s xi W U)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∃ operation : IntervalMergeOperation L q,
      (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
        Submodule.IsViable (3 / 200 : ℝ) S1
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
        Submodule.IsViable (3 / 200 : ℝ) S2
          (G.map (Entropy.regionTensorCoordinates q
            (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
        Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
        ∃ U : Matrix.unitaryGroup
          (Fin (Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
          operation J.val.1 k J.val.2 hpk hkr S1 S2 =
            sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
              (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace operation width hwidth p r
        Submodule.IsViable (3 / 200 : ℝ) S
          (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
        Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S := by
  intro A s count failure hleaf hEvents
  obtain ⟨hs, -⟩ := Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1.le
  have hpow := (Nat.viable_node_power_bounds hD hs).2.2.2
  exact exists_balanced_sampled_interval_tree_of_power hwidth hq hD hrG G hxi hxi1 N F hN
    hbeta hbeta1 (Nat.clog D (D ^ 2 * s)) count (le_of_eq (by dsimp only [count]; ring))
    (by rw [pow_mul']; exact hpow) hleaf hEvents

end TNLean.MPS.AreaLaw
