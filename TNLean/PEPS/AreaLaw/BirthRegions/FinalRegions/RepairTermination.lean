/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Set.Finite.Lattice
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.BirthRegions.Stars.RepairInductionMetric
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairCurrentRegions
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairTerminalPrefixSites

/-!
# A common empty generation of the repair

The initial mark scales form a bounded finite set. Uniform halving of the
scales and a positive stopping scale therefore give a generation with no
marks. This stopping generation may depend on the initial family.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, initial marks, lines 325–363, and
`geometry:repair-induction`, termination argument, lines 538–541.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Terminal interiors before an empty generation

Once a generation has no repair marks, every later generation is also empty.
Thus the union of terminal-square interiors over all generations is already
the union over the finitely many preceding generations. These are open
interiors; no assertion about the closed terminal squares or unassigned
boundary points is made here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, termination, lines 538–541, final regions, lines 558–561, and the
finite partition argument, lines 694–707. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Exceptional sites at an empty repair generation

The exceptional sites are the cut sites in the surviving dummy or in an
accumulated terminal interior. At an empty generation the terminal union
is a finite prefix. The existing separate estimates therefore bound this
exceptional set without a metric or positive-boundary hypothesis.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:bad-sites`, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- A common generation has no actual mark occurrences. The initial finite
family is bounded uniformly before the contraction estimate is applied.
Source: area-law Section 11, initial marks, lines 325–363, and
`geometry:repair-induction`, lines 538–541. -/
theorem RepairMetricHypotheses.exists_isEmpty_markIndex {a₀ : ℝ}
    (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
      (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀) :
    ∃ N : ℕ, IsEmpty (𝔇 N).markIndex := by
  exact
    letI := finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar 0
    let ⟨M, hB⟩ := (Set.finite_range (𝔇 0).scale).bddAbove
    let ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / Sstar) (one_lt_two : (1 : ℝ) < 2)
    ⟨0 + n, ⟨fun q ↦
      (not_le_of_gt ((div_lt_iff₀ h.stop_pos).mp hn))
        (((mul_le_mul_of_nonneg_left (h.le_scale (0 + n) q)
          (pow_pos (two_pos : (0 : ℝ) < 2) n).le).trans_eq
            (mul_comm ((2 : ℝ) ^ n) ((𝔇 (0 + n)).scale q))).trans
          ((h.scale_mul_two_pow_le 0 n q).trans
            (hB (Set.mem_range_self (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 n q)))))⟩⟩

/-- Once an actual mark family is empty, every later mark family is empty.
A later mark would have an ancestor in the empty generation.
Source: area-law Section 11, child marks, lines 404–409, and
`geometry:repair-induction`, termination argument, lines 538–541. -/
theorem isEmpty_repairStage_markIndex_add (j n : ℕ)
    (h : IsEmpty (𝔇 j).markIndex) : IsEmpty (𝔇 (j + n)).markIndex := by
  exact
    letI := h
    Function.isEmpty (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar j n)

/-- The stopping-scale and lower-layer thresholds precede the finite domain
and cut; each resulting repair has a common empty generation.
Source: area-law Section 11, `geometry:trim-margins`, lines 380–394,
initial marks, lines 325–363, and `geometry:repair-induction`, lines 538–541. -/
theorem exists_uniform_isEmpty_repairStage_markIndex {a₀ : ℝ}
    (ha₀ : 0 < a₀) (ha₀' : a₀ ≤ 1 / 4) :
    ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          ∃ N : ℕ, IsEmpty (repairStage o Λ A C k₀ hC h₀ Sstar N).markIndex := by
  exact
    let ⟨T, hT⟩ := exists_repairMetricHypotheses ha₀ ha₀'
    ⟨T, fun Sstar hSstar C ↦
      let ⟨K, hK⟩ := hT Sstar hSstar C
      ⟨K, fun o Λ A k₀ hC h₀ hk ↦
        RepairMetricHypotheses.exists_isEmpty_markIndex o Λ A C k₀ hC h₀ Sstar
          (hK o Λ A k₀ hC h₀ hk)⟩⟩

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The accumulated terminal interiors are the union of the contributions
strictly before an empty generation.
Source: area-law Section 11, lines 538–541, 558–561 and 694–707. -/
theorem repairTerminalInteriors_eq_iUnion_lt_of_isEmpty (N : ℕ)
    [IsEmpty (𝔇 N).markIndex] :
    repairTerminalInteriors o Λ A C k₀ hC h₀ Sstar =
      ⋃ j < N, repairTerminalInteriorSet (𝔇 j).location (𝔇 j).scale Sstar := by
  refine Set.iUnion_congr fun j ↦ ?_
  by_cases hj : j < N
  · simp only [hj, Set.iUnion_true]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj)
    have : IsEmpty (𝔇 (N + n)).markIndex :=
      isEmpty_repairStage_markIndex_add o Λ A C k₀ hC h₀ Sstar N n inferInstance
    simp only [repairTerminalInteriorSet, Set.iUnion_of_empty, Set.iUnion_empty]

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

open ManyBody (edgeBoundary planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- At an empty generation, the exceptional-site count is bounded by the
existing dummy-site estimate and the terminal-site prefix estimate.
Source: area-law Section 11, `geometry:bad-sites`, lines 694–707;
this is the finite-union counting consequence before the uniform mark bound. -/
theorem card_repairStageExceptionalSites_le_prefix (N : ℕ)
    [IsEmpty (𝔇 N).markIndex] :
    ((repairStageExceptionalSites o Λ A C k₀ hC h₀ Sstar N).card : ℝ) ≤
      ((2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) : ℝ) *
        ((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) +
      (2 * Sstar + 1) ^ 2 *
        ∑ j ∈ Finset.range N, (Nat.card (𝔇 j).markIndex : ℝ) := by
  classical
  have hterminal :=
    repairTerminalInteriors_eq_iUnion_lt_of_isEmpty o Λ A C k₀ hC h₀ Sstar N
  have hsplit : repairStageExceptionalSites o Λ A C k₀ hC h₀ Sstar N =
      (𝔇 N).regionSites Λ A (𝔇 N).dummy ∪
        A.filter (fun x ↦ integerPoint x.val ∈
          ⋃ j < N, repairTerminalInteriorSet
            (𝔇 j).location (𝔇 j).scale Sstar) := by
    simp only [repairStageExceptionalSites, RepairStage.regionSites,
      Set.mem_union, Finset.filter_or, hterminal]
  have hdummy : (((𝔇 N).regionSites Λ A (𝔇 N).dummy).card : ℝ) ≤
      ((2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) : ℝ) *
        ((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) := by
    exact_mod_cast card_repairStage_dummySites_le o Λ A C k₀ hC h₀ Sstar N
  rw [hsplit]
  calc
    _ ≤ (((𝔇 N).regionSites Λ A (𝔇 N).dummy).card : ℝ) +
        ((A.filter (fun x ↦ integerPoint x.val ∈
          ⋃ j < N, repairTerminalInteriorSet
            (𝔇 j).location (𝔇 j).scale Sstar)).card : ℝ) := by
      exact_mod_cast Finset.card_union_le
        ((𝔇 N).regionSites Λ A (𝔇 N).dummy)
        (A.filter (fun x ↦ integerPoint x.val ∈
          ⋃ j < N, repairTerminalInteriorSet
            (𝔇 j).location (𝔇 j).scale Sstar))
    _ ≤ _ := add_le_add hdummy
      (card_repairTerminalInteriorSites_prefix_le o Λ A C k₀ hC h₀ Sstar N)

end TNLean.PEPS.AreaLaw.Geometry
end

end
