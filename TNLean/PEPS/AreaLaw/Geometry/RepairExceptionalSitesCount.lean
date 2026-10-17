/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairDummySites
import TNLean.PEPS.AreaLaw.Geometry.RepairTerminalInteriors
import TNLean.PEPS.AreaLaw.Geometry.RepairTerminalPrefixSites

/-!
# Exceptional sites at an empty repair generation

The exceptional sites are the cut sites in the surviving dummy or in an
accumulated terminal interior. At an empty generation the terminal union
is a finite prefix. The existing separate estimates therefore bound this
exceptional set without a metric or positive-boundary hypothesis.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:bad-sites`, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
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
        ((edgeBoundary Λ A).card : ℝ) +
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
        ((edgeBoundary Λ A).card : ℝ) := by
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
