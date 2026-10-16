/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairExceptionalSitesCount
import TNLean.PEPS.AreaLaw.Geometry.RepairTotalMarkPrefixCount
import TNLean.PEPS.AreaLaw.Geometry.RepairTermination

/-!
# A uniform bound for the exceptional sites

The exceptional sites consist of the surviving dummy sites and the cut sites
in terminal interiors. The bound for a finite prefix, the uniform count of
repair marks, and termination give a bound proportional to the edge boundary.
Its coefficient may depend on the fixed width, lower layer, and stopping scale,
but is chosen before the origin, finite domain, and cut.

The first theorem assumes the existing repair metric hypotheses. The second
chooses the stopping and lower-layer thresholds and derives those hypotheses
with isolation constant one quarter. Thus the second theorem has no supplied
metric or empty-generation hypothesis. These thresholds concern the exceptional
count; the scanner-template and clearance conditions are separate results.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:bad-sites`, lines 694–707, and the
threshold order, lines 762–776.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- For fixed repair parameters, a positive coefficient chosen before the
geometric data bounds the exceptional sites at an actual empty generation.
This auxiliary statement uses the existing repair metric hypotheses.
Source: area-law Section 11, `geometry:bad-sites`, lines 694–707. -/
theorem exists_uniform_repairStageExceptionalSites_bound
    (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (a₀ : ℝ),
        RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
          (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
        ∃ N : ℕ, IsEmpty (repairStage o Λ A C k₀ hC h₀ Sstar N).markIndex ∧
          ((repairStageExceptionalSites o Λ A C k₀ hC h₀ Sstar N).card : ℝ) ≤
            L * (edgeBoundary Λ A).card := by
  classical
  obtain ⟨M, hM, hmark⟩ := exists_uniform_repairStage_markIndex_prefix_bound hSstar
  let D : ℝ := ((2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) : ℝ)
  refine ⟨D + (2 * Sstar + 1) ^ 2 * M * (2 * (C : ℝ) + 1) ^ 2, ?_, ?_⟩
  · dsimp [D]
    positivity
  · intro o Λ A a₀ h
    obtain ⟨N, hN⟩ :=
      RepairMetricHypotheses.exists_isEmpty_markIndex o Λ A C k₀ hC h₀ Sstar h
    let : IsEmpty (repairStage o Λ A C k₀ hC h₀ Sstar N).markIndex := hN
    refine ⟨N, hN, ?_⟩
    calc
      _ ≤ D * (edgeBoundary Λ A).card + (2 * Sstar + 1) ^ 2 *
          ∑ j ∈ Finset.range N,
            (Nat.card (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex : ℝ) :=
        card_repairStageExceptionalSites_le_prefix o Λ A C k₀ hC h₀ Sstar N
      _ ≤ D * (edgeBoundary Λ A).card + (2 * Sstar + 1) ^ 2 *
          (M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card) :=
        _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (hmark o Λ A C k₀ hC h₀ a₀ h N) (sq_nonneg _))
      _ = _ := by ring

/-- Fixed stopping and lower-layer thresholds give a uniform exceptional-site
bound for every origin, finite domain, and cut. The coefficient is chosen
before those data; the existing construction supplies the metric hypotheses
and an empty generation internally.
Source: area-law Section 11, `geometry:bad-sites`, lines 694–707, and the
threshold order, lines 762–776. Only the thresholds for this count are asserted. -/
theorem exists_uniform_repairStageExceptionalSites_bound_of_thresholds :
    ∃ T : ℝ, 1 < T ∧
      ∀ (Sstar : ℝ), T ≤ Sstar → ∀ (C : ℕ) (hC : 2 ≤ C),
        ∃ (K : ℕ) (hK : 50000000 ≤ K),
          ∀ (k₀ : ℕ) (hk₀ : K ≤ k₀),
            let h₀ : 50000000 ≤ k₀ := hK.trans hk₀
            ∃ L : ℝ, 0 < L ∧
              ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)),
                ∃ N : ℕ, IsEmpty (repairStage o Λ A C k₀ hC h₀ Sstar N).markIndex ∧
                  ((repairStageExceptionalSites o Λ A C k₀ hC h₀ Sstar N).card : ℝ) ≤
                    L * (edgeBoundary Λ A).card := by
  classical
  obtain ⟨T, hT⟩ := exists_repairMetricHypotheses (a₀ := (1 : ℝ) / 4)
    (by norm_num) le_rfl
  refine ⟨max T 2, lt_of_lt_of_le one_lt_two (le_max_right _ _), ?_⟩
  intro Sstar hSstar C hC
  obtain ⟨K, hK⟩ := hT Sstar ((le_max_left _ _).trans hSstar) C
  refine ⟨max K 50000000, le_max_right _ _, ?_⟩
  intro k₀ hk₀
  obtain ⟨L, hL, hbound⟩ := exists_uniform_repairStageExceptionalSites_bound
    C k₀ hC ((le_max_right K 50000000).trans hk₀)
    (lt_of_lt_of_le one_lt_two ((le_max_right T 2).trans hSstar))
  exact ⟨L, hL, fun o Λ A ↦ hbound o Λ A (1 / 4)
    (hK o Λ A k₀ hC _ ((le_max_left _ _).trans hk₀))⟩

end TNLean.PEPS.AreaLaw.Geometry
