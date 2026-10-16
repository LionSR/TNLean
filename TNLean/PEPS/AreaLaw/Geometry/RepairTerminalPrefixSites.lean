/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.Geometry.RepairTerminalSquareCount

/-!
# Terminal sites in finitely many repair generations

The sites of a cut lying in terminal interiors before generation `N` are
bounded by the number of marks in those generations, multiplied by the
uniform bound for the lattice sites in one terminal square. Overlaps between
terminal squares can only reduce the number of sampled sites.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:bad-sites`, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

open scoped Classical in
/-- The cut sites in terminal interiors before generation `N` are bounded
by the sum of the actual mark counts in those generations, multiplied by
`(2 * Sstar + 1)²`. Source: area-law Section 11, `geometry:bad-sites`,
lines 694–707, the finite-union counting step. -/
theorem card_repairTerminalInteriorSites_prefix_le (N : ℕ) :
    ((A.filter (fun x ↦ integerPoint x.val ∈
      ⋃ j < N, repairTerminalInteriorSet
        (𝔇 j).location (𝔇 j).scale Sstar)).card : ℝ) ≤
      (2 * Sstar + 1) ^ 2 *
        ∑ j ∈ Finset.range N, (Nat.card (𝔇 j).markIndex : ℝ) := by
  classical
  let (j : ℕ) : Fintype (𝔇 j).markIndex :=
    @Fintype.ofFinite _ (finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar j)
  let T (j : ℕ) : Finset (𝔇 j).markIndex :=
    Finset.univ.filter (fun p ↦ repairHalfSide ((𝔇 j).scale p) < Sstar)
  let Q (j : ℕ) : Finset (Site Λ) :=
    (T j).biUnion (fun p ↦
      closedSquareSample Λ ((𝔇 j).location p) (repairHalfSide ((𝔇 j).scale p)))
  have hsub : A.filter (fun x ↦ integerPoint x.val ∈
      ⋃ j < N, repairTerminalInteriorSet (𝔇 j).location (𝔇 j).scale Sstar) ⊆
      (Finset.range N).biUnion Q := by
    intro x hx
    simp only [Finset.mem_filter, Set.mem_iUnion, repairTerminalInteriorSet] at hx
    obtain ⟨_, j, hj, p, hp⟩ := hx
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
      Finset.mem_biUnion.mpr ⟨p.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.property⟩, ?_⟩⟩
    simpa only [mem_closedSquareSample, repairSquare, Metric.mem_closedBall,
      Prod.dist_eq, Real.dist_eq, max_le_iff, integerPoint] using (interior_subset hp)
  have hQ (j : ℕ) : ((Q j).card : ℝ) ≤
      (2 * Sstar + 1) ^ 2 * (Nat.card (𝔇 j).markIndex : ℝ) := by
    calc
      ((Q j).card : ℝ) ≤ ∑ p ∈ T j,
          ((closedSquareSample Λ ((𝔇 j).location p)
            (repairHalfSide ((𝔇 j).scale p))).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := T j)
          (t := fun p ↦ closedSquareSample Λ ((𝔇 j).location p)
            (repairHalfSide ((𝔇 j).scale p))))
      _ ≤ ((T j).card : ℝ) * (2 * Sstar + 1) ^ 2 := by
        simpa only [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul (T j)
            (fun p ↦ ((closedSquareSample Λ ((𝔇 j).location p)
              (repairHalfSide ((𝔇 j).scale p))).card : ℝ))
            ((2 * Sstar + 1) ^ 2) (fun p hp ↦
              card_closedSquareSample_repairHalfSide_le Λ _ (Finset.mem_filter.mp hp).2))
      _ ≤ (2 * Sstar + 1) ^ 2 * (Nat.card (𝔇 j).markIndex : ℝ) := by
        simpa only [Nat.card_eq_fintype_card, mul_comm] using
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ (T j)))
            (sq_nonneg (2 * Sstar + 1)))
  calc
    _ ≤ (((Finset.range N).biUnion Q).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ j ∈ Finset.range N, ((Q j).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.range N) (t := Q))
    _ ≤ _ := by
      simpa only [Finset.mul_sum] using
        (Finset.sum_le_sum (s := Finset.range N) (fun j _ ↦ hQ j))

end TNLean.PEPS.AreaLaw.Geometry
