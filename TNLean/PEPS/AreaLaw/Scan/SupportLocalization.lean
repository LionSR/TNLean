/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth
import TNLean.PEPS.AreaLaw.Geometry.CellCounting

/-!
# Localization of scan balls inside the fixed cut

A graph ball of radius `r₀` meeting `A ∩ T_L` lies wholly in `A` when the
ambient target is separated from the physical cut endpoints by more than
`2L + 10r₀`. A path between two points of the ball has length at most `2r₀`;
if it leaves `A`, its first crossing produces an actual cut endpoint of
ambient depth at most `L + 2r₀`, contradicting that separation.

This proves the spatial localization step for actual graph balls. Identifying
a splitting truncated designated support with such a ball is a separate
accepted result, `truncationRadius_eq_of_mem_crossingLabels` in
`CrossingBudget`: its hypothesis requires that the crossed compact set lie
inside the truncation set. This module does not identify an arbitrary
truncated support with the fixed-radius ball used by a charge.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 43–48 and 225–233, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- A radius-`r₀` graph ball meeting `A ∩ T_L` cannot leave the fixed cut.
The clearance is stated on the actual ambient endpoints of physical cut edges,
exactly as in `scanner:test-geometry`. Source: `08-scanner.tex`, lines 225–233. -/
theorem domainGraph_ball_subset_of_clearance (Λ T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (A : Finset (Site Λ)) (L r₀ : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {anchor : Site Λ}
    (hmeet : ∃ y ∈ A, ambientDepth T hT y.val ≤ L ∧
      (domainGraph Λ).edist anchor y ≤ (r₀ : ℕ∞)) :
    (Finset.univ.filter fun x ↦ (domainGraph Λ).edist anchor x ≤ (r₀ : ℕ∞)) ⊆ A := by
  classical
  intro x hx
  obtain ⟨y, hyA, hydepth, hy⟩ := hmeet
  have hxball := (Finset.mem_filter.mp hx).2
  by_contra hxA
  have hyx : (domainGraph Λ).edist y x ≤ ((2 * r₀ : ℕ) : ℕ∞) := by
    calc
      (domainGraph Λ).edist y x ≤
          (domainGraph Λ).edist y anchor + (domainGraph Λ).edist anchor x :=
        SimpleGraph.edist_triangle
      _ ≤ (r₀ : ℕ∞) + r₀ :=
        add_le_add (by simpa only [SimpleGraph.edist_comm] using hy) hxball
      _ = ((2 * r₀ : ℕ) : ℕ∞) := by simp [two_mul]
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top (2 * r₀)) hyx)
  obtain ⟨u, w, -, -, hcut, p', hp'⟩ := exists_edgeBoundary_of_walk p hyA hxA
  have hyd : (domainGraph Λ).edist y u ≤ ((2 * r₀ : ℕ) : ℕ∞) := by
    calc
      (domainGraph Λ).edist y u ≤ p'.length := SimpleGraph.edist_le _
      _ ≤ p.length := by exact_mod_cast hp'
      _ = (domainGraph Λ).edist y x := hp
      _ ≤ ((2 * r₀ : ℕ) : ℕ∞) := hyx
  have hvariation := abs_ambientDepth_sub_le_domainGraph T hT hyd
  have hz : u.val ∈ Geometry.boundaryEndpoints Λ A := by
    refine Finset.mem_image.mpr ⟨u, ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨s(u, w), hcut, by simp⟩
  obtain ⟨t, ht, hmin⟩ := T.exists_mem_eq_inf' hT (ambientSupDistance u.val)
  have hseparate := hclear t ht u.val hz
  have hdeep : ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientDepth T hT u.val := by
    rw [ambientDepth, hmin]
    simpa only [ambientSupDistance, abs_sub_comm] using hseparate
  rw [abs_le] at hvariation
  omega

end TNLean.PEPS.AreaLaw.Scan
