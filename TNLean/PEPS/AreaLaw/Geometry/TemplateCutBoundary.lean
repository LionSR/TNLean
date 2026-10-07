/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellCounting
import TNLean.PEPS.AreaLaw.Geometry.TemplateBoundary

/-!
# Physical boundaries of separated templates

The physical boundary of a cut restricted to an ambient set avoiding cut
endpoints injects into the ambient boundary. Template separation implies this
avoidance throughout every permitted dilation, giving the `4n` and `8n` bounds.
Missing lattice edges are never counted as physical edges.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Definition 9.3 and Lemma 9.4, final proof paragraph.
Revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The sufficient condition `1 ≤ D₀` follows from `D₀ > 2R + 10` in
`02-initial.tex`, line 225, since the interaction range is nonnegative.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026; scanner:templates (Lemma 9.4).
Revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original formalization; no upstream Lean proof text reused.
Provenance-ID: 8754-cut-boundary-tnlean.peps.arealaw.geometry.mem_boundaryendpoints_of_mem_edgeboundary
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary
Provenance-ID: 8754-cut-boundary-tnlean.peps.arealaw.geometry.edgeboundary_filter_image_subset_ambientboundary
Downstream declaration:
  TNLean.PEPS.AreaLaw.Geometry.edgeBoundary_filter_image_subset_ambientBoundary
Provenance-ID: 8754-cut-boundary-tnlean.peps.arealaw.geometry.card_edgeboundary_filter_le_ambientboundary
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_filter_le_ambientBoundary
Provenance-ID: 8754-cut-boundary-tnlean.peps.arealaw.geometry.template.isseparated.disjoint_ambientdilation
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.IsSeparated.disjoint_ambientDilation
Provenance-ID: 8754-cut-boundary-tnlean.peps.arealaw.geometry.template_cut_boundary_card_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.template_cut_boundary_card_le
Provenance-ID: 8754-cut-boundary-tnlean.peps.arealaw.geometry.template_core_boundary_card_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.template_core_boundary_card_le
Provenance-ID: 8754-cut-boundary-tnlean.peps.arealaw.geometry.template_shell_cut_boundary_card_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.template_shell_cut_boundary_card_le
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A physical crossing edge contributes both endpoints to the source set `Z`.
Source: Lemma 9.4, final proof paragraph, and the definition of `Z`. -/
theorem mem_boundaryEndpoints_of_mem_edgeBoundary {Λ : Finset (ℤ × ℤ)}
    {A : Finset (Site Λ)} {e : Sym2 (Site Λ)} (he : e ∈ edgeBoundary Λ A)
    {x : Site Λ} (hx : x ∈ e) : x.1 ∈ boundaryEndpoints Λ A := by
  classical
  exact Finset.mem_image.mpr
    ⟨x, Finset.mem_biUnion.mpr ⟨e, he, by simpa using hx⟩, rfl⟩

/-- Restricting a cut to a set avoiding its cut endpoints creates only ambient
crossing edges. Source: Lemma 9.4, final proof paragraph. -/
theorem edgeBoundary_filter_image_subset_ambientBoundary
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (U : Finset (ℤ × ℤ))
    (hU : Disjoint U (boundaryEndpoints Λ A)) :
    (edgeBoundary Λ (A.filter fun x ↦ x.1 ∈ U)).image (Sym2.map Subtype.val) ⊆
      ambientBoundary U := by
  classical
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hedge, p, hp, q, hq, rfl⟩ := Finset.mem_filter.mp hf
  obtain ⟨hpA, hpU⟩ := Finset.mem_filter.mp hp
  have hqA : q ∈ A := by
    by_contra hn
    have hcut : s(p, q) ∈ edgeBoundary Λ A :=
      Finset.mem_filter.mpr ⟨hedge, p, hpA, q, hn, rfl⟩
    exact Finset.disjoint_left.mp hU hpU
      (mem_boundaryEndpoints_of_mem_edgeBoundary hcut (by simp))
  have hqU : q.1 ∉ U := fun h ↦ hq (Finset.mem_filter.mpr ⟨hqA, h⟩)
  have hadj : (domainGraph Λ).Adj p q := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  exact mem_ambientBoundary_iff.mpr
    ⟨p.1, hpU, q.1, hqU, mem_latticeNeighbors_iff.mpr hadj, rfl⟩

/-- The ambient comparison counts unordered physical edges once, even for
empty or disconnected domains. Source: Lemma 9.4, physical boundary estimate. -/
theorem card_edgeBoundary_filter_le_ambientBoundary
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (U : Finset (ℤ × ℤ))
    (hU : Disjoint U (boundaryEndpoints Λ A)) :
    (edgeBoundary Λ (A.filter fun x ↦ x.1 ∈ U)).card ≤ (ambientBoundary U).card := by
  classical
  have h := Finset.card_le_card
    (edgeBoundary_filter_image_subset_ambientBoundary Λ A U hU)
  rwa [Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)] at h

/-- Separation excludes every point of `Z` from all permitted dilations.
Source: Definition 9.3 and Lemma 9.4; no cut-clearance premise is added. -/
theorem Template.IsSeparated.disjoint_ambientDilation {Ctpl D₀ : ℝ} {n s₀ : ℕ}
    {T : Template Ctpl n s₀} {Z : Finset (ℤ × ℤ)}
    (hsep : T.IsSeparated D₀ Z) (hD : 1 ≤ D₀) (j : ℕ) (hj : j ≤ s₀) :
    Disjoint (ambientDilation T.points j) Z := by
  apply Finset.disjoint_left.mpr
  intro z hz hzZ
  obtain ⟨p, hp, hcoord⟩ := mem_ambientDilation_iff.mp hz
  have hdist : max |(p.1 : ℝ) - z.1| |(p.2 : ℝ) - z.2| ≤ (j : ℝ) := by
    rw [max_le_iff, abs_le, abs_le]
    exact_mod_cast (show (-(j : ℤ) ≤ p.1 - z.1 ∧ p.1 - z.1 ≤ j) ∧
      (-(j : ℤ) ≤ p.2 - z.2 ∧ p.2 - z.2 ≤ j) by omega)
  have hsep' := hsep p hp z hzZ
  have hs : (0 : ℝ) < s₀ := by exact_mod_cast T.s₀_pos
  have hj' : (j : ℝ) ≤ s₀ := by exact_mod_cast hj
  nlinarith

/-- Every physical cut of a permitted dilation of a separated template has at
most `4 * n` edges. Source: Lemma 9.4. Clearance is derived from separation. -/
theorem template_cut_boundary_card_le {Ctpl D₀ : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j : ℕ) (hj : j ≤ s₀) :
    (edgeBoundary Λ (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j)).card ≤ 4 * n :=
  (card_edgeBoundary_filter_le_ambientBoundary Λ A _
    (hsep.disjoint_ambientDilation hD j hj)).trans (template_boundary_card_le T hC j hj)

/-- The physical core has at most `4 * n` crossing edges, including empty cores.
Source: Lemma 9.4, `X = A ∩ T`. -/
theorem template_core_boundary_card_le {Ctpl D₀ : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀) :
    (edgeBoundary Λ (A.filter fun x ↦ x.1 ∈ T.points)).card ≤ 4 * n := by
  simpa only [ambientDilation_zero] using
    template_cut_boundary_card_le T hC Λ A hsep hD 0 (Nat.zero_le s₀)

/-- A physical template shell has at most `8 * n` crossing edges.
Source: Lemma 9.4, `Q_j = A ∩ (T_j ∖ T)`. -/
theorem template_shell_cut_boundary_card_le {Ctpl D₀ : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j : ℕ) (hj : j ≤ s₀) :
    (edgeBoundary Λ
      (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points)).card ≤ 8 * n :=
  (card_edgeBoundary_filter_le_ambientBoundary Λ A _
    ((hsep.disjoint_ambientDilation hD j hj).mono_left Finset.sdiff_subset)).trans
      (template_shell_boundary_card_le T hC j hj)

end TNLean.PEPS.AreaLaw.Geometry
