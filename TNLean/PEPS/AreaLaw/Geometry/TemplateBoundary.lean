/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.AmbientBoundary
import TNLean.PEPS.AreaLaw.Geometry.TemplateLayers

/-!
# Ambient edge boundaries of actual templates

The four-neighbor bound converts the proved depth-layer estimate into the
ambient boundary estimate of Lemma 9.4. Positive radii use the inside layer;
radius zero uses the first outside layer. The largest permitted radius never
requires a layer estimate at the next radius.

Original formalization from the mathematical manuscript; no upstream Lean
proof text is reused. Physical cut clearance and entropy remain separate.
-/

/-
Source: September 24, 2026; scanner:templates (Lemma 9.4).
Revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original formalization; no upstream Lean proof text reused.
Provenance-ID: 8754-boundary-tnlean.peps.arealaw.geometry.template_boundary_card_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.template_boundary_card_le
Provenance-ID: 8754-boundary-tnlean.peps.arealaw.geometry.template_shell_boundary_card_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.template_shell_boundary_card_le
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The actual unordered ambient boundary of every permitted template dilation
has at most `4 * n` edges. Source: Lemma 9.4, ambient boundary estimate. -/
theorem template_boundary_card_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (j : ℕ) (hj : j ≤ s₀) :
    (ambientBoundary (ambientDilation T.points j)).card ≤ 4 * n := by
  by_cases hz : j = 0
  · subst j
    rw [ambientDilation_zero]
    have h := template_layer_card_le T hC 1 (by omega) T.s₀_pos
    simp only [Nat.sub_self, ambientDilation_zero] at h
    exact (card_ambientBoundary_le_outer_layer T.points).trans (Nat.mul_le_mul_left 4 h)
  · exact (card_ambientBoundary_dilation_le_layer T.points j (by omega)).trans
      (Nat.mul_le_mul_left 4 (template_layer_card_le T hC j (by omega) hj))

/-- Removing the original template from a permitted dilation leaves an ambient
shell with at most `8 * n` crossing edges. This is not a physical cut statement. -/
theorem template_shell_boundary_card_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (j : ℕ) (hj : j ≤ s₀) :
    (ambientBoundary (ambientDilation T.points j \ T.points)).card ≤ 8 * n := by
  have hzero := template_boundary_card_le T hC 0 (Nat.zero_le s₀)
  rw [ambientDilation_zero] at hzero
  have hj' := template_boundary_card_le T hC j hj
  have h := card_ambientBoundary_sdiff_le (ambientDilation T.points j) T.points
  omega

end TNLean.PEPS.AreaLaw.Geometry
