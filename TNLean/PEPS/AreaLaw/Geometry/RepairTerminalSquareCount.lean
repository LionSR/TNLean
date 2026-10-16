/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.ClosedSquare
import TNLean.PEPS.AreaLaw.Geometry.RepairDepth

/-!
# Lattice sites in a terminal repair square

A terminal removal square has half-side less than the stopping scale. Its
closed square contains at most `(2 * Sstar + 1)²` sites of any finite induced
lattice domain. This also bounds the sites in its interior and in any cut
of the domain. The center may be any point of the real plane.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:bad-sites`, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The closed sample of one terminal removal square has at most
`(2 * Sstar + 1)²` sites. Source: area-law Section 11,
`geometry:bad-sites`, lines 694–707. -/
theorem card_closedSquareSample_repairHalfSide_le (Λ : Finset (ℤ × ℤ))
    (v : ℝ × ℝ) {S Sstar : ℝ} (hterm : repairHalfSide S < Sstar) :
    ((closedSquareSample Λ v (repairHalfSide S)).card : ℝ) ≤ (2 * Sstar + 1) ^ 2 := by
  have hSstar : 0 ≤ Sstar := (repairHalfSide_pos S).le.trans hterm.le
  exact (Nat.cast_le.mpr (Finset.card_le_card
    (closedSquareSample_mono Λ v hterm.le))).trans
      (card_closedSquareSample_le Λ v hSstar)

end TNLean.PEPS.AreaLaw.Geometry
