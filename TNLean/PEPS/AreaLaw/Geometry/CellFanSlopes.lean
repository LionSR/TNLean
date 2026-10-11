/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFans

/-!
# Prescribed slopes of cell-fan edges

The elementary perimeter edge and the radial edge from its final endpoint
to the center have one of the four prescribed slopes. The assertion concerns
the existing actual fan and permits every optional midpoint subdivision.
The origin, dyadic exponent and signed cell index are arbitrary.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`,
lines 308–310, and `geometry:initial-stars`, lines 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The base and last radial edge have the slopes carried by the actual
triangle constructor. Auxiliary to Section 11, `prop:two-families`,
lines 308–310, and `geometry:initial-stars`, lines 352–359. -/
private theorem triangle_base_and_last_slopes (P : TemplatePolygon) :
    match P with
    | .triangle a b c _ _ _ _ => IsAllowedSlope (c - b) ∧ IsAllowedSlope (a - c)
    | .rectangle _ _ _ _ _ _ _ _ => True := by
  cases P with
  | triangle _ _ _ _ _ hbc hca => exact ⟨hbc, hca⟩
  | rectangle => trivial

/-- The elementary base and the final radial edge of an actual fan triangle
have allowed slopes. Source: area-law Section 11,
`prop:two-families`, lines 308–310, and `geometry:initial-stars`, lines 352–359. -/
theorem cellFanPolygon_base_and_radial_isAllowedSlope
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    IsAllowedSlope (cellFanEnd o ℓ z split i - cellFanStart o ℓ z split i) ∧
      IsAllowedSlope (cellFanCenter o ℓ z - cellFanEnd o ℓ z split i) := by
  exact triangle_base_and_last_slopes (cellFanPolygon o ℓ z split i)

end TNLean.PEPS.AreaLaw.Geometry
