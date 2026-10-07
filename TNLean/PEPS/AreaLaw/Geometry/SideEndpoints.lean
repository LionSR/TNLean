/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivision

/-!
# Endpoints of whole dyadic-cell sides

The endpoints of the four whole fan sides have the ordinary translated
square coordinates. Each endpoint is an actual binary corner of that cell.
These identities hold at every natural scale and every integer cell index.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–306.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.unsplit_endpoint_coordinates
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.cellFan_unsplit_endpoints_coordinates
Source labels: prop:two-families
Source: Section 11, lines 299–306.

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.unsplit_endpoint_corners
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.cellFan_unsplit_endpoints_are_corners
Source labels: prop:two-families
Source: Section 11, lines 299–306.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The exact oriented endpoint coordinates of each whole dyadic-cell side.
Source: area-law Section 11, lines 299–306. -/
theorem cellFan_unsplit_endpoints_coordinates (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (s : Fin 4) :
    (cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩,
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩) =
    match s.val with
    | 0 => ((o.1 + 2 ^ ℓ * (z.1 + 1), o.2 + 2 ^ ℓ * z.2),
        (o.1 + 2 ^ ℓ * (z.1 + 1), o.2 + 2 ^ ℓ * (z.2 + 1)))
    | 1 => ((o.1 + 2 ^ ℓ * (z.1 + 1), o.2 + 2 ^ ℓ * (z.2 + 1)),
        (o.1 + 2 ^ ℓ * z.1, o.2 + 2 ^ ℓ * (z.2 + 1)))
    | 2 => ((o.1 + 2 ^ ℓ * z.1, o.2 + 2 ^ ℓ * (z.2 + 1)),
        (o.1 + 2 ^ ℓ * z.1, o.2 + 2 ^ ℓ * z.2))
    | _ => ((o.1 + 2 ^ ℓ * z.1, o.2 + 2 ^ ℓ * z.2),
        (o.1 + 2 ^ ℓ * (z.1 + 1), o.2 + 2 ^ ℓ * z.2)) := by
  fin_cases s
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1,
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1)),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1,
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1)) = _
    norm_num
    constructor <;> ring
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(-1)),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1)) = _
    norm_num
    constructor <;> ring
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(-1))),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1))) = _
    norm_num
    ring
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1)),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1,
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1))) = _
    norm_num
    ring

/-- The two endpoints of a whole fan side are actual binary corners of the
same dyadic cell. Source: area-law Section 11, lines 299–306. -/
theorem cellFan_unsplit_endpoints_are_corners (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (s : Fin 4) :
    ∃ ε η : Fin 2 × Fin 2,
      cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩ = dyadicCellCorner o ℓ z ε ∧
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ = dyadicCellCorner o ℓ z η := by
  let ε : Fin 2 × Fin 2 := match s.val with
    | 0 => (1, 0)
    | 1 => (1, 1)
    | 2 => (0, 1)
    | _ => (0, 0)
  let η : Fin 2 × Fin 2 := match s.val with
    | 0 => (1, 1)
    | 1 => (0, 1)
    | 2 => (0, 0)
    | _ => (1, 0)
  refine ⟨ε, η, ?_⟩
  have h := cellFan_unsplit_endpoints_coordinates o ℓ z s
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  dsimp only at ha hb
  fin_cases s <;> norm_num [ε, η, dyadicCellCorner] at ha hb ⊢
  all_goals exact ⟨ha, hb⟩

end TNLean.PEPS.AreaLaw.Geometry
