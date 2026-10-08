/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cell_frontier_side
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.exists_dyadicCellSide_of_mem_frontier
Source labels: prop:two-families, geometry:initial-stars
Source: Section 11, prop:two-families, lines 299–323; geometry:initial-stars, lines 333–370,
especially 352–359.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellContacts

/-!
# Whole sides of a dyadic square

Every boundary point of an actual translated dyadic square belongs to one of
its four whole sides. The origin, natural exponent and signed cell index are
arbitrary. The argument is shared by dummy contacts and the local geometry
of initial stars.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323,
and `geometry:initial-stars`, lines 333–370, especially 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Every frontier point of an actual translated dyadic square lies on a whole
side. Source: area-law Section 11, `prop:two-families`, lines 299–323,
and `geometry:initial-stars`, lines 333–370, especially 352–359. -/
theorem exists_dyadicCellSide_of_mem_frontier (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (x : ℝ × ℝ) (hx : x ∈ frontier (dyadicCell o ℓ z)) :
    ∃ s : Fin 4, x ∈ dyadicCellSide o ℓ z s := by
  let A := o.1 + (2 : ℝ) ^ ℓ * z.1
  let A' := o.1 + (2 : ℝ) ^ ℓ * (z.1 + 1)
  let B := o.2 + (2 : ℝ) ^ ℓ * z.2
  let B' := o.2 + (2 : ℝ) ^ ℓ * (z.2 + 1)
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  have hA : A < A' := by dsimp [A, A']; linarith
  have hB : B < B' := by dsimp [B, B']; linarith
  have hfront : frontier (dyadicCell o ℓ z) =
      (Set.Icc A A' ×ˢ {B, B'}) ∪ ({A, A'} ×ˢ Set.Icc B B') := by
    change frontier (Set.Ico A A' ×ˢ Set.Ico B B') = _
    rw [frontier_prod_eq, frontier_Ico hB, frontier_Ico hA,
      closure_Ico hA.ne, closure_Ico hB.ne]
  have hcoords (s : Fin 4) := congrArg
    (fun ab : (ℝ × ℝ) × (ℝ × ℝ) ↦ segment ℝ ab.1 ab.2)
    (cellFan_unsplit_endpoints_coordinates o ℓ z s)
  rw [hfront] at hx
  rcases hx with ⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩
  · rcases hx₂ with hx₂ | hx₂
    · refine ⟨3, ?_⟩
      have hs := hcoords 3
      norm_num at hs
      rw [dyadicCellSide, hs, ← Prod.image_mk_segment_left, segment_eq_Icc hA.le]
      exact ⟨x.1, hx₁, Prod.ext rfl hx₂.symm⟩
    · refine ⟨1, ?_⟩
      have hs := hcoords 1
      norm_num at hs
      rw [dyadicCellSide, hs, segment_symm, ← Prod.image_mk_segment_left,
        segment_eq_Icc hA.le]
      exact ⟨x.1, hx₁, Prod.ext rfl hx₂.symm⟩
  · rcases hx₁ with hx₁ | hx₁
    · refine ⟨2, ?_⟩
      have hs := hcoords 2
      norm_num at hs
      rw [dyadicCellSide, hs, segment_symm, ← Prod.image_mk_segment_right,
        segment_eq_Icc hB.le]
      exact ⟨x.2, hx₂, Prod.ext hx₁.symm rfl⟩
    · refine ⟨0, ?_⟩
      have hs := hcoords 0
      norm_num at hs
      rw [dyadicCellSide, hs, ← Prod.image_mk_segment_right, segment_eq_Icc hB.le]
      exact ⟨x.2, hx₂, Prod.ext hx₁.symm rfl⟩

end TNLean.PEPS.AreaLaw.Geometry
