/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRuns
import TNLean.PEPS.AreaLaw.Geometry.CellFanCycle
import TNLean.PEPS.AreaLaw.Geometry.CellFanRays
import TNLean.PEPS.AreaLaw.Geometry.CellFanRadialIncidence
import TNLean.PEPS.AreaLaw.Geometry.FanRadialPieces
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Intersections across inactive fan radials

Adjacent equally colored triangles of an actual all-midpoint fan retain a
common point inside the open dyadic square after the family-change radials
are removed. The midpoint of their common radial supplies that point.
The change set may be empty; distinct runs bearing the same color remain
separate graph components.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–370,
and `prop:two-families`, lines 308–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The retained part of one triangle of the actual all-midpoint fan.
The color-change radials are removed, and the triangle is restricted to the
open ball whose radius is the half-side of the dyadic cell.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and
`prop:two-families`, lines 308–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The color assignment is arbitrary, and the change set may be empty. -/
def cellFanCutPiece (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2)
    (s : CellFanSlot (fun _ : Fin 4 ↦ true)) : Set (ℝ × ℝ) :=
  ((cellFanPolygon o ℓ z (fun _ ↦ true) s).region \
      (⋃ t ∈ {t | family t ≠ family (cellFanNext t)},
        segment ℝ (cellFanCenter o ℓ z)
          (cellFanEnd o ℓ z (fun _ ↦ true) t))) ∩
    Metric.ball (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2)

/-- Adjacent equally colored triangles of the actual all-midpoint fan have
a common point in the open centered square after all color-change radials
are removed. The radius is the actual half-side of the dyadic cell.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and
`prop:two-families`, lines 308–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The color assignment is arbitrary. No active radial is assumed to exist,
and separated graph components bearing the same color remain distinct. -/
theorem cellFanPolygon_cut_inter_nonempty_of_adj
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2)
    (i j : CellFanSlot (fun _ : Fin 4 ↦ true))
    (hadj : (cellFanRunGraph o ℓ z (fun _ ↦ true) family).Adj i j) :
    (cellFanCutPiece o ℓ z family i ∩ cellFanCutPiece o ℓ z family j).Nonempty := by
  have horient := hadj.2.1
  have hforward (u v : CellFanSlot (fun _ : Fin 4 ↦ true))
      (he : cellFanEnd o ℓ z (fun _ ↦ true) u =
        cellFanStart o ℓ z (fun _ ↦ true) v)
      (hc : family u = family v) :
      (cellFanCutPiece o ℓ z family u ∩ cellFanCutPiece o ℓ z family v).Nonempty := by
    have hv : v = cellFanNext u :=
      (cellFanEnd_eq_cellFanStart_iff o ℓ z u v).mp he
    have hce : dist (cellFanCenter o ℓ z)
        (cellFanEnd o ℓ z (fun _ ↦ true) u) = (2 : ℝ) ^ ℓ / 2 :=
      (dist_eq_norm_vsub' (ℝ × ℝ) _ _).trans
        (norm_sub_cellFanCenter_of_mem_base o ℓ z (fun _ ↦ true) u
          (right_mem_segment ℝ _ _))
    have hr : 0 < (2 : ℝ) ^ ℓ / 2 :=
      div_pos (pow_pos zero_lt_two ℓ) zero_lt_two
    let m := midpoint ℝ (cellFanCenter o ℓ z)
      (cellFanEnd o ℓ z (fun _ ↦ true) u)
    have hdist : dist m (cellFanCenter o ℓ z) = ((2 : ℝ) ^ ℓ / 2) / 2 := by
      simpa only [Real.norm_two, hce, inv_mul_eq_div] using
        (dist_midpoint_left (𝕜 := ℝ) (cellFanCenter o ℓ z)
          (cellFanEnd o ℓ z (fun _ ↦ true) u))
    have hmball : m ∈ Metric.ball (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) :=
      Metric.mem_ball.mpr (hdist.trans_lt (half_lt_self hr))
    have hmc : m ≠ cellFanCenter o ℓ z :=
      dist_pos.mp (hdist.symm ▸ div_pos hr zero_lt_two)
    have hmradial : m ∈ segment ℝ (cellFanCenter o ℓ z)
        (cellFanEnd o ℓ z (fun _ ↦ true) u) :=
      midpoint_mem_segment (𝕜 := ℝ) _ _
    have huinactive : family u = family (cellFanNext u) :=
      hc.trans (congrArg family hv)
    have hmcut : m ∉ ⋃ t ∈ {t | family t ≠ family (cellFanNext t)},
        segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z (fun _ ↦ true) t) := by
      intro hmL
      obtain ⟨t, ht, hmt⟩ := Set.mem_iUnion₂.mp hmL
      have hut : u = t :=
        (cellFanEnd_sameRay_iff o ℓ z (fun _ ↦ true) u t).mp
          ((mem_segment_iff_wbtw.mp hmradial).sameRay_vsub_left.symm.trans
            (mem_segment_iff_wbtw.mp hmt).sameRay_vsub_left
            (fun h0 ↦ (hmc (sub_eq_zero.mp h0)).elim))
      exact ht (hut ▸ huinactive)
    exact ⟨m,
      ⟨⟨(cellFanPolygon_mem_iff_of_mem_radial o ℓ z (fun _ ↦ true) u u m
        hmc hmradial).mpr (Or.inl rfl), hmcut⟩, hmball⟩,
      ⟨⟨(cellFanPolygon_mem_iff_of_mem_radial o ℓ z (fun _ ↦ true) v u m
        hmc hmradial).mpr (Or.inr he), hmcut⟩, hmball⟩⟩
  exact horient.elim (fun h ↦ hforward i j h hadj.2.2)
    (fun h ↦ Set.inter_comm (cellFanCutPiece o ℓ z family j)
      (cellFanCutPiece o ℓ z family i) ▸ hforward j i h hadj.2.2.symm)

end TNLean.PEPS.AreaLaw.Geometry
