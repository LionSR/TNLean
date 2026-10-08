/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.concentric_fan_restriction
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon_succ_inter_closedBall
Source labels: prop:two-families, geometry:initial-stars
Source: Section 11, prop:two-families, lines 299–323, especially 308–316; geometry:initial-stars,
lines 333–370, especially 352–363.
Public claim: https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050817719

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFans
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Restriction of concentric triangular fans

Two concentric dyadic squares with consecutive exponents have corresponding
fan triangles for every optional midpoint subdivision. Intersecting a triangle
of the larger fan with the smaller closed square gives the corresponding
triangle of the smaller fan. The metric on the plane is the maximum norm.

The smaller triangle is the image of the larger triangle under the homothety
of ratio one half about their common center. Every point of the larger base
has the same distance from that center, so clipping restricts its radial
coefficient to the interval from zero to one half.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–363, and `prop:two-families`, lines 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A triangle with its base at constant distance `2 * r` from its center
restricts to its image under the homothety of ratio one half.
Auxiliary to Section 11, `geometry:initial-stars`, lines 333–370, especially
352–363, and the actual fan construction in `prop:two-families`, lines 299–323. -/
private theorem radial_triangle_inter_closedBall (c a b : ℝ × ℝ) (r : ℝ)
    (hr : 0 < r) (hbase : ∀ y ∈ segment ℝ a b, dist c y = 2 * r) :
    convexHull ℝ {c, a, b} ∩ Metric.closedBall c r =
      (AffineMap.homothety c (1 / 2 : ℝ)) '' convexHull ℝ {c, a, b} := by
  simp only [← convexJoin_singleton_segment]
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    obtain ⟨v, hv, y, hy, hxy⟩ := mem_convexJoin.mp hx
    have hvc : v = c := Set.mem_singleton_iff.mp hv
    subst v
    rw [segment_eq_image_lineMap] at hxy
    obtain ⟨u, hu, rfl⟩ := hxy
    have hd : u * (2 * r) ≤ r := by
      have hd := Metric.mem_closedBall.mp hball
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hu.1, hbase y hy] at hd
      exact hd
    have hu' : 2 * u ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hr).mp
      nlinarith [hd]
    refine ⟨AffineMap.lineMap c y (2 * u), ?_, ?_⟩
    · exact mem_convexJoin.mpr ⟨c, by simp, y, hy,
        lineMap_mem_segment ℝ c y ⟨by linarith [hu.1], hu'⟩⟩
    · rw [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_lineMap_right]
      congr 1
      ring
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, hv, z, hz, hyz⟩ := mem_convexJoin.mp hy
    have hvc : v = c := Set.mem_singleton_iff.mp hv
    subst v
    rw [segment_eq_image_lineMap] at hyz
    obtain ⟨u, hu, rfl⟩ := hyz
    have hu' : (1 / 2 : ℝ) * u ∈ Set.Icc 0 1 :=
      ⟨mul_nonneg (by norm_num) hu.1, by linarith [hu.2]⟩
    simp only [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_lineMap_right]
    refine ⟨mem_convexJoin.mpr ⟨c, by simp, z, hz,
      lineMap_mem_segment ℝ c z hu'⟩, ?_⟩
    apply Metric.mem_closedBall.mpr
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hu'.1, hbase z hz]
    nlinarith [mul_le_mul_of_nonneg_right hu.2 hr.le]

/-- The actual small and large dyadic squares have the prescribed common center.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363, and the fan
construction in `prop:two-families`, lines 299–323. -/
private theorem concentric_centers (c : ℝ × ℝ) (ℓ : ℕ) :
    let r := (2 : ℝ) ^ ℓ / 2
    cellFanCenter (c.1 - r, c.2 - r) ℓ (0, 0) = c ∧
      cellFanCenter (c.1 - 2 * r, c.2 - 2 * r) (ℓ + 1) (0, 0) = c := by
  dsimp only
  constructor <;> apply Prod.ext <;> simp [cellFanCenter, pow_succ] <;> ring

/-- Halving the displacement from the center halves the dyadic radius.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363, and the fan
construction in `prop:two-families`, lines 299–323. -/
private theorem homothety_half_add (c v : ℝ × ℝ) (ℓ : ℕ) :
    AffineMap.homothety c (1 / 2 : ℝ) (c + ((2 : ℝ) ^ (ℓ + 1) / 2) • v) =
      c + ((2 : ℝ) ^ ℓ / 2) • v := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    add_sub_cancel_left, smul_smul]
  have h : (1 / 2 : ℝ) * ((2 : ℝ) ^ (ℓ + 1) / 2) = (2 : ℝ) ^ ℓ / 2 := by
    rw [pow_succ]
    ring
  rw [h, add_comm]

/-- The corresponding actual fan endpoints are related by the same homothety,
without changing their side or optional midpoint slot.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363, and the fan
construction in `prop:two-families`, lines 299–323. -/
private theorem concentric_endpoints (c : ℝ × ℝ) (ℓ : ℕ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (c.1 - r, c.2 - r)
    let oLarge := (c.1 - 2 * r, c.2 - 2 * r)
    AffineMap.homothety c (1 / 2 : ℝ) (cellFanStart oLarge (ℓ + 1) (0, 0) split i) =
        cellFanStart oSmall ℓ (0, 0) split i ∧
      AffineMap.homothety c (1 / 2 : ℝ) (cellFanEnd oLarge (ℓ + 1) (0, 0) split i) =
        cellFanEnd oSmall ℓ (0, 0) split i := by
  dsimp only
  obtain ⟨hs, hl⟩ := concentric_centers c ℓ
  constructor
  · unfold cellFanStart
    rw [hs, hl]
    exact homothety_half_add c _ ℓ
  · unfold cellFanEnd
    rw [hs, hl]
    exact homothety_half_add c _ ℓ

/-- Clipping a concentric larger fan triangle by the smaller closed square
gives exactly the corresponding smaller actual triangle, for every optional
midpoint mask and slot. Source: Section 11, `geometry:initial-stars`, lines
333–370, especially 352–363, and `prop:two-families`, lines 299–323. -/
theorem cellFanPolygon_succ_inter_closedBall (c : ℝ × ℝ) (ℓ : ℕ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (c.1 - r, c.2 - r)
    let oLarge := (c.1 - 2 * r, c.2 - 2 * r)
    (cellFanPolygon oLarge (ℓ + 1) (0, 0) split i).region ∩
        Metric.closedBall c r =
      (cellFanPolygon oSmall ℓ (0, 0) split i).region := by
  dsimp only
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (c.1 - r, c.2 - r)
  let oLarge := (c.1 - 2 * r, c.2 - 2 * r)
  change (cellFanPolygon oLarge (ℓ + 1) (0, 0) split i).region ∩
    Metric.closedBall c r = (cellFanPolygon oSmall ℓ (0, 0) split i).region
  have hr : 0 < r := div_pos (pow_pos zero_lt_two ℓ) (by norm_num)
  obtain ⟨hs, hl⟩ := concentric_centers c ℓ
  obtain ⟨ha, hb⟩ := concentric_endpoints c ℓ split i
  change AffineMap.homothety c (1 / 2 : ℝ)
    (cellFanStart oLarge (ℓ + 1) (0, 0) split i) = cellFanStart oSmall ℓ (0, 0) split i at ha
  change AffineMap.homothety c (1 / 2 : ℝ)
    (cellFanEnd oLarge (ℓ + 1) (0, 0) split i) = cellFanEnd oSmall ℓ (0, 0) split i at hb
  have hbase : ∀ y ∈ segment ℝ (cellFanStart oLarge (ℓ + 1) (0, 0) split i)
      (cellFanEnd oLarge (ℓ + 1) (0, 0) split i), dist c y = 2 * r := by
    intro y hy
    have hn := norm_sub_cellFanCenter_of_mem_base oLarge (ℓ + 1) (0, 0) split i hy
    rw [hl] at hn
    calc
      dist c y = ‖y - c‖ := by rw [dist_comm, dist_eq_norm]
      _ = (2 : ℝ) ^ (ℓ + 1) / 2 := hn
      _ = 2 * r := by dsimp [r]; rw [pow_succ]; ring
  change convexHull ℝ {cellFanCenter oLarge (ℓ + 1) (0, 0),
    cellFanStart oLarge (ℓ + 1) (0, 0) split i,
    cellFanEnd oLarge (ℓ + 1) (0, 0) split i} ∩ Metric.closedBall c r =
      convexHull ℝ {cellFanCenter oSmall ℓ (0, 0),
        cellFanStart oSmall ℓ (0, 0) split i, cellFanEnd oSmall ℓ (0, 0) split i}
  rw [hl, hs, radial_triangle_inter_closedBall c _ _ r hr hbase,
    (AffineMap.homothety c (1 / 2 : ℝ)).image_convexHull]
  simp only [Set.image_insert_eq, Set.image_singleton,
    AffineMap.homothety_apply_same, ha, hb]

end TNLean.PEPS.AreaLaw.Geometry
