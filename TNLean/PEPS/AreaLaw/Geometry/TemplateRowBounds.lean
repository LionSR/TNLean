/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows
import TNLean.PEPS.AreaLaw.Geometry.TemplatePolygons

/-!
# Rounded row bounds from actual template polygons

The supporting-strip characterization gives integer affine endpoint formulas.
Consequently nonempty sampled rows are consecutive, and their endpoints move
by at most one between consecutive rows. These are consequences of the actual
polygon model, including exact sampling, rather than additional assumptions.

Original formalization of the geometric argument in manuscript Lemma 9.4;
no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026; scanner:templates (Lemma 9.4).
Revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original formalization; no upstream Lean proof text reused.
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.template.exists_sample_four_strip_bounds
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.exists_sample_four_strip_bounds
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.template.exists_latticerow_profile
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.exists_latticeRow_profile
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.template.latticerow_nonempty_between
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_nonempty_between
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.template.latticerow_min_step
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_min_step
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.template.latticerow_max_step
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.latticeRow_max_step
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.template.exists_sample_in_window_between
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.exists_sample_in_window_between
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.template.exists_nearby_sample_in_row
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.Template.exists_nearby_sample_in_row
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Exact sampling rounds the eight real supporting-strip bounds, including
negative intercepts and polygons with no sampled lattice points. -/
theorem Template.exists_sample_four_strip_bounds {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) :
    ∃ lx ux ly uy ls us ld ud : ℤ, ∀ x y : ℤ,
      (x, y) ∈ T.sample i ↔ (lx ≤ x ∧ x ≤ ux) ∧ (ly ≤ y ∧ y ≤ uy) ∧
        (ls ≤ x + y ∧ x + y ≤ us) ∧ (ld ≤ x - y ∧ x - y ≤ ud) := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ :=
    (T.polygon i).exists_four_strip_bounds
  refine ⟨⌈lx⌉, ⌊ux⌋, ⌈ly⌉, ⌊uy⌋, ⌈ls⌉, ⌊us⌋, ⌈ld⌉, ⌊ud⌋, fun x y ↦ ?_⟩
  rw [T.mem_sample, h]
  simp only [integerPoint, Int.ceil_le, Int.le_floor, Int.cast_add, Int.cast_sub]

/-- A sampled row has max/min affine integer endpoints when the vertical strip
allows it. The endpoint interval may still be empty. -/
theorem Template.exists_latticeRow_profile {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) :
    ∃ lx ux ly uy ls us ld ud : ℤ, ∀ y : ℤ,
      latticeRow (T.sample i) y = if ly ≤ y ∧ y ≤ uy then
        Finset.Icc (max lx (max (ls - y) (ld + y)))
          (min ux (min (us - y) (ud + y))) else ∅ := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ := T.exists_sample_four_strip_bounds i
  refine ⟨lx, ux, ly, uy, ls, us, ld, ud, fun y ↦ ?_⟩
  ext x
  rw [mem_latticeRow, h]
  by_cases hy : ly ≤ y ∧ y ≤ uy
  · rw [ite_eq_left hy]
    simp only [Finset.mem_Icc, max_le_iff, le_min_iff]
    omega
  · rw [ite_eq_right hy]
    constructor
    · intro hs
      exact (hy hs.2.1).elim
    · intro hx
      exact (Finset.notMem_empty x hx).elim

/-- Nonempty rows of an actual sampled polygon form an integer interval. -/
theorem Template.latticeRow_nonempty_between {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) {a b y : ℤ}
    (ha : (latticeRow (T.sample i) a).Nonempty)
    (hb : (latticeRow (T.sample i) b).Nonempty) (hay : a ≤ y) (hyb : y ≤ b) :
    (latticeRow (T.sample i) y).Nonempty := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ := T.exists_sample_four_strip_bounds i
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  have hsa := (h xa a).mp (mem_latticeRow.mp hxa)
  have hsb := (h xb b).mp (mem_latticeRow.mp hxb)
  refine ⟨max lx (max (ls - y) (ld + y)), ?_⟩
  apply mem_latticeRow.mpr
  apply (h _ y).mpr
  omega

/-- Lower endpoints of consecutive nonempty sampled rows differ by at most one. -/
theorem Template.latticeRow_min_step {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (y : ℤ)
    (h₀ : (latticeRow (T.sample i) y).Nonempty)
    (h₁ : (latticeRow (T.sample i) (y + 1)).Nonempty) :
    (latticeRow (T.sample i) (y + 1)).min' h₁ ≤
        (latticeRow (T.sample i) y).min' h₀ + 1 ∧
      (latticeRow (T.sample i) y).min' h₀ ≤
        (latticeRow (T.sample i) (y + 1)).min' h₁ + 1 := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ := T.exists_sample_four_strip_bounds i
  have hs₀ := (h _ y).mp (mem_latticeRow.mp (Finset.min'_mem _ h₀))
  have hs₁ := (h _ (y + 1)).mp (mem_latticeRow.mp (Finset.min'_mem _ h₁))
  have hL₀ : max lx (max (ls - y) (ld + y)) ∈ latticeRow (T.sample i) y := by
    apply mem_latticeRow.mpr
    apply (h _ y).mpr
    omega
  have hL₁ : max lx (max (ls - (y + 1)) (ld + (y + 1))) ∈
      latticeRow (T.sample i) (y + 1) := by
    apply mem_latticeRow.mpr
    apply (h _ (y + 1)).mpr
    omega
  have hm₀ := Finset.min'_le _ _ hL₀
  have hm₁ := Finset.min'_le _ _ hL₁
  constructor <;> omega

/-- Upper endpoints of consecutive nonempty sampled rows differ by at most one. -/
theorem Template.latticeRow_max_step {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (y : ℤ)
    (h₀ : (latticeRow (T.sample i) y).Nonempty)
    (h₁ : (latticeRow (T.sample i) (y + 1)).Nonempty) :
    (latticeRow (T.sample i) (y + 1)).max' h₁ ≤
        (latticeRow (T.sample i) y).max' h₀ + 1 ∧
      (latticeRow (T.sample i) y).max' h₀ ≤
        (latticeRow (T.sample i) (y + 1)).max' h₁ + 1 := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ := T.exists_sample_four_strip_bounds i
  have hs₀ := (h _ y).mp (mem_latticeRow.mp (Finset.max'_mem _ h₀))
  have hs₁ := (h _ (y + 1)).mp (mem_latticeRow.mp (Finset.max'_mem _ h₁))
  have hU₀ : min ux (min (us - y) (ud + y)) ∈ latticeRow (T.sample i) y := by
    apply mem_latticeRow.mpr
    apply (h _ y).mpr
    omega
  have hU₁ : min ux (min (us - (y + 1)) (ud + (y + 1))) ∈
      latticeRow (T.sample i) (y + 1) := by
    apply mem_latticeRow.mpr
    apply (h _ (y + 1)).mpr
    omega
  have hm₀ := Finset.le_max' _ _ hU₀
  have hm₁ := Finset.le_max' _ _ hU₁
  constructor <;> omega

/-- Restricting to a vertical window preserves consecutive occupied columns.
This supplies horizontal interval rows after ambient integer dilation. -/
theorem Template.exists_sample_in_window_between {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) {a b x za zb lo hi : ℤ}
    (ha : (a, za) ∈ T.sample i) (hb : (b, zb) ∈ T.sample i)
    (hza : lo ≤ za ∧ za ≤ hi) (hzb : lo ≤ zb ∧ zb ≤ hi)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ∃ z : ℤ, (x, z) ∈ T.sample i ∧ lo ≤ z ∧ z ≤ hi := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ := T.exists_sample_four_strip_bounds i
  have hsa := (h a za).mp ha
  have hsb := (h b zb).mp hb
  refine ⟨max lo (max ly (max (ls - x) (x - ud))), ?_, ?_, ?_⟩
  · apply (h x _).mpr
    omega
  · omega
  · omega

/-- A sampled point can be moved to any occupied adjacent row while changing
its horizontal coordinate by at most one. -/
theorem Template.exists_nearby_sample_in_row {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) {x y z : ℤ}
    (hp : (x, y) ∈ T.sample i) (hyz : y - 1 ≤ z ∧ z ≤ y + 1)
    (hz : (latticeRow (T.sample i) z).Nonempty) :
    ∃ w : ℤ, (w, z) ∈ T.sample i ∧ x - 1 ≤ w ∧ w ≤ x + 1 := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ := T.exists_sample_four_strip_bounds i
  have hp' := (h x y).mp hp
  obtain ⟨w, hw⟩ := hz
  have hw' := (h w z).mp (mem_latticeRow.mp hw)
  let L := max lx (max (ls - z) (ld + z))
  let U := min ux (min (us - z) (ud + z))
  have hLU : L ≤ U := by dsimp [L, U]; omega
  have hL : L ≤ x + 1 := by dsimp [L]; omega
  have hU : x - 1 ≤ U := by dsimp [U]; omega
  refine ⟨max L (min x U), ?_, ?_, ?_⟩
  · apply (h _ z).mpr
    dsimp [L, U] at *
    omega
  · omega
  · omega

end TNLean.PEPS.AreaLaw.Geometry
