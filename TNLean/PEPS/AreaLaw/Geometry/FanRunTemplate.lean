/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DistanceLayers
import TNLean.PEPS.AreaLaw.Geometry.FanRuns
import TNLean.PEPS.AreaLaw.Geometry.TemplatePolygonFiniteIntegerPoints

/-!
# Templates for a fan run

A fan run is the closed union of at most eight allowed triangles in one
square. Its exact ambient lattice sample admits a template whenever that
sample is nonempty. The piece size is the square side, and a fixed multiple
of that side bounds the template length.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, lines 299–318 and 732–740;
the template fields are those of Definition 9.3 (`scanner:template`).
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The integer sample of an actual closed fan run has a template with at
most eight pieces. The coefficient is uniform in the fan geometry.
Auxiliary to area-law Definition 9.3 (`scanner:template`) and Section 11,
`10-geometry.tex`, lines 299–318 and 732–740. A retained-region lattice point
will supply the nonempty sample in the later geometric construction. -/
theorem CellFanRun.exists_template (Ctpl C_B : ℝ)
    (hCtpl : 1 ≤ Ctpl) (hCB : 16 * Ctpl ≤ C_B)
    (o : ℝ × ℝ) (â : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (R : CellFanRun o â z split family) (w : ℤ × ℤ)
    (hw : integerPoint w ∈ cellFanRunRegion o â z split family R) :
    ∃ T : Template Ctpl ⌈C_B * (2 : ℝ) ^ â⌉₊ (2 ^ â),
      T.pieceCount ≤ 8 ∧
        ∀ x : ℤ × ℤ,
          x ∈ T.points ↔
            integerPoint x ∈ cellFanRunRegion o â z split family R := by
  classical
  let ι : Type := {t : CellFanSlot split // t ∈ R.supp}
  let e := Fintype.equivFin ι
  let polygon (i : Fin (Fintype.card ι)) :=
    cellFanPolygon o â z split (e.symm i).val
  let sample (i : Fin (Fintype.card ι)) := (polygon i).finite_integerPoints.toFinset
  let points := Finset.univ.biUnion sample
  have hsample (i : Fin (Fintype.card ι)) (x : ℤ × ℤ) :
      x ∈ sample i ↔ integerPoint x ∈ (polygon i).region :=
    (polygon i).finite_integerPoints.mem_toFinset
  have hpoints (x : ℤ × ℤ) :
      x ∈ points ↔ integerPoint x ∈ cellFanRunRegion o â z split family R := by
    simp only [points, Finset.mem_biUnion, Finset.mem_univ, true_and, hsample,
      cellFanRunRegion, Set.mem_iUnion]
    refine ⟨(fun ⟨i, hix⟩ ↦ ⟨(e.symm i).val, (e.symm i).property, hix⟩), ?_⟩
    rintro ⟨t, ht, hxt⟩
    refine ⟨e ⟨t, ht⟩, ?_⟩
    simpa only [polygon, Equiv.symm_apply_apply] using hxt
  have hnonempty : points.Nonempty := ⟨w, (hpoints w).mpr hw⟩
  have hm : Fintype.card ι ≤ 8 :=
    (Fintype.card_subtype_le (fun t : CellFanSlot split ↦ t ∈ R.supp)).trans
      (card_cellFanSlot_bounds split).2
  obtain ⟨i, _, _⟩ := Finset.mem_biUnion.mp ((hpoints w).mpr hw)
  have hmpos : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le i.val) i.is_lt
  have hcell (i : Fin (Fintype.card ι)) (x : ℝ × ℝ) (hx : x ∈ (polygon i).region) :
      x ∈ closure (dyadicCell o â z) :=
    (cellFanPolygons_cover o â z split).le
      (Set.mem_iUnion.mpr ⟨(e.symm i).val, hx⟩)
  have hdiam (x y : ℝ × ℝ) (hx : x ∈ closure (dyadicCell o â z))
      (hy : y ∈ closure (dyadicCell o â z)) :
      max |x.1 - y.1| |x.2 - y.2| ≤ (2 : ℝ) ^ â := by
    simpa only [Nat.cast_zero, zero_add, one_mul, Prod.dist_eq, Real.dist_eq] using
      dyadicCell_dist_le o â z z 0 x y hx hy (by simp)
  have hpointcell (x : ℤ × ℤ) (hx : x ∈ points) :
      integerPoint x ∈ closure (dyadicCell o â z) :=
    (cellFanRunRegions_cover o â z split family).le
      (Set.mem_iUnion.mpr ⟨R, (hpoints x).mp hx⟩)
  have hu : (1 : ℝ) ≤ (2 : ℝ) ^ â := one_le_pow₀ (by norm_num)
  have hCBone : (1 : ℝ) ≤ C_B := by linarith only [hCtpl, hCB]
  have hn : (2 : ℝ) ^ â ≤ (⌈C_B * (2 : ℝ) ^ â⌉₊ : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_right hCBone (le_trans zero_le_one hu),
      Nat.le_ceil (C_B * (2 : ℝ) ^ â)]
  have hnpos : 0 < ⌈C_B * (2 : ℝ) ^ â⌉₊ := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (hu.trans hn))
  have hmR : (Fintype.card ι : ℝ) ≤ 8 := by exact_mod_cast hm
  have hfactor : Ctpl * (Fintype.card ι : ℝ) ≤ Ctpl * 8 :=
    mul_le_mul_of_nonneg_left hmR (le_trans zero_le_one hCtpl)
  have hplus : (2 : ℝ) ^ â + 1 ≤ 2 * (2 : ℝ) ^ â := by linarith only [hu]
  have hscale0 : Ctpl * (Fintype.card ι : ℝ) * ((2 : ℝ) ^ â + 1) ≤
      16 * Ctpl * (2 : ℝ) ^ â := by
    nlinarith only [mul_le_mul hfactor hplus (by positivity)
      (mul_nonneg (le_trans zero_le_one hCtpl) (by norm_num))]
  have hscale : Ctpl * (Fintype.card ι : ℝ) * ((2 : ℝ) ^ â + 1) ≤
      (⌈C_B * (2 : ℝ) ^ â⌉₊ : ℝ) :=
    hscale0.trans
      ((mul_le_mul_of_nonneg_right hCB (le_trans zero_le_one hu)).trans
        (Nat.le_ceil (C_B * (2 : ℝ) ^ â)))
  refine ⟨{
    n_pos := hnpos
    s₀_pos := by positivity
    pieceCount := Fintype.card ι
    pieceCount_pos := hmpos
    polygon := polygon
    sample := sample
    mem_sample := hsample
    piece_diameter := fun i x hx y hy ↦ by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        hdiam x y (hcell i x hx) (hcell i y hy)
    points := points
    nonempty := hnonempty
    cover := rfl
    scale := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale
    diameter := fun x hx y hy ↦
      (hdiam (integerPoint x) (integerPoint y) (hpointcell x hx) (hpointcell y hy)).trans hn
  }, hm, hpoints⟩

end TNLean.PEPS.AreaLaw.Geometry
