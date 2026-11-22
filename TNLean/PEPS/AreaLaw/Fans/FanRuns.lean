/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Fans.CellFans
import QICLean.Algebra.Combinatorics.IndexInduction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite
import TNLean.PEPS.AreaLaw.Layers.DistanceLayers
import TNLean.PEPS.AreaLaw.Templates.TemplatePolygons

/-!
# Equal-colored runs of a cell fan

Two consecutive triangles of an actual cell fan are joined when their labels
agree. The connected components of this graph are the cyclic runs, and each
run region is the union of its actual closed triangles. Distinct runs with the
same label remain distinct. If every triangle has one label, there is one run
and its region is the whole closed cell.

The perimeter adjacency is defined by the actual segment endpoints. Its
connectivity is proved from the four cyclic sides and their optional midpoint
subdivisions. No matching of opposing cells or choice of global labels is
assumed or constructed here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 313–318.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

## Counting connected runs in a cell fan

Each connected run contains a fan triangle. Thus the number of runs is at
most the number of triangles, which is at most eight. This applies to every
splitting mask and every binary labeling, including a constant labeling.
It applies both to the initial belt fans and to the fully split replacement
fan. The estimate concerns the existing connected-run identifiers only.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, fan runs, lines 299–318, replacement sectors,
lines 398–417, and `geometry:total-repairs`, lines 682–691.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Templates for a fan run

A fan run is the closed union of at most eight allowed triangles in one
square. Its exact ambient lattice sample admits a template whenever that
sample is nonempty. The piece size is the square side, and a fixed multiple
of that side bounds the template length.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, lines 299–318 and 732–740;
the template fields are those of Definition 9.3 (`scanner:template`).
-/

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

private def perimeterGraph (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) : SimpleGraph (CellFanSlot split) where
  Adj i j := i ≠ j ∧ (cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∨
    cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def firstSlot (split : Fin 4 → Bool) (side : Fin 4) : CellFanSlot split :=
  ⟨side, ⟨0, by split <;> norm_num⟩⟩

private def lastSlot (split : Fin 4 → Bool) (side : Fin 4) : CellFanSlot split :=
  ⟨side, ⟨if split side then 1 else 0, by split <;> norm_num⟩⟩

private theorem slot_first_or_last (split : Fin 4 → Bool) (i : CellFanSlot split) :
    i = firstSlot split i.1 ∨ i = lastSlot split i.1 := by
  rcases i with ⟨side, j⟩
  have hj := j.isLt
  cases hs : split side
  · left
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply Fin.ext
    change j.val = 0
    have hj0 : j.val < 1 := by simpa only [hs, Bool.false_eq_true, ↓reduceIte] using hj
    omega
  · have hj' : j.val = 0 ∨ j.val = 1 := by simp [hs] at hj; omega
    rcases hj' with hj' | hj'
    · left
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Fin.ext hj')
    · right
      apply Sigma.ext
      · rfl
      apply heq_of_eq
      apply Fin.ext
      simpa [lastSlot, hs] using hj'

private theorem first_last_reachable (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (side : Fin 4) :
    (perimeterGraph o ℓ z split).Reachable (firstSlot split side) (lastSlot split side) := by
  cases hs : split side
  · have he : firstSlot split side = lastSlot split side := by simp [firstSlot, lastSlot, hs]
    rw [← he]
  · apply SimpleGraph.Adj.reachable
    refine ⟨?_, Or.inl ?_⟩
    · intro he
      have hv := congrArg (fun i : CellFanSlot split => i.2.val) he
      simp [firstSlot, lastSlot, hs] at hv
    · simp [cellFanStart_eq, cellFanEnd_eq, firstSlot, lastSlot, hs]

private theorem last_next_reachable (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (side : Fin 4) :
    (perimeterGraph o ℓ z split).Reachable (lastSlot split side) (firstSlot split (side + 1)) := by
  apply SimpleGraph.Adj.reachable
  refine ⟨?_, Or.inl ?_⟩
  · intro he
    have hv := congrArg Sigma.fst he
    fin_cases side <;> norm_num [lastSlot, firstSlot] at hv
  · fin_cases side <;>
      simp only [cellFanStart_eq, cellFanEnd_eq, firstSlot, lastSlot] <;>
      split_ifs <;> norm_num [cellFanSideVector]

private theorem perimeterGraph_preconnected (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) : (perimeterGraph o ℓ z split).Preconnected := by
  have hsides (side : Fin 4) : (perimeterGraph o ℓ z split).Reachable
      (firstSlot split 0) (firstSlot split side) := by
    apply Fin.cyclic_induction (P := fun side => (perimeterGraph o ℓ z split).Reachable
      (firstSlot split 0) (firstSlot split side))
    · exact SimpleGraph.Reachable.rfl
    · intro side hside
      exact (hside.trans (first_last_reachable o ℓ z split side)).trans
        (last_next_reachable o ℓ z split side)
  have hslots (i : CellFanSlot split) : (perimeterGraph o ℓ z split).Reachable
      (firstSlot split 0) i := by
    rcases slot_first_or_last split i with hi | hi
    · rw [hi]
      exact hsides i.1
    · rw [hi]
      exact (hsides i.1).trans (first_last_reachable o ℓ z split i.1)
  exact fun i j => (hslots i).symm.trans (hslots j)

/-- Consecutive actual fan triangles are joined exactly when their colors agree.
Source: area-law Section 11, lines 313–318. -/
def cellFanRunGraph (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2) :
    SimpleGraph (CellFanSlot split) where
  Adj i j := i ≠ j ∧ (cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∨
    cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i) ∧ family i = family j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The identifier of an equal-colored cyclic run is an actual graph component.
Source: area-law Section 11, lines 313–316. -/
abbrev CellFanRun (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2) :=
  (cellFanRunGraph o ℓ z split family).ConnectedComponent

/-- The closed region of a run is the union of its actual fan triangles.
Source: area-law Section 11, lines 313–316. -/
def cellFanRunRegion (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (R : CellFanRun o ℓ z split family) : Set (ℝ × ℝ) :=
  ⋃ i ∈ R.supp, (cellFanPolygon o ℓ z split i).region

private theorem walk_color_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    {i j : CellFanSlot split} (p : (cellFanRunGraph o ℓ z split family).Walk i j) :
    family i = family j := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact h.2.2.trans ih

/-- All triangles with one run identifier have one color.
Source: area-law Section 11, lines 313–318. -/
theorem cellFanRun_color_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (i j : CellFanSlot split)
    (h : (cellFanRunGraph o ℓ z split family).connectedComponentMk i =
      (cellFanRunGraph o ℓ z split family).connectedComponentMk j) : family i = family j := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact h
  exact walk_color_eq o ℓ z split family p

/-- The run regions cover exactly the closed cell.
Source: area-law Section 11, lines 313–316. -/
theorem cellFanRunRegions_cover (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2) :
    (⋃ R : CellFanRun o ℓ z split family, cellFanRunRegion o ℓ z split family R) =
      closure (dyadicCell o ℓ z) := by
  rw [← cellFanPolygons_cover o ℓ z split]
  ext x
  simp only [cellFanRunRegion, Set.mem_iUnion]
  constructor
  · rintro ⟨R, i, _, hx⟩
    exact ⟨i, hx⟩
  · rintro ⟨i, hx⟩
    refine ⟨(cellFanRunGraph o ℓ z split family).connectedComponentMk i, i, ?_, hx⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl

/-- Consecutive triangles in distinct run identifiers have opposite colors.
Source: area-law Section 11, lines 313–318. -/
theorem cellFanRun_adjacent_colors_ne (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (i j : CellFanSlot split)
    (hadj : cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∨
      cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i)
    (hne : (cellFanRunGraph o ℓ z split family).connectedComponentMk i ≠
      (cellFanRunGraph o ℓ z split family).connectedComponentMk j) : family i ≠ family j := by
  intro hcolor
  apply hne
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  refine ⟨?_, hadj, hcolor⟩
  intro hij
  exact hne (hij ▸ rfl)

/-- A constant-colored fan has one identifier, whose region is the whole closed cell.
Source: area-law Section 11, lines 313–316. -/
theorem cellFanRun_all_equal (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (hfamily : ∀ i j, family i = family j) :
    (∀ i j, (cellFanRunGraph o ℓ z split family).connectedComponentMk i =
      (cellFanRunGraph o ℓ z split family).connectedComponentMk j) ∧
    ∀ R : CellFanRun o ℓ z split family,
      cellFanRunRegion o ℓ z split family R = closure (dyadicCell o ℓ z) := by
  have hle : perimeterGraph o ℓ z split ≤ cellFanRunGraph o ℓ z split family :=
    fun i j h => ⟨h.1, h.2, hfamily i j⟩
  have hconnected := (perimeterGraph_preconnected o ℓ z split).mono hle
  refine ⟨fun i j => SimpleGraph.ConnectedComponent.sound (hconnected i j), ?_⟩
  intro R
  have hR : R.supp = Set.univ := by
    obtain ⟨i, rfl⟩ := R.exists_rep
    ext j
    simp only [Set.mem_univ, iff_true]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
      (SimpleGraph.ConnectedComponent.sound (hconnected j i))
  simp only [cellFanRunRegion, hR, Set.mem_univ, Set.iUnion_true]
  exact cellFanPolygons_cover o ℓ z split

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Any cell fan has at most eight connected runs of equal-colored triangles.
The same bound applies to the fully split replacement fan, independently of
the old identifiers assigned to its wedges.
Source: area-law Section 11, lines 299–318 and 398–417. -/
theorem card_cellFanRun_le_eight (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2) :
    Nat.card (CellFanRun o ℓ z split family) ≤ 8 := by
  have hcard : Nat.card (CellFanRun o ℓ z split family) ≤
      Nat.card (CellFanSlot split) :=
    Nat.card_le_card_of_surjective
      (cellFanRunGraph o ℓ z split family).connectedComponentMk Quot.mk_surjective
  exact hcard.trans (by simpa only [Nat.card_eq_fintype_card] using
    (card_cellFanSlot_bounds split).2)

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The integer sample of an actual closed fan run has a template with at
most eight pieces. The coefficient is uniform in the fan geometry.
Auxiliary to area-law Definition 9.3 (`scanner:template`) and Section 11,
`10-geometry.tex`, lines 299–318 and 732–740. A retained-region lattice point
will supply the nonempty sample in the later geometric construction. -/
theorem CellFanRun.exists_template (Ctpl C_B : ℝ)
    (hCtpl : 1 ≤ Ctpl) (hCB : 16 * Ctpl ≤ C_B)
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (R : CellFanRun o ℓ z split family) (w : ℤ × ℤ)
    (hw : integerPoint w ∈ cellFanRunRegion o ℓ z split family R) :
    ∃ T : Template Ctpl ⌈C_B * (2 : ℝ) ^ ℓ⌉₊ (2 ^ ℓ),
      T.pieceCount ≤ 8 ∧
        ∀ x : ℤ × ℤ,
          x ∈ T.points ↔
            integerPoint x ∈ cellFanRunRegion o ℓ z split family R := by
  classical
  let ι : Type := {t : CellFanSlot split // t ∈ R.supp}
  let e := Fintype.equivFin ι
  let polygon (i : Fin (Fintype.card ι)) :=
    cellFanPolygon o ℓ z split (e.symm i).val
  let sample (i : Fin (Fintype.card ι)) := (polygon i).finite_integerPoints.toFinset
  let points := Finset.univ.biUnion sample
  have hsample (i : Fin (Fintype.card ι)) (x : ℤ × ℤ) :
      x ∈ sample i ↔ integerPoint x ∈ (polygon i).region :=
    (polygon i).finite_integerPoints.mem_toFinset
  have hpoints (x : ℤ × ℤ) :
      x ∈ points ↔ integerPoint x ∈ cellFanRunRegion o ℓ z split family R := by
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
      x ∈ closure (dyadicCell o ℓ z) :=
    (cellFanPolygons_cover o ℓ z split).le
      (Set.mem_iUnion.mpr ⟨(e.symm i).val, hx⟩)
  have hdiam (x y : ℝ × ℝ) (hx : x ∈ closure (dyadicCell o ℓ z))
      (hy : y ∈ closure (dyadicCell o ℓ z)) :
      max |x.1 - y.1| |x.2 - y.2| ≤ (2 : ℝ) ^ ℓ := by
    simpa only [Nat.cast_zero, zero_add, one_mul, Prod.dist_eq, Real.dist_eq] using
      dyadicCell_dist_le o ℓ z z 0 x y hx hy (by simp)
  have hpointcell (x : ℤ × ℤ) (hx : x ∈ points) :
      integerPoint x ∈ closure (dyadicCell o ℓ z) :=
    (cellFanRunRegions_cover o ℓ z split family).le
      (Set.mem_iUnion.mpr ⟨R, (hpoints x).mp hx⟩)
  have hu : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  have hCBone : (1 : ℝ) ≤ C_B := by linarith only [hCtpl, hCB]
  have hn : (2 : ℝ) ^ ℓ ≤ (⌈C_B * (2 : ℝ) ^ ℓ⌉₊ : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_right hCBone (le_trans zero_le_one hu),
      Nat.le_ceil (C_B * (2 : ℝ) ^ ℓ)]
  have hnpos : 0 < ⌈C_B * (2 : ℝ) ^ ℓ⌉₊ := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (hu.trans hn))
  have hmR : (Fintype.card ι : ℝ) ≤ 8 := by exact_mod_cast hm
  have hfactor : Ctpl * (Fintype.card ι : ℝ) ≤ Ctpl * 8 :=
    mul_le_mul_of_nonneg_left hmR (le_trans zero_le_one hCtpl)
  have hplus : (2 : ℝ) ^ ℓ + 1 ≤ 2 * (2 : ℝ) ^ ℓ := by linarith only [hu]
  have hscale0 : Ctpl * (Fintype.card ι : ℝ) * ((2 : ℝ) ^ ℓ + 1) ≤
      16 * Ctpl * (2 : ℝ) ^ ℓ := by
    nlinarith only [mul_le_mul hfactor hplus (by positivity)
      (mul_nonneg (le_trans zero_le_one hCtpl) (by norm_num))]
  have hscale : Ctpl * (Fintype.card ι : ℝ) * ((2 : ℝ) ^ ℓ + 1) ≤
      (⌈C_B * (2 : ℝ) ^ ℓ⌉₊ : ℝ) :=
    hscale0.trans
      ((mul_le_mul_of_nonneg_right hCB (le_trans zero_le_one hu)).trans
        (Nat.le_ceil (C_B * (2 : ℝ) ^ ℓ)))
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

end
