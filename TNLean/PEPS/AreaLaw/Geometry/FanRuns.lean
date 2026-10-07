/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFans
import TNLean.Algebra.FinCyclicInduction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/
  sections/
  10-geometry.tex
Labels: prop:two-families.
Source lines: 313–318.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cellfanrungraph
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cellFanRunGraph
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cellfanrun
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.CellFanRun
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cellfanrunregion
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegion
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cellfanrun_color_eq
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cellFanRun_color_eq
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cellfanrunregions_cover
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegions_cover
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cellfanrun_adjacent_colors_ne
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cellFanRun_adjacent_colors_ne
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cellfanrun_all_equal
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cellFanRun_all_equal
-/


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
    · dsimp only [firstSlot, lastSlot, cellFanEnd, cellFanStart]
      congr 1
      change (if split side then ((0 : ℕ) : ℝ) else 1) =
        (if split side then ((if split side then 1 else 0 : ℕ) : ℝ) - 1 else -1)
      simp [hs]

private theorem last_next_reachable (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (side : Fin 4) :
    (perimeterGraph o ℓ z split).Reachable (lastSlot split side) (firstSlot split (side + 1)) := by
  apply SimpleGraph.Adj.reachable
  refine ⟨?_, Or.inl ?_⟩
  · intro he
    have hv := congrArg Sigma.fst he
    fin_cases side <;> norm_num [lastSlot, firstSlot] at hv
  · let c := cellFanCenter o ℓ z
    let r := (2 : ℝ) ^ ℓ / 2
    fin_cases side
    · change (c.1 + r * 1, c.2 + r *
        (if split 0 then ((if split 0 then 1 else 0 : ℕ) : ℝ) else 1)) =
        (c.1 + r * -(if split 1 then ((0 : ℕ) : ℝ) - 1 else -1), c.2 + r * 1)
      split_ifs <;> norm_num
    · change (c.1 + r * -(if split 1 then ((if split 1 then 1 else 0 : ℕ) : ℝ) else 1),
        c.2 + r * 1) = (c.1 + r * -1,
        c.2 + r * -(if split 2 then ((0 : ℕ) : ℝ) - 1 else -1))
      split_ifs <;> norm_num
    · change (c.1 + r * -1,
        c.2 + r * -(if split 2 then ((if split 2 then 1 else 0 : ℕ) : ℝ) else 1)) =
        (c.1 + r * (if split 3 then ((0 : ℕ) : ℝ) - 1 else -1), c.2 + r * -1)
      split_ifs <;> norm_num
    · change (c.1 + r * (if split 3 then ((if split 3 then 1 else 0 : ℕ) : ℝ) else 1),
        c.2 + r * -1) = (c.1 + r * 1,
        c.2 + r * (if split 0 then ((0 : ℕ) : ℝ) - 1 else -1))
      split_ifs <;> norm_num

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
