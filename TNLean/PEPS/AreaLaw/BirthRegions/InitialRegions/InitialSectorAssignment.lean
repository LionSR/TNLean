/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.InitialStarFrontiers
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.InitialRegions
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.CellFanSectors
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.CellFans
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.AdjacentScales
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Convex.Hull
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.CellFanCycle
import Mathlib.Data.Finset.SymmDiff
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Even
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.FanRuns
import Mathlib.Logic.Relation

/-!
# Actual initial regions in the eight open sectors

Around an actual fine-cell mark, the eight open triangles of a concentric
midpoint-subdivided fan each lie in one actual initial open region. Their
assignment is unique. In the smaller concentric closed square, every initial
birth region is exactly the union of its assigned smaller triangles.

The actual cell and mark memberships imply that the endpoint set is nonempty.
Closed coverage and frontier exclusion give the assignment by preconnectedness.
The finite union of the open triangles is dense in the working square; the
regularity of actual birth regions then gives the closed equality, including
identifiers assigned no triangle. The metric on the plane is the maximum norm.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.initialRegion_sector_assignment_adjacent_colors_eq_iff`: colors of
  adjacent actual sectors.
* `TNLean.PEPS.AreaLaw.Geometry.initialRegion_sector_assignment_changes_even`: evenness of actual
  initial-sector changes.
* `TNLean.PEPS.AreaLaw.Geometry.exists_unique_initialRegion_sector_run_assignment`,
  `TNLean.PEPS.AreaLaw.Geometry.exists_unique_initialRegion_of_no_active_sector`: actual initial
  identifiers on local sector runs.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–370, and `prop:two-families`, lines 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (closure_dyadicCell dyadicCell dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
  dyadicLayer_exists_dist_le fineLayerIndices)

namespace TNLean.PEPS.AreaLaw.Geometry

section InitialSectorAssignment

/-- Density inside an open neighborhood extends an open-region containment to
its closure, even when the containing closed set is empty.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–370, and the actual
initial regions in `prop:two-families`, lines 308–323. -/
private theorem closure_inter_subset_of_dense_inter
    (U D W E : Set (ℝ × ℝ)) (hU : IsOpen U) (hW : IsOpen W)
    (hWD : W ⊆ closure D) (hE : IsClosed E) (hUD : U ∩ D ⊆ E) :
    closure U ∩ W ⊆ E := by
  have hUW : U ∩ W ⊆ E := by
    intro x hx
    exact closure_minimal hUD hE (hU.inter_closure ⟨hx.1, hWD hx.2⟩)
  exact fun _ hx ↦ closure_minimal hUW hE (hW.closure_inter hx)

/-- A nonempty preconnected set avoiding all frontiers belongs to exactly one
member of a regular closed cover with pairwise disjoint interiors.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–370, and the actual
initial identifiers in `prop:two-families`, lines 308–323. -/
private theorem preconnected_unique_interior {I : Type*}
    (B : I → Set (ℝ × ℝ)) (S : Set (ℝ × ℝ)) (hSnon : S.Nonempty)
    (hS : IsPreconnected S) (hcover : ∀ x, ∃ i, x ∈ B i)
    (hregular : ∀ i, B i = closure (interior (B i)))
    (hpair : Pairwise (fun i j ↦ Disjoint (interior (B i)) (interior (B j))))
    (havoid : ∀ i, ∀ x ∈ S, x ∉ frontier (B i)) :
    ∃! i, S ⊆ interior (B i) := by
  obtain ⟨x, hx⟩ := hSnon
  obtain ⟨i, hxi⟩ := hcover x
  have hxi' : x ∈ interior (B i) :=
    (mem_interior_iff_notMem_frontier hxi).mpr (havoid i x hx)
  have hsub : S ⊆ interior (B i) :=
    hS.subset_of_closure_inter_subset isOpen_interior ⟨x, hx, hxi'⟩ (by
      intro y hy
      have hyB : y ∈ B i := by
        rw [hregular i]
        exact hy.1
      exact (mem_interior_iff_notMem_frontier hyB).mpr (havoid i y hy.2))
  refine ⟨i, hsub, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (hpair hji) (hj hx) (hsub hx)

/-- The closed translated zero-index dyadic cell is the closed square about
its prescribed center. The product metric is the maximum metric.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–370, and the dyadic
fan in `prop:two-families`, lines 299–310. -/
theorem closure_centered_dyadicCell_eq_closedBall (c : ℝ × ℝ) (ℓ : ℕ) :
    let r := (2 : ℝ) ^ ℓ / 2
    closure (dyadicCell (c.1 - r, c.2 - r) ℓ (0, 0)) = Metric.closedBall c r := by
  dsimp only
  rw [closure_dyadicCell, ← closedBall_prod_same]
  simp only [Real.closedBall_eq_Icc, zero_add, Int.cast_zero, mul_zero, mul_one, add_zero]
  congr 2 <;> ring

/-- The existing late-layer bound supplies the exponent needed to make the
working half-side one thirty-second of the actual fine-cell side.
Auxiliary to Section 11, `prop:two-families`, lines 200–207, and
`geometry:initial-stars`, lines 352–370. -/
private theorem fine_working_radius_eq (k : ℕ) (hk : 50000000 ≤ k) :
    2 * ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2) =
      (2 : ℝ) ^ fineScaleIndex k / 32 := by
  have hfixed : 6 ≤ fineScaleIndex 50000000 := by
    unfold fineScaleIndex
    apply Nat.le_floor
    norm_num [Exponents.zeta, Exponents.geometryDelta]
  have hn : 5 ≤ fineScaleIndex k :=
    (by omega : 5 ≤ 6).trans (hfixed.trans (fineScaleIndex_mono hk))
  have hp := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) (Nat.sub_add_cancel hn)
  rw [pow_add] at hp
  norm_num at hp
  rw [← hp]
  ring

/-- The closed half-radius square in the initial-star construction has
half-side one hundred and twenty-eighth of the actual fine-cell side. The
existing late-layer bound supplies the exponent needed for natural subtraction.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 200–207, and
`geometry:initial-stars`, lines 333–370, especially 352–370, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem fineScaleIndex_closed_half_radius_eq (k : ℕ) (hk : 50000000 ≤ k) :
    ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2) / 2 =
      (2 : ℝ) ^ fineScaleIndex k / 128 := by
  have h := fine_working_radius_eq k hk
  linarith

/-- The eight actual open working triangles about a fine-cell mark have a
unique assignment to actual initial identifiers. Every initial birth region
in the smaller concentric closed square is precisely the union of its assigned
smaller triangles, including the empty union for an unassigned identifier.
The working and final half-sides are respectively one thirty-second and one
sixty-fourth of the reference fine-cell side. Source: Section 11,
`geometry:initial-stars`, lines 333–370, especially 352–370, and the actual
initial identifiers in `prop:two-families`, lines 299–323. -/
theorem exists_unique_initialRegion_sector_assignment
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let oLarge := (v.1 - 2 * r, v.2 - 2 * r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let I := InitialRegionIndex o k₀ Z C a b hC h₀
    ∃! σ : J → I,
      (∀ s : J,
        interior (cellFanPolygon oLarge (ℓ + 1) (0, 0)
          (fun _ ↦ true) s).region ⊆
          initialOpenRegion o k₀ Z C a b hC h₀ (σ s)) ∧
      ∀ i : I,
        initialBirthRegion o k₀ Z C a b hC h₀ i ∩ Metric.closedBall v r =
          ⋃ s : {s : J // σ s = i},
            (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s.val).region := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let oLarge := (v.1 - 2 * r, v.2 - 2 * r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let P : J → Set (ℝ × ℝ) := fun s ↦
    (cellFanPolygon oLarge (ℓ + 1) (0, 0) (fun _ ↦ true) s).region
  let Q : J → Set (ℝ × ℝ) := fun s ↦
    (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s).region
  let B : I → Set (ℝ × ℝ) := initialBirthRegion o k₀ Z C a b hC h₀
  let U : I → Set (ℝ × ℝ) := initialOpenRegion o k₀ Z C a b hC h₀
  let W := Metric.ball v (2 * r)
  let D := ⋃ s : J, interior (P s)
  change ∃! σ : J → I,
    (∀ s : J, interior (P s) ⊆ U (σ s)) ∧
      ∀ i : I, B i ∩ Metric.closedBall v r =
        ⋃ s : {s : J // σ s = i}, Q s.val
  have hr : 0 < r := div_pos (pow_pos zero_lt_two ℓ) (by norm_num)
  have hR : 0 < 2 * r := mul_pos zero_lt_two hr
  have hp : (2 : ℝ) ^ (ℓ + 1) / 2 = 2 * r := by
    dsimp [r]
    rw [pow_succ]
    ring
  have hcenter : cellFanCenter oLarge (ℓ + 1) (0, 0) = v := by
    apply Prod.ext <;> simp [oLarge, r, cellFanCenter, pow_succ] <;> ring
  have hcell : closure (dyadicCell oLarge (ℓ + 1) (0, 0)) =
      Metric.closedBall v (2 * r) := by
    have h := closure_centered_dyadicCell_eq_closedBall v (ℓ + 1)
    dsimp only at h
    rw [hp] at h
    exact h
  have hcoverP : (⋃ s : J, P s) = Metric.closedBall v (2 * r) :=
    (cellFanPolygons_cover oLarge (ℓ + 1) (0, 0) (fun _ ↦ true)).trans hcell
  have hPregular (s : J) : closure (interior (P s)) = P s :=
    (cellFanPolygon_interior_nonempty_and_closure_eq oLarge (ℓ + 1)
      (0, 0) (fun _ ↦ true) s).2
  have hD : closure D = Metric.closedBall v (2 * r) := by
    calc
      closure D = ⋃ s : J, closure (interior (P s)) := closure_iUnion_of_finite _
      _ = ⋃ s : J, P s := Set.iUnion_congr hPregular
      _ = Metric.closedBall v (2 * r) := hcoverP
  have hsectorBall (s : J) : interior (P s) ⊆ W := by
    have hsub : P s ⊆ Metric.closedBall v (2 * r) := by
      intro x hx
      rw [← hcoverP]
      exact Set.mem_iUnion.mpr ⟨s, hx⟩
    have h := interior_mono hsub
    rw [interior_closedBall v hR.ne'] at h
    exact h
  have hZ : Z.Nonempty := by
    have href := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
      (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
    have hvD := closure_mono href
      (beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k) z hv)
    obtain ⟨w, hw, _⟩ := dyadicLayer_exists_dist_le o k Z C v hvD
    exact ⟨w, hw⟩
  have hBcover : ∀ x, ∃ i : I, x ∈ B i := by
    intro x
    apply Set.mem_iUnion.mp
    rw [initialBirthRegions_cover o k₀ Z C a b hC h₀ hZ]
    trivial
  have hBregular (i : I) : B i = closure (U i) :=
    initialBirthRegion_eq_closure_initialOpenRegion o k₀ Z C a b hC h₀ i
  have hpair : Pairwise (fun i j : I ↦ Disjoint (U i) (U j)) :=
    initialOpenRegion_pairwise_disjoint o k₀ Z C a b hC h₀
  have hradius : 2 * r = (2 : ℝ) ^ fineScaleIndex k / 32 :=
    fine_working_radius_eq k (h₀.trans hk₀)
  have hassign (s : J) : ∃! i : I, interior (P s) ⊆ U i := by
    have hconv : Convex ℝ (P s) := by
      change Convex ℝ (convexHull ℝ {cellFanCenter oLarge (ℓ + 1) (0, 0),
        cellFanStart oLarge (ℓ + 1) (0, 0) (fun _ ↦ true) s,
        cellFanEnd oLarge (ℓ + 1) (0, 0) (fun _ ↦ true) s})
      exact convex_convexHull ℝ _
    refine preconnected_unique_interior B (interior (P s))
      (cellFanPolygon_interior_nonempty_and_closure_eq oLarge (ℓ + 1)
        (0, 0) (fun _ ↦ true) s).1
      hconv.interior.isPreconnected hBcover hBregular hpair ?_
    intro i x hx hfrontier
    have hnear : dist v x < (2 : ℝ) ^ fineScaleIndex k / 32 := by
      have h := Metric.mem_ball.mp (hsectorBall s hx)
      simpa only [dist_comm, hradius] using h
    have hallowed := initialBirthRegion_frontier_near_mark_allowed o k₀ Z C
      a b hC h₀ k z v x hk₀ hz hv i hfrontier hnear
    have hnot := cellFanPolygon_interior_not_isAllowedSlope_sub_center
      oLarge (ℓ + 1) (0, 0) s hx
    rw [hcenter] at hnot
    exact hnot hallowed
  let σ : J → I := fun s ↦ Classical.choose (hassign s)
  have hσ (s : J) : interior (P s) ⊆ U (σ s) :=
    (Classical.choose_spec (hassign s)).1
  refine ⟨σ, ⟨hσ, ?_⟩, ?_⟩
  · intro i
    let E := ⋃ s : {s : J // σ s = i}, P s.val
    have hE : IsClosed E := by
      apply isClosed_iUnion_of_finite
      intro s
      rw [← hPregular s.val]
      exact isClosed_closure
    have hUD : U i ∩ D ⊆ E := by
      rintro x ⟨hxU, hxD⟩
      obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxD
      have hsi : σ s = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hpair hne) (hσ s hxs) hxU
      exact Set.mem_iUnion.mpr ⟨⟨s, hsi⟩, interior_subset hxs⟩
    have hBE : B i ∩ W ⊆ E := by
      rw [hBregular i]
      exact closure_inter_subset_of_dense_inter (U i) D W E isOpen_interior
        Metric.isOpen_ball (by rw [hD]; exact Metric.ball_subset_closedBall) hE hUD
    have hEB : E ⊆ B i := by
      intro x hx
      obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
      have hs : interior (P s.val) ⊆ U i := by
        simpa only [s.property] using hσ s.val
      have h := closure_mono hs
      rw [hPregular s.val, ← hBregular i] at h
      exact h hxs
    have hsmall : Metric.closedBall v r ⊆ W :=
      Metric.closedBall_subset_ball (by linarith)
    calc
      B i ∩ Metric.closedBall v r = E ∩ Metric.closedBall v r := by
        ext x
        constructor
        · intro hx
          exact ⟨hBE ⟨hx.1, hsmall hx.2⟩, hx.2⟩
        · intro hx
          exact ⟨hEB hx.1, hx.2⟩
      _ = ⋃ s : {s : J // σ s = i}, P s.val ∩ Metric.closedBall v r :=
        Set.iUnion_inter _ _
      _ = ⋃ s : {s : J // σ s = i}, Q s.val := by
        apply Set.iUnion_congr
        intro s
        exact cellFanPolygon_succ_inter_closedBall v ℓ (fun _ ↦ true) s.val
  · intro τ hτ
    funext s
    exact (Classical.choose_spec (hassign s)).2 (τ s) (hτ.1 s)

/-- The canonical assignment of the eight working sectors about an actual
fine-cell mark to the initial region identifiers. It is characterized by
containment of each working open triangle in its assigned initial open region
and by the smaller closed-square decomposition.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 333–370, especially 352–370,
and `prop:two-families`, lines 299–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
noncomputable def initialSectorAssignment
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    CellFanSlot (fun _ : Fin 4 ↦ true) → InitialRegionIndex o k₀ Z C a b hC h₀ :=
  Classical.choose
    (exists_unique_initialRegion_sector_assignment
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv)

end InitialSectorAssignment

section InitialSectorColors

/-!
## Colors of adjacent actual sectors

Two neighboring triangles in the smaller concentric fan have the same actual
initial color exactly when their assigned initial identifiers agree. The
assignment is the unique one obtained from the actual initial regions. Their
closed decomposition places the common nondegenerate radial segment in both
birth regions, so distinct identifiers have opposite colors by the actual
initial-interface theorem.

The statement concerns actual endpoint adjacency. It makes no identification
of nonadjacent sectors with the same color or identifier.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 361–370, and `prop:two-families`, lines 313–323.
Source file: `build/sections/10-geometry.tex` in
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-- Actual neighboring fan triangles contain a common radial segment with
distinct endpoints. The distance of the perimeter endpoint from the center
is the positive fan radius. Auxiliary to Section 11, `prop:two-families`,
lines 308–323, and `geometry:initial-stars`, lines 352–370. -/
private theorem exists_shared_radial_segment (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split)
    (hadj : cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∨
      cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i) :
    ∃ e : ℝ × ℝ, cellFanCenter o ℓ z ≠ e ∧
      segment ℝ (cellFanCenter o ℓ z) e ⊆
        (cellFanPolygon o ℓ z split i).region ∩ (cellFanPolygon o ℓ z split j).region := by
  have ordered (i j : CellFanSlot split)
      (h : cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j) :
      cellFanCenter o ℓ z ≠ cellFanEnd o ℓ z split i ∧
        segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split i) ⊆
          (cellFanPolygon o ℓ z split i).region ∩
            (cellFanPolygon o ℓ z split j).region := by
    constructor
    · intro hce
      have hn := norm_sub_cellFanCenter_of_mem_base o ℓ z split i
        (right_mem_segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i))
      rw [← hce, sub_self, norm_zero] at hn
      have hr : 0 < (2 : ℝ) ^ ℓ / 2 := by positivity
      linarith
    · intro x hx
      constructor
      · change x ∈ convexHull ℝ {cellFanCenter o ℓ z, cellFanStart o ℓ z split i,
          cellFanEnd o ℓ z split i}
        exact segment_subset_convexHull (by simp) (by simp) hx
      · change x ∈ convexHull ℝ {cellFanCenter o ℓ z, cellFanStart o ℓ z split j,
          cellFanEnd o ℓ z split j}
        rw [h] at hx
        exact segment_subset_convexHull (by simp) (by simp) hx
  rcases hadj with h | h
  · exact ⟨cellFanEnd o ℓ z split i, (ordered i j h).1, (ordered i j h).2⟩
  · obtain ⟨hne, hsub⟩ := ordered j i h
    exact ⟨cellFanEnd o ℓ z split j, hne, fun x hx ↦ ⟨(hsub hx).2, (hsub hx).1⟩⟩

/-- On actual neighboring sectors, equality of initial colors is equivalent to
equality of their assigned initial identifiers. The unique assignment is
derived from the actual initial-region family. No identification of
nonadjacent sectors is asserted. Source: Section 11, `geometry:initial-stars`,
lines 333–370, especially 361–370, and `prop:two-families`, lines 313–323. -/
theorem initialRegion_sector_assignment_adjacent_colors_eq_iff
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let σ :=
      initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
    ∀ s t : J,
      (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∨
        cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) s) →
      (initialRegionColor o k₀ Z C a b hC h₀ (σ s) =
          initialRegionColor o k₀ Z C a b hC h₀ (σ t) ↔ σ s = σ t) := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  change ∀ s t : J,
    (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
        cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∨
      cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t =
        cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) s) →
    (initialRegionColor o k₀ Z C a b hC h₀ (σ s) =
        initialRegionColor o k₀ Z C a b hC h₀ (σ t) ↔ σ s = σ t)
  have hdecomp (i : I) :
      initialBirthRegion o k₀ Z C a b hC h₀ i ∩ Metric.closedBall v r =
        ⋃ s : {s : J // σ s = i},
          (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s.val).region :=
    (Classical.choose_spec
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1.2 i
  have hsub (s : J) : (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s).region ⊆
      initialBirthRegion o k₀ Z C a b hC h₀ (σ s) := by
    intro x hx
    have h : x ∈ initialBirthRegion o k₀ Z C a b hC h₀ (σ s) ∩
        Metric.closedBall v r := by
      rw [hdecomp (σ s)]
      exact Set.mem_iUnion.mpr ⟨⟨s, rfl⟩, hx⟩
    exact h.1
  intro s t hadj
  constructor
  · intro hcolor
    by_contra hne
    obtain ⟨e, hce, hradial⟩ := exists_shared_radial_segment
      oSmall ℓ (0, 0) (fun _ ↦ true) s t hadj
    have hcolors := initialRegionColor_ne_of_segment_subset_inter o k₀ Z C a b
      hC h₀ (σ s) (σ t) hne (cellFanCenter oSmall ℓ (0, 0)) e hce
      (fun x hx ↦ ⟨hsub s (hradial hx).1, hsub t (hradial hx).2⟩)
    exact hcolors hcolor
  · intro hsame
    rw [hsame]

end InitialSectorColors

end TNLean.PEPS.AreaLaw.Geometry

section InitialSectorCycle

/-!
## Evenness of actual initial-sector changes

The binary labels on a finite permutation change an even number of times.
For the eight sectors around an actual fine-cell mark, adjacent label changes
are precisely changes of the identifiers assigned by the initial regions.
The assignment is derived from those regions, and the count distinguishes
slots even when several disconnected runs carry the same identifier.

### References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 361–370,
and `prop:two-families`, lines 313–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped symmDiff

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Binary label changes under a finite permutation have even cardinality.
Auxiliary to Section 11, `geometry:initial-stars`, lines 361–370. -/
private theorem binaryPermutation_changes_even
    {J : Type*} [Fintype J] (τ : Equiv.Perm J) (c : J → Fin 2) :
    Even ((Finset.univ.filter (fun s ↦ c s ≠ c (τ s))).card) := by
  classical
  have hbinary : ∀ a b : Fin 2,
      a ≠ b ↔ (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0) := by decide
  let A : Finset J := Finset.univ.filter (fun s ↦ c s = 0)
  let B : Finset J := A.map τ.symm.toEmbedding
  have hmemB : ∀ s, s ∈ B ↔ c (τ s) = 0 := fun s ↦ by simp [B, A]
  have hchange :
      Finset.univ.filter (fun s ↦ c s ≠ c (τ s)) = A ∆ B := by
    ext s
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_symmDiff, A, hmemB] using hbinary (c s) (c (τ s))
  have hcard : A.card = B.card := by simp only [B, Finset.card_map]
  have hdiff : (A \ B).card = (B \ A).card :=
    (Finset.card_sdiff_eq_card_sdiff_iff (s := A) (t := B)).mpr hcard
  have hdis : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  refine ⟨(A \ B).card, ?_⟩
  rw [hchange, Finset.symmDiff_def,
    Finset.card_union_of_disjoint hdis, ← hdiff]

/-- The number of changes of the derived initial identifier around the eight
midpoint sectors is even. Source: Section 11, `geometry:initial-stars`,
lines 361–370, and `prop:two-families`, lines 313–323. -/
theorem initialRegion_sector_assignment_changes_even
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let σ := initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
    Even (Nat.card {s : J // σ s ≠ σ (cellFanNext s)}) := by
  classical
  dsimp only
  let σ := initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  have hchange (s : CellFanSlot (fun _ : Fin 4 ↦ true)) :
      σ s ≠ σ (cellFanNext s) ↔
        initialRegionColor o k₀ Z C a b hC h₀ (σ s) ≠
          initialRegionColor o k₀ Z C a b hC h₀ (σ (cellFanNext s)) :=
    not_congr (initialRegion_sector_assignment_adjacent_colors_eq_iff
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv s (cellFanNext s)
      (Or.inl (cellFanEnd_eq_cellFanStart_next _ _ _ s))).symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [← hchange] using
    binaryPermutation_changes_even cellFanNext
      (fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s))

end TNLean.PEPS.AreaLaw.Geometry

end InitialSectorCycle

section InitialSectorRuns

/-!
## Actual initial identifiers on local sector runs

The actual assignment of the eight local sectors descends to the connected
components of the existing equal-colored fan graph. The resulting function
is unique, and every actual birth region in the smaller closed square is
exactly the union of the run regions carrying its identifier. Separated runs
with the same identifier remain separate components.

If every neighboring pair has the same assigned identifier, the proved
connectivity of a constant-colored fan makes the assignment constant. The
working fan lies in the corresponding birth region. Its strict margin puts
the entire smaller closed square in one unique actual open region.

### References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 361–370, and `prop:two-families`, lines 313–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- An identifier preserved by graph edges is preserved by reachability.
The proof uses reflexive transitive closure, without a new walk induction.
Auxiliary to Section 11, `prop:two-families`, lines 313–323, and
`geometry:initial-stars`, lines 361–370. -/
private theorem identifier_eq_of_reachable {J I : Type*} (G : SimpleGraph J)
    (σ : J → I) (hedge : ∀ s t, G.Adj s t → σ s = σ t)
    {s t : J} (h : G.Reachable s t) : σ s = σ t := by
  have hg : Relation.ReflTransGen G.Adj s t :=
    (SimpleGraph.reachable_iff_reflTransGen s t).mp h
  have hi : Relation.ReflTransGen (fun i j : I ↦ i = j) (σ s) (σ t) :=
    Relation.ReflTransGen.lift σ hedge s t hg
  simpa only [Relation.reflTransGen_eq_self] using hi

/-- The actual sector assignment descends uniquely to the existing fan runs.
For every actual initial identifier, its birth region in the smaller closed
square is exactly the union of the run regions with that identifier. The
union includes every component bearing the identifier, without an
injectivity assertion. Source: Section 11, `geometry:initial-stars`,
lines 333–370, especially 361–370, and `prop:two-families`, lines 313–323. -/
theorem exists_unique_initialRegion_sector_run_assignment
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let I := InitialRegionIndex o k₀ Z C a b hC h₀
    let σ : J → I :=
      initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
    let family : J → Fin 2 := fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
    let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
    ∃! runLabel : G.ConnectedComponent → I,
      (∀ s : J, runLabel (G.connectedComponentMk s) = σ s) ∧
      ∀ i : I,
        initialBirthRegion o k₀ Z C a b hC h₀ i ∩ Metric.closedBall v r =
          ⋃ R : {R : G.ConnectedComponent // runLabel R = i},
            cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R.val := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  let family : J → Fin 2 := fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
  let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
  change ∃! runLabel : G.ConnectedComponent → I,
    (∀ s : J, runLabel (G.connectedComponentMk s) = σ s) ∧
    ∀ i : I,
      initialBirthRegion o k₀ Z C a b hC h₀ i ∩ Metric.closedBall v r =
        ⋃ R : {R : G.ConnectedComponent // runLabel R = i},
          cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R.val
  have hedge (s t : J) (h : G.Adj s t) : σ s = σ t :=
    (initialRegion_sector_assignment_adjacent_colors_eq_iff
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv s t h.2.1).mp h.2.2
  have hpath (s t : J) (p : G.Walk s t) (_ : p.IsPath) : σ s = σ t :=
    identifier_eq_of_reachable G σ hedge p.reachable
  let runLabel : G.ConnectedComponent → I := SimpleGraph.ConnectedComponent.lift σ hpath
  have hRunLabel (s : J) : runLabel (G.connectedComponentMk s) = σ s := rfl
  have hdecomp (i : I) :
      initialBirthRegion o k₀ Z C a b hC h₀ i ∩ Metric.closedBall v r =
        ⋃ s : {s : J // σ s = i},
          (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s.val).region :=
    (Classical.choose_spec
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1.2 i
  refine ⟨runLabel, ⟨hRunLabel, ?_⟩, ?_⟩
  · intro i
    apply Set.Subset.antisymm
    · intro x hx
      rw [hdecomp i] at hx
      obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
      have hRi : runLabel (G.connectedComponentMk s.val) = i :=
        (hRunLabel s.val).trans s.property
      refine Set.mem_iUnion.mpr ⟨⟨G.connectedComponentMk s.val, hRi⟩, ?_⟩
      change x ∈ ⋃ t ∈ (G.connectedComponentMk s.val).supp,
        (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) t).region
      refine Set.mem_iUnion.mpr ⟨s.val, Set.mem_iUnion.mpr ⟨?_, hxs⟩⟩
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · intro x hx
      obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp hx
      change x ∈ ⋃ s ∈ R.val.supp,
        (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s).region at hxR
      obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxR
      obtain ⟨hsR, hxs⟩ := Set.mem_iUnion.mp hxs
      have hMk : G.connectedComponentMk s = R.val :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hsR
      have hsi : σ s = i := (hRunLabel s).symm.trans
        ((congrArg runLabel hMk).trans R.property)
      rw [hdecomp i]
      exact Set.mem_iUnion.mpr ⟨⟨s, hsi⟩, hxs⟩
  · intro μ hμ
    funext R
    obtain ⟨s, rfl⟩ := R.exists_rep
    exact (hμ.1 s).trans (hRunLabel s).symm

/-- If every actual neighboring sector has the same assigned identifier,
the smaller closed square lies in one unique actual initial open region.
The working square supplies the strict margin needed at the smaller square's
boundary. Source: Section 11, `geometry:initial-stars`, lines 333–370,
especially 361–370, and `prop:two-families`, lines 313–323. -/
theorem exists_unique_initialRegion_of_no_active_sector
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let I := InitialRegionIndex o k₀ Z C a b hC h₀
    let σ : J → I :=
      initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
    (∀ s t : J,
      (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∨
        cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) s) → σ s = σ t) →
      ∃! i : I, Metric.closedBall v r ⊆ initialOpenRegion o k₀ Z C a b hC h₀ i := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let oLarge := (v.1 - 2 * r, v.2 - 2 * r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  let family : J → Fin 2 := fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
  let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
  let G₀ := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) (fun _ ↦ (0 : Fin 2))
  let P : J → Set (ℝ × ℝ) := fun s ↦
    (cellFanPolygon oLarge (ℓ + 1) (0, 0) (fun _ ↦ true) s).region
  let B : I → Set (ℝ × ℝ) := initialBirthRegion o k₀ Z C a b hC h₀
  let U : I → Set (ℝ × ℝ) := initialOpenRegion o k₀ Z C a b hC h₀
  change (∀ s t : J,
    (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
        cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∨
      cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t =
        cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) s) → σ s = σ t) →
    ∃! i : I, Metric.closedBall v r ⊆ U i
  intro hno
  have hle : G₀ ≤ G := by
    intro s t h
    refine ⟨h.1, h.2.1, ?_⟩
    change initialRegionColor o k₀ Z C a b hC h₀ (σ s) =
      initialRegionColor o k₀ Z C a b hC h₀ (σ t)
    rw [hno s t h.2.1]
  have hconstant := (cellFanRun_all_equal oSmall ℓ (0, 0) (fun _ ↦ true)
    (fun _ ↦ (0 : Fin 2)) (fun _ _ ↦ rfl)).1
  have hconnected (s t : J) : G.connectedComponentMk s = G.connectedComponentMk t :=
    SimpleGraph.ConnectedComponent.sound
      ((SimpleGraph.ConnectedComponent.exact (hconstant s t)).mono hle)
  obtain ⟨runLabel, hRunLabel, _⟩ :=
    (exists_unique_initialRegion_sector_run_assignment
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv).exists
  let s₀ : J := ⟨0, 0⟩
  let i₀ : I := σ s₀
  have hσ (s : J) : σ s = i₀ :=
    (hRunLabel s).symm.trans ((congrArg runLabel (hconnected s s₀)).trans (hRunLabel s₀))
  have hworking (s : J) : interior (P s) ⊆ U (σ s) :=
    (Classical.choose_spec
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1.1 s
  have hregular (s : J) : closure (interior (P s)) = P s :=
    (cellFanPolygon_interior_nonempty_and_closure_eq
      oLarge (ℓ + 1) (0, 0) (fun _ ↦ true) s).2
  have hBregular : B i₀ = closure (U i₀) :=
    initialBirthRegion_eq_closure_initialOpenRegion o k₀ Z C a b hC h₀ i₀
  have hPB (s : J) : P s ⊆ B i₀ := by
    have hs : interior (P s) ⊆ U i₀ := by
      simpa only [hσ s] using hworking s
    have h := closure_mono hs
    rw [hregular s, ← hBregular] at h
    exact h
  have hr : 0 < r := div_pos (pow_pos zero_lt_two ℓ) (by norm_num)
  have hR : 0 < 2 * r := mul_pos zero_lt_two hr
  have hp : (2 : ℝ) ^ (ℓ + 1) / 2 = 2 * r := by
    dsimp [r]
    rw [pow_succ]
    ring
  have hcell := closure_centered_dyadicCell_eq_closedBall v (ℓ + 1)
  dsimp only at hcell
  rw [hp] at hcell
  have hcover : (⋃ s : J, P s) = Metric.closedBall v (2 * r) :=
    (cellFanPolygons_cover oLarge (ℓ + 1) (0, 0) (fun _ ↦ true)).trans hcell
  have hballB : Metric.closedBall v (2 * r) ⊆ B i₀ := by
    rw [← hcover]
    exact Set.iUnion_subset hPB
  have hballU : Metric.ball v (2 * r) ⊆ U i₀ := by
    have h := interior_mono hballB
    change interior (Metric.closedBall v (2 * r)) ⊆ U i₀ at h
    rw [interior_closedBall v hR.ne'] at h
    exact h
  have hsmall : Metric.closedBall v r ⊆ Metric.ball v (2 * r) :=
    Metric.closedBall_subset_ball (by linarith)
  have hcontain : Metric.closedBall v r ⊆ U i₀ := hsmall.trans hballU
  refine ⟨i₀, hcontain, ?_⟩
  intro j hj
  by_contra hji
  have hvball : v ∈ Metric.closedBall v r := Metric.mem_closedBall_self hr.le
  exact Set.disjoint_left.mp
    (initialOpenRegion_pairwise_disjoint o k₀ Z C a b hC h₀ hji)
    (hj hvball) (hcontain hvball)

end TNLean.PEPS.AreaLaw.Geometry

end InitialSectorRuns
