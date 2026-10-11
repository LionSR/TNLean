/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialStarFrontiers
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionRegularity
import TNLean.PEPS.AreaLaw.Geometry.CellFanSectors
import TNLean.PEPS.AreaLaw.Geometry.ConcentricFans
import TNLean.PEPS.AreaLaw.Geometry.AdjacentScales
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.RCLike.Real

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

namespace TNLean.PEPS.AreaLaw.Geometry

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

end TNLean.PEPS.AreaLaw.Geometry
