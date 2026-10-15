/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.IsolatedStars
import TNLean.PEPS.AreaLaw.Geometry.InitialActiveRays
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorColors
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorRuns

/-!
# Isolated stars of the initial mesh

Every mark of an actual fine-layer cell has an isolated star in the actual
initial regions, in the closed square of half-side one hundred and
twenty-eighth of the side of that cell. The belt residues of all layers are
arbitrary. The eight triangles of this square receive the identifiers of the
actual initial regions containing them. The frontiers in the square are the
directed rays at changes of identifier, successive triangles carry opposite
labels exactly at such changes, and without a change the square lies in one
region.

For the deduplicated marks of selected belt cells, with any positive scale
realized by an incident selected cell, in particular the least incident
scale, the constant `a₀ = 1/128` gives both assertions of the initial-star
lemma: distinct marks are separated by `a₀` times the larger scale, and each
mark of scale `S` has an isolated star of half-side `a₀ S`. The jointly chosen
initial repair stage therefore has isolated stars with this constant.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 332–370,
with the deduplicated marks and least incident scales in lines 325–330.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Scaling the second vector by a positive factor does not change whether two
vectors lie on the same ray.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–343. -/
private theorem sameRay_pos_smul_right_iff' {x y : ℝ × ℝ} {r : ℝ} (hr : 0 < r) :
    SameRay ℝ x (r • y) ↔ SameRay ℝ x y := by
  constructor
  · intro h
    have h' := h.pos_smul_right (inv_pos.mpr hr)
    rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h'
  · exact fun h ↦ h.pos_smul_right hr

/-- The actual closed fan triangle about a mark is the wedge of the normalized
fan scaled about that mark.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
private theorem cellFanPolygon_region_eq_repairCurrentFanTriangle (v : ℝ × ℝ)
    (ℓ : ℕ) (s : CellFanSlot (fun _ : Fin 4 ↦ true)) :
    (cellFanPolygon (v.1 - (2 : ℝ) ^ ℓ / 2, v.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0)
        (fun _ ↦ true) s).region =
      repairCurrentFanTriangle v ((2 : ℝ) ^ ℓ / 2) s := by
  rw [cellFanPolygon_region_eq_image]
  rfl

/-- The final fan endpoint about a mark is the mark plus the fan half-side
times the normalized wedge direction.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–343. -/
private theorem cellFanEnd_sub_eq_smul_repairFanDirection (v : ℝ × ℝ) (ℓ : ℕ)
    (s : CellFanSlot (fun _ : Fin 4 ↦ true)) :
    cellFanEnd (v.1 - (2 : ℝ) ^ ℓ / 2, v.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0)
        (fun _ ↦ true) s - v =
      ((2 : ℝ) ^ ℓ / 2) • repairFanDirection s := by
  show _ = _ • cellFanEnd (-1, -1) 1 (0, 0) (fun _ ↦ true) s
  rw [cellFanEnd_eq, cellFanEnd_eq]
  ext <;> simp [cellFanCenter]

/-- The actual initial regions have an isolated star at every mark of an actual
fine-layer cell, in the closed square whose half-side is one hundred and
twenty-eighth of the side of that cell. The belt residues are arbitrary.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–370. -/
theorem initialRegion_isIsolatedStar
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    IsIsolatedStar (initialOpenRegion o k₀ Z C a b hC h₀)
      (initialRegionColor o k₀ Z C a b hC h₀) v
      ((2 : ℝ) ^ fineScaleIndex k / 128) := by
  classical
  rw [← fineScaleIndex_closed_half_radius_eq k (h₀.trans hk₀)]
  have hr : (0 : ℝ) < (2 : ℝ) ^ (fineScaleIndex k - 5) / 2 := by positivity
  have hρ : (0 : ℝ) < (2 : ℝ) ^ (fineScaleIndex k - 5) / 2 / 2 := by positivity
  have hρr : (2 : ℝ) ^ (fineScaleIndex k - 5) / 2 / 2 ≤
      (2 : ℝ) ^ (fineScaleIndex k - 5) / 2 := by linarith
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let B : I → Set (ℝ × ℝ) := initialBirthRegion o k₀ Z C a b hC h₀
  let U : I → Set (ℝ × ℝ) := initialOpenRegion o k₀ Z C a b hC h₀
  let σ : RepairFanSlot → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  have hspec := (Classical.choose_spec
    (exists_unique_initialRegion_sector_assignment
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1
  dsimp only at hspec
  have hP (s : CellFanSlot (fun _ : Fin 4 ↦ true)) :
      repairCurrentFanTriangle v ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2 / 2) s ⊆
        (cellFanPolygon (v.1 - 2 * ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2),
          v.2 - 2 * ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2))
          (fineScaleIndex k - 5 + 1) (0, 0) (fun _ ↦ true) s).region := by
    rw [← repairCurrentFanTriangle_inter_closedBall v hρ hρr s,
      ← cellFanPolygon_region_eq_repairCurrentFanTriangle v (fineScaleIndex k - 5) s]
    have h := cellFanPolygon_succ_inter_closedBall v (fineScaleIndex k - 5)
      (fun _ ↦ true) s
    dsimp only at h
    rw [← h]
    exact Set.inter_subset_left.trans Set.inter_subset_left
  have hBU (i : I) : B i = closure (U i) :=
    initialBirthRegion_eq_closure_initialOpenRegion o k₀ Z C a b hC h₀ i
  have hBclosed (i : I) : IsClosed (B i) := by
    rw [hBU i]
    exact isClosed_closure
  have hfrontier (i : I) : frontier (U i) = frontier (B i) := by
    change frontier (interior (B i)) = frontier (B i)
    have h := hBU i
    change B i = closure (interior (B i)) at h
    rw [frontier, frontier, interior_interior, ← h, (hBclosed i).closure_eq]
  refine ⟨σ, fun s ↦ (interior_mono (hP s)).trans (hspec.1 s), fun i ↦ ?_,
    fun x hx ↦ ?_, fun s ↦ ?_, fun hn ↦ ?_⟩
  · change closure (U i) ∩ _ = _
    rw [← hBU i, ← Set.inter_eq_right.mpr (Metric.closedBall_subset_closedBall hρr),
      ← Set.inter_assoc, hspec.2 i, Set.iUnion_inter]
    refine Set.iUnion_congr fun s ↦ ?_
    rw [cellFanPolygon_region_eq_repairCurrentFanTriangle v (fineScaleIndex k - 5) s.val]
    exact repairCurrentFanTriangle_inter_closedBall v hρ hρr s.val
  · have h := initialRegion_frontier_small_closedBall_iff_active_ray
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv x hx
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨s, hs, hray⟩ := h.mp ⟨i, (hfrontier i) ▸ hi⟩
      refine ⟨s, hs, (sameRay_pos_smul_right_iff' hr).mp ?_⟩
      rw [cellFanEnd_sub_eq_smul_repairFanDirection v (fineScaleIndex k - 5) s] at hray
      exact hray
    · rintro ⟨s, hs, hray⟩
      have hray' := (sameRay_pos_smul_right_iff' hr).mpr hray
      rw [← cellFanEnd_sub_eq_smul_repairFanDirection v (fineScaleIndex k - 5) s] at hray'
      obtain ⟨i, hi⟩ := h.mpr ⟨s, hs, hray'⟩
      exact ⟨i, (hfrontier i).symm ▸ hi⟩
  · exact initialRegion_sector_assignment_adjacent_colors_eq_iff
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv s (cellFanNext s)
      (Or.inl ((cellFanEnd_eq_cellFanStart_iff _ _ _ s (cellFanNext s)).mpr rfl))
  · have hadj (s t : CellFanSlot (fun _ : Fin 4 ↦ true))
        (_ : cellFanEnd (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
              v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
              (fun _ ↦ true) s =
            cellFanStart (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
              v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
              (fun _ ↦ true) t ∨
          cellFanEnd (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
              v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
              (fun _ ↦ true) t =
            cellFanStart (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
              v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2) (fineScaleIndex k - 5) (0, 0)
              (fun _ ↦ true) s) :
        σ s = σ t := by
      rename_i h
      rcases h with h | h
      · rw [(cellFanEnd_eq_cellFanStart_iff _ _ _ s t).mp h]
        exact hn s
      · rw [(cellFanEnd_eq_cellFanStart_iff _ _ _ t s).mp h]
        exact (hn t).symm
    obtain ⟨i, hi, -⟩ := exists_unique_initialRegion_of_no_active_sector
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv hadj
    exact ⟨i, (Metric.closedBall_subset_closedBall hρr).trans hi⟩

/-- **Isolated stars of the initial mesh**, for arbitrary belt residues. Let
`M` be the set of deduplicated marks of the selected belt cells of all layers
from `k₀` on, and give each mark a positive scale realized by an incident
selected cell, such as its least incident side. With `a₀ = 1/128`, distinct
marks satisfy `‖v - w‖_∞ ≥ a₀ max(S_v, S_w)`, and each mark `v` has an
isolated star of half-side `a₀ S_v` in the actual initial regions.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–370. -/
theorem initialMarks_isolatedStars
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (M : Set (ℝ × ℝ)) (S : M → ℝ)
    (hS : ∀ v, 0 < S v ∧ ∃ k z, k₀ ≤ k ∧
      z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
        (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k) ∧
      v.val ∈ beltCellMarks o (fineScaleIndex k) z ∧
      S v = (2 : ℝ) ^ fineScaleIndex k) :
    (∀ v w : M, v ≠ w → 1 / 128 * max (S v) (S w) ≤ dist v.val w.val) ∧
      ∀ v : M, IsIsolatedStar (initialOpenRegion o k₀ Z C a b hC h₀)
        (initialRegionColor o k₀ Z C a b hC h₀) v.val (1 / 128 * S v) := by
  constructor
  · intro v w hvw
    obtain ⟨hv₀, k, z, hk, hz, hv, hSv⟩ := hS v
    obtain ⟨-, h, t, hh, ht, hw, hSw⟩ := hS w
    have hsep := fineLayer_marks_dist_ge o k h Z C z t v.val w.val hC
      (h₀.trans hk) (h₀.trans hh) (Finset.mem_filter.mp hz).1
      (Finset.mem_filter.mp ht).1 hv hw (fun he ↦ hvw (Subtype.ext he))
    rw [← hSv, ← hSw] at hsep
    have hmax : 0 ≤ max (S v) (S w) := hv₀.le.trans (le_max_left _ _)
    linarith
  · intro v
    obtain ⟨-, k, z, hk, hz, hv, hSv⟩ := hS v
    have h := initialRegion_isIsolatedStar o k₀ Z C a b hC h₀ k z v.val hk
      (Finset.mem_filter.mp hz).1 hv
    rwa [hSv, show (1 / 128 : ℝ) * (2 : ℝ) ^ fineScaleIndex k =
      (2 : ℝ) ^ fineScaleIndex k / 128 by ring]

/-- The jointly chosen initial repair stage has isolated stars with constant
`1/128`, for every domain, cut, origin, width factor and admissible lower
scale. Source: area-law Section 11, `geometry:initial-stars`, lines 325–370. -/
theorem initialRepairStage_hasIsolatedStars (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    (initialRepairStage o Λ A C k₀ hC h₀).HasIsolatedStars (1 / 128) := by
  let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
    o Λ A C k₀ hC h₀
  let hb := Classical.choose_spec h
  let hab := Classical.choose_spec hb
  let hM := hab.2.2
  let hS := (Classical.choose_spec hM).2.2
  exact initialMarks_isolatedStars o k₀ (boundaryEndpoints Λ A) C
    (Classical.choose h) (Classical.choose hb) hC h₀
    ((Classical.choose hM : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) (Classical.choose hS)
    (Classical.choose_spec hS).1

/-- **Isolated stars of the initial mesh.** The constant `a₀ = 1/128` works
for every width factor, domain, cut, origin and admissible lower scale.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–349. -/
theorem initialIsolatedStarsStatement_holds : InitialIsolatedStarsStatement :=
  ⟨1 / 128, by norm_num, fun C ↦ ⟨0, fun o Λ A k₀ hC h₀ _ ↦
    initialRepairStage_hasIsolatedStars o Λ A C k₀ hC h₀⟩⟩

end TNLean.PEPS.AreaLaw.Geometry
