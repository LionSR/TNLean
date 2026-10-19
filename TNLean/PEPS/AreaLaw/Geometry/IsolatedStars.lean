/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStage
import TNLean.PEPS.AreaLaw.Geometry.CellFanCycle
import Mathlib.Analysis.Convex.Combination

/-!
# Isolated radial stars

A family of open regions with binary labels has an isolated star in the
closed square of half-side ρ about v when the eight elementary triangles of
that square can be assigned identifiers with the following properties. Each
open triangle lies in its assigned region. The closure of every region meets
the square exactly in the union of its assigned triangles. The union of the
region frontiers in the square is exactly the union of the directed rays from
v, in the eight axis and diagonal directions, at which the assigned
identifier changes to its successor. Successive triangles have equal labels
exactly when they have equal identifiers. When no identifier changes, the
whole square lies in one region.

A sector between consecutive active rays is a run of triangles carrying one
identifier, so it lies in one tile; a seam inside such a run is not on any
frontier. A repair stage has isolated stars with constant a₀ when its mark
occurrences are separated by a₀ times the larger scale and each occurrence
of scale S has an isolated star of half-side a₀S in the current regions.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 332–349,
and `geometry:repair-induction`, lines 471–485.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The direction of the radial edge ending an elementary wedge: the final
perimeter endpoint of the wedge in the normalized square `[-1, 1]²`. These are
the eight axis and diagonal directions.
Source: area-law Section 11, `geometry:initial-stars`, lines 340–343. -/
def repairFanDirection (s : RepairFanSlot) : ℝ × ℝ :=
  cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit s

/-- The normalized wedge directions are the nonzero vectors with coordinates
in `{-1, 0, 1}`, that is, the eight axis and diagonal directions.
Source: area-law Section 11, `geometry:initial-stars`, lines 340–343. -/
theorem repairFanDirection_mem (s : RepairFanSlot) :
    repairFanDirection s ≠ 0 ∧
      (repairFanDirection s).1 ∈ ({-1, 0, 1} : Set ℝ) ∧
      (repairFanDirection s).2 ∈ ({-1, 0, 1} : Set ℝ) := by
  rcases s with ⟨side, j⟩
  have hj : j.val = 0 ∨ j.val = 1 := by
    have := j.isLt
    simp only [repairFanSplit, ite_true] at this
    omega
  rw [repairFanDirection, cellFanEnd_eq]
  simp only [repairFanSplit, ite_true]
  rcases hj with hj | hj <;> rw [hj] <;> fin_cases side <;>
    simp [cellFanCenter, cellFanSideVector, Prod.ext_iff]

/-- The closed square of half-side `ρ` about `v` is an isolated star of the
labelled region family `R`, `ξ`. The assignment `σ` gives the identifier of
each of the eight elementary triangles; its changes to the perimeter successor
are the active rays.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–349. -/
def IsIsolatedStar {ι : Type*} (R : ι → Set (ℝ × ℝ)) (ξ : ι → Fin 2)
    (v : ℝ × ℝ) (ρ : ℝ) : Prop :=
  ∃ σ : RepairFanSlot → ι,
    (∀ s, interior (repairCurrentFanTriangle v ρ s) ⊆ R (σ s)) ∧
    (∀ i, closure (R i) ∩ Metric.closedBall v ρ =
      ⋃ s : {s : RepairFanSlot // σ s = i}, repairCurrentFanTriangle v ρ s.val) ∧
    (∀ x ∈ Metric.closedBall v ρ, (∃ i, x ∈ frontier (R i)) ↔
      ∃ s, σ s ≠ σ (cellFanNext s) ∧ SameRay ℝ (x - v) (repairFanDirection s)) ∧
    (∀ s, ξ (σ s) = ξ (σ (cellFanNext s)) ↔ σ s = σ (cellFanNext s)) ∧
    ((∀ s, σ s = σ (cellFanNext s)) → ∃ i, Metric.closedBall v ρ ⊆ R i)

/-- A repair stage has isolated stars with constant `a₀`: distinct mark
occurrences are separated by `a₀` times the larger scale, and each occurrence
of scale `S` has an isolated star of half-side `a₀ S` in the current regions.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–349, and
`geometry:repair-induction`, lines 471–485. -/
def RepairStage.HasIsolatedStars (D : RepairStage) (a₀ : ℝ) : Prop :=
  (∀ p q, p ≠ q →
    a₀ * max (D.scale p) (D.scale q) ≤ dist (D.location p) (D.location q)) ∧
  ∀ p, IsIsolatedStar D.current D.color (D.location p) (a₀ * D.scale p)

/-- The closed triangle of a centered dyadic fan is the scaled image of the
corresponding normalized triangle.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
theorem cellFanPolygon_region_eq_image (c : ℝ × ℝ) (ℓ : ℕ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) :
    (cellFanPolygon (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0)
        split s).region =
      (fun x : ℝ × ℝ ↦ c + ((2 : ℝ) ^ ℓ / 2) • x) ''
        (cellFanPolygon (-1, -1) 1 (0, 0) split s).region := by
  set r : ℝ := (2 : ℝ) ^ ℓ / 2
  let f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x ↦ c + r • x
      linear := r • LinearMap.id
      map_vadd' := by
        intro p w
        simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_add]
        abel }
  have hf : (fun x : ℝ × ℝ ↦ c + r • x) = f := rfl
  have hreg (o : ℝ × ℝ) (m : ℕ) : (cellFanPolygon o m (0, 0) split s).region =
      convexHull ℝ {cellFanCenter o m (0, 0), cellFanStart o m (0, 0) split s,
        cellFanEnd o m (0, 0) split s} := rfl
  rw [hreg, hreg, hf, f.image_convexHull]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]
  have hc : f (cellFanCenter (-1, -1) 1 (0, 0)) =
      cellFanCenter (c.1 - r, c.2 - r) ℓ (0, 0) := by
    change c + r • _ = _
    ext <;> simp [cellFanCenter, r]
  have hs : f (cellFanStart (-1, -1) 1 (0, 0) split s) =
      cellFanStart (c.1 - r, c.2 - r) ℓ (0, 0) split s := by
    change c + r • _ = _
    rw [cellFanStart_eq, cellFanStart_eq]
    ext <;> simp [cellFanCenter, r]
  have he : f (cellFanEnd (-1, -1) 1 (0, 0) split s) =
      cellFanEnd (c.1 - r, c.2 - r) ℓ (0, 0) split s := by
    change c + r • _ = _
    rw [cellFanEnd_eq, cellFanEnd_eq]
    ext <;> simp [cellFanCenter, r]
  rw [hc, hs, he]

/-- The normalized center of the eight-triangle fan is the origin.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
private theorem normalized_center : cellFanCenter (-1, -1) 1 (0, 0) = 0 := by
  ext <;> simp [cellFanCenter]

/-- A point of a normalized closed wedge is a nonnegative multiple, of factor at
most one, of a point of its outer side, and that side lies on the unit sphere.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
private theorem mem_normalized_wedge_iff (s : RepairFanSlot) (x : ℝ × ℝ) :
    x ∈ (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s).region ↔
      ∃ y ∈ segment ℝ (cellFanStart (-1, -1) 1 (0, 0) repairFanSplit s)
          (cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit s),
        ∃ u ∈ Set.Icc (0 : ℝ) 1, x = u • y := by
  have hreg : (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s).region =
      convexHull ℝ {cellFanCenter (-1, -1) 1 (0, 0),
        cellFanStart (-1, -1) 1 (0, 0) repairFanSplit s,
        cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit s} := rfl
  rw [hreg, normalized_center, ← convexJoin_singleton_segment, mem_convexJoin]
  constructor
  · rintro ⟨c, hc, y, hy, hx⟩
    rw [Set.mem_singleton_iff.mp hc, segment_eq_image] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨y, hy, u, hu, by simp⟩
  · rintro ⟨y, hy, u, hu, rfl⟩
    refine ⟨0, rfl, y, hy, ?_⟩
    rw [segment_eq_image]
    exact ⟨u, hu, by simp⟩

/-- Points of the outer side of a normalized wedge have norm one.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
private theorem norm_of_mem_normalized_base (s : RepairFanSlot) {y : ℝ × ℝ}
    (hy : y ∈ segment ℝ (cellFanStart (-1, -1) 1 (0, 0) repairFanSplit s)
      (cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit s)) : ‖y‖ = 1 := by
  have h := norm_sub_cellFanCenter_of_mem_base (-1, -1) 1 (0, 0) repairFanSplit s hy
  rw [normalized_center, sub_zero] at h
  rw [h]
  norm_num

/-- Clipping a wedge of half-side `ρ` by the closed square of a smaller
positive half-side `ρ'` gives the corresponding wedge of half-side `ρ'`.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
theorem repairCurrentFanTriangle_inter_closedBall (v : ℝ × ℝ) {ρ ρ' : ℝ}
    (hρ' : 0 < ρ') (hρ : ρ' ≤ ρ) (s : RepairFanSlot) :
    repairCurrentFanTriangle v ρ s ∩ Metric.closedBall v ρ' =
      repairCurrentFanTriangle v ρ' s := by
  have hρpos : 0 < ρ := hρ'.trans_le hρ
  ext x
  simp only [repairCurrentFanTriangle, Set.mem_inter_iff, Set.mem_image,
    mem_normalized_wedge_iff, Metric.mem_closedBall]
  constructor
  · rintro ⟨⟨t, ⟨y, hy, u, hu, rfl⟩, rfl⟩, hd⟩
    have hny := norm_of_mem_normalized_base s hy
    have hd' : ρ * u ≤ ρ' := by
      rw [dist_eq_norm, add_sub_cancel_left, smul_smul, norm_smul, hny, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρpos.le hu.1)] at hd
      exact hd
    refine ⟨(ρ * u / ρ') • y, ⟨y, hy, ρ * u / ρ',
      ⟨div_nonneg (mul_nonneg hρpos.le hu.1) hρ'.le, ?_⟩, rfl⟩, ?_⟩
    · exact (div_le_one hρ').mpr hd'
    · rw [smul_smul, smul_smul, mul_div_cancel₀ _ hρ'.ne']
  · rintro ⟨t, ⟨y, hy, u, hu, rfl⟩, rfl⟩
    have hny := norm_of_mem_normalized_base s hy
    refine ⟨⟨(ρ' * u / ρ) • y, ⟨y, hy, ρ' * u / ρ,
      ⟨div_nonneg (mul_nonneg hρ'.le hu.1) hρpos.le, ?_⟩, rfl⟩, ?_⟩, ?_⟩
    · rw [div_le_one hρpos]
      nlinarith [hu.1, hu.2]
    · rw [smul_smul, smul_smul, mul_div_cancel₀ _ hρpos.ne']
    · rw [dist_eq_norm, add_sub_cancel_left, smul_smul, norm_smul, hny, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρ'.le hu.1)]
      nlinarith [hu.1, hu.2]

/-- An isolated star remains an isolated star after shrinking its half-side.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 332–349, and
`geometry:repair-induction`, lines 471–494. -/
theorem IsIsolatedStar.mono {ι : Type*} {R : ι → Set (ℝ × ℝ)} {ξ : ι → Fin 2}
    {v : ℝ × ℝ} {ρ ρ' : ℝ} (h : IsIsolatedStar R ξ v ρ) (hρ' : 0 < ρ')
    (hρ : ρ' ≤ ρ) : IsIsolatedStar R ξ v ρ' := by
  obtain ⟨σ, hsub, hdecomp, hfront, hcolor, hnone⟩ := h
  have hball : Metric.closedBall v ρ' ⊆ Metric.closedBall v ρ :=
    Metric.closedBall_subset_closedBall hρ
  have htri (s : RepairFanSlot) :
      repairCurrentFanTriangle v ρ' s ⊆ repairCurrentFanTriangle v ρ s := by
    rw [← repairCurrentFanTriangle_inter_closedBall v hρ' hρ s]
    exact Set.inter_subset_left
  refine ⟨σ, fun s ↦ (interior_mono (htri s)).trans (hsub s), fun i ↦ ?_,
    fun x hx ↦ hfront x (hball hx), hcolor, fun hn ↦ ?_⟩
  · rw [← Set.inter_eq_right.mpr hball, ← Set.inter_assoc, hdecomp i,
      Set.iUnion_inter]
    exact Set.iUnion_congr fun s ↦
      repairCurrentFanTriangle_inter_closedBall v hρ' hρ s.val
  · obtain ⟨i, hi⟩ := hnone hn
    exact ⟨i, hball.trans hi⟩

/-- Isolated stars persist for a smaller positive constant, provided that every
mark scale is positive.
Auxiliary to area-law Section 11, `geometry:initial-stars`, lines 332–349, and
`geometry:repair-induction`, lines 471–494. -/
theorem RepairStage.HasIsolatedStars.mono {D : RepairStage} {a₀ a₀' : ℝ}
    (h : D.HasIsolatedStars a₀) (hpos : ∀ p, 0 < D.scale p) (ha₀' : 0 < a₀')
    (ha₀ : a₀' ≤ a₀) : D.HasIsolatedStars a₀' := by
  refine ⟨fun p q hpq ↦ ?_, fun p ↦ (h.2 p).mono (mul_pos ha₀' (hpos p))
    (mul_le_mul_of_nonneg_right ha₀ (hpos p).le)⟩
  have hmax : 0 ≤ max (D.scale p) (D.scale q) := (hpos p).le.trans (le_max_left _ _)
  exact (mul_le_mul_of_nonneg_right ha₀ hmax).trans (h.1 p q hpq)

/-- The conclusion of the initial-star lemma for the actual initial stage: one
positive constant `a₀`, independent of the domain, cut, origin and layer, such
that for each width factor `C` the initial stage has isolated stars with
constant `a₀` for every sufficiently large lower scale `k₀`.

This is the specialization of the source lemma to the belt residues chosen
jointly in `initialRepairStage`, in the form used by the repair induction. The
source lemma quantifies over all admissible residues; its statement for
arbitrary residues is proved separately for the initial mark family.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–349. -/
def InitialIsolatedStarsStatement : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ C : ℕ, ∃ K : ℕ, ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
      (initialRepairStage o Λ A C k₀ hC h₀).HasIsolatedStars a₀

end TNLean.PEPS.AreaLaw.Geometry
