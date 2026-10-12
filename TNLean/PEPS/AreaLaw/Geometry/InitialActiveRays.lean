/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorRuns
import TNLean.PEPS.AreaLaw.Geometry.CellFanRays
import TNLean.PEPS.AreaLaw.Geometry.FanFrontiers
import Mathlib.Topology.NhdsWithin

/-!
# Actual active radial interfaces near an initial mark

Inside the open smaller square, the union of the actual initial frontiers consists exactly
of the radial segments where neighboring sectors have different assigned
identifiers. The assignment is the one derived from the actual initial
regions. A finite family indexed by its image supplies a second identifier
at every frontier point; actual triangle contacts then give the radial
description. Identifiers not in that finite image have no local points.

The same description holds in the closed square of half the smaller radius.
For a mark realizing its smallest incident side, this is a closed radius of
one hundred and twenty-eighth of that side. In this closed square, each
active radial segment agrees with its full directed ray. Each ray includes
the mark; an empty change set gives an empty union. All valid shifts remain
arbitrary. No cyclic enumeration, parity count, or repaired partition is asserted.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–370, and `prop:two-families`, lines 308–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Topology

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A point shared by two regions with disjoint interiors lies on the first
frontier when the second region is the closure of its interior.
Auxiliary to Section 11, `prop:two-families`, lines 313–323, and
`geometry:initial-stars`, lines 361–370. -/
private theorem mem_frontier_of_mem_disjoint_regular
    {S T : Set (ℝ × ℝ)} (hT : T = closure (interior T))
    (hd : Disjoint (interior S) (interior T)) {x : ℝ × ℝ}
    (hxS : x ∈ S) (hxT : x ∈ T) : x ∈ frontier S := by
  apply (mem_frontier_iff_notMem_interior hxS).mpr
  intro hx
  have h := hd.closure_right isOpen_interior
  rw [← hT] at h
  exact Set.disjoint_left.mp h hx hxT

/-- A finite local decomposition by assigned closed sets supplies two
different assigned identifiers at every frontier point in the open ball.
The finite index set is the image of the assignment, so repeated identifiers
do not furnish a spurious second member. The frontier argument reuses the
finite-cover theorem. Auxiliary to Section 11, `geometry:initial-stars`,
lines 352–370, and `prop:two-families`, lines 308–323. -/
private theorem exists_distinct_local_sector_contact {J I : Type*} [Finite J]
    (Q : J → Set (ℝ × ℝ)) (σ : J → I) (B : I → Set (ℝ × ℝ))
    (c : ℝ × ℝ) (r : ℝ) (hr : 0 < r)
    (hQclosed : ∀ s, IsClosed (Q s))
    (hcover : (⋃ s, Q s) = Metric.closedBall c r)
    (hBclosed : ∀ i, IsClosed (B i))
    (hdecomp : ∀ i, B i ∩ Metric.closedBall c r =
      ⋃ s : {s : J // σ s = i}, Q s.val)
    (i : I) (x : ℝ × ℝ) (hx : x ∈ frontier (B i))
    (hxball : x ∈ Metric.ball c r) :
    ∃ s t : J, σ s = i ∧ σ t ≠ i ∧ x ∈ Q s ∩ Q t := by
  classical
  let K := {i : I // i ∈ Set.range σ}
  let : Finite K := (Set.finite_range σ).to_subtype
  let E : K → Set (ℝ × ℝ) := fun j ↦ ⋃ s : {s : J // σ s = j.val}, Q s.val
  have hEclosed (j : K) : IsClosed (E j) :=
    isClosed_iUnion_of_finite fun s ↦ hQclosed s.val
  have hEcover : (⋃ j : K, E j) = closure (Metric.ball c r) := by
    calc
      (⋃ j : K, E j) = ⋃ s : J, Q s := by
        ext y
        constructor
        · intro hy
          obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
          obtain ⟨s, hys⟩ := Set.mem_iUnion.mp hyj
          exact Set.mem_iUnion.mpr ⟨s.val, hys⟩
        · intro hy
          obtain ⟨s, hys⟩ := Set.mem_iUnion.mp hy
          exact Set.mem_iUnion.mpr ⟨⟨σ s, ⟨s, rfl⟩⟩,
            Set.mem_iUnion.mpr ⟨⟨s, rfl⟩, hys⟩⟩
      _ = Metric.closedBall c r := hcover
      _ = closure (Metric.ball c r) := (closure_ball c hr.ne').symm
  have hxB : x ∈ B i := (hBclosed i).frontier_subset hx
  have hxQ : x ∈ ⋃ s : {s : J // σ s = i}, Q s.val := by
    rw [← hdecomp i]
    exact ⟨hxB, Metric.ball_subset_closedBall hxball⟩
  obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxQ
  let j₀ : K := ⟨i, ⟨s.val, s.property⟩⟩
  have hxE : x ∈ E j₀ := Set.mem_iUnion.mpr ⟨s, hxs⟩
  have heq : Filter.EventuallyEqSet (𝓝 x) (B i) (E j₀) := by
    change ∀ᶠ y in 𝓝 x, (y ∈ B i) = (y ∈ E j₀)
    filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
    have hyclosed : y ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hy
    have h : (y ∈ B i ∩ Metric.closedBall c r) = (y ∈ E j₀) :=
      congrArg (fun S : Set (ℝ × ℝ) ↦ y ∈ S) (hdecomp i)
    simpa only [Set.mem_inter_iff, hyclosed, and_true] using h
  have hxfront : x ∈ frontier (E j₀) := by
    apply (mem_frontier_iff_notMem_interior hxE).mpr
    intro hxi
    exact (mem_frontier_iff_notMem_interior hxB).mp hx
      (heq.mem_interior_iff.mpr hxi)
  rcases finiteCover_frontier_subset (Metric.ball c r) E hEclosed hEcover j₀ hxfront
      with houter | hcontact
  · exact False.elim ((mem_frontier_iff_notMem_interior hxball).mp houter
      (by simpa only [Metric.isOpen_ball.interior_eq] using hxball))
  · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hcontact
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxj.2
    refine ⟨s.val, t.val, s.property, ?_, hxs, hxt⟩
    intro hti
    apply j.property
    apply Subtype.ext
    exact t.property.symm.trans hti

/-- In the open smaller square about an actual fine-cell mark, membership in
some actual initial birth frontier is equivalent to membership in a radial
segment between neighboring sectors with different assigned identifiers.
The assignment is derived from the actual initial-region family, and unused
identifiers are included in the statement. Source: Section 11,
`geometry:initial-stars`, lines 333–370, especially 352–370, and
`prop:two-families`, lines 308–323. -/
theorem initialRegion_frontier_near_mark_iff_active_radial
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
    ∀ x ∈ Metric.ball v r,
      (∃ i : I, x ∈ frontier (initialBirthRegion o k₀ Z C a b hC h₀ i)) ↔
      ∃ s t : J,
        cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∧
        σ s ≠ σ t ∧
        x ∈ segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s) := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  let Q : J → Set (ℝ × ℝ) := fun s ↦
    (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s).region
  let B : I → Set (ℝ × ℝ) := initialBirthRegion o k₀ Z C a b hC h₀
  have hr : 0 < r := div_pos (pow_pos zero_lt_two ℓ) (by norm_num)
  have hcenter : cellFanCenter oSmall ℓ (0, 0) = v := by
    simp [cellFanCenter, oSmall, r]
  have hQclosed (s : J) : IsClosed (Q s) := by
    change IsClosed (cellFanPolygon oSmall ℓ (0, 0) (fun _ ↦ true) s).region
    rw [← (cellFanPolygon_interior_nonempty_and_closure_eq
      oSmall ℓ (0, 0) (fun _ ↦ true) s).2]
    exact isClosed_closure
  have hQcover : (⋃ s : J, Q s) = Metric.closedBall v r := by
    have h := closure_centered_dyadicCell_eq_closedBall v ℓ
    dsimp only at h
    exact (cellFanPolygons_cover oSmall ℓ (0, 0) (fun _ ↦ true)).trans h
  have hBregular (i : I) : B i = closure (interior (B i)) :=
    initialBirthRegion_eq_closure_initialOpenRegion o k₀ Z C a b hC h₀ i
  have hBclosed (i : I) : IsClosed (B i) := by
    rw [hBregular i]
    exact isClosed_closure
  have hpair : Pairwise (fun i j : I ↦ Disjoint (interior (B i)) (interior (B j))) :=
    initialOpenRegion_pairwise_disjoint o k₀ Z C a b hC h₀
  have hdecomp (i : I) : B i ∩ Metric.closedBall v r =
      ⋃ s : {s : J // σ s = i}, Q s.val :=
    (Classical.choose_spec
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1.2 i
  have hsub (s : J) : Q s ⊆ B (σ s) := by
    intro x hx
    exact ((hdecomp (σ s)).symm ▸
      (show x ∈ ⋃ t : {t : J // σ t = σ s}, Q t.val from
        Set.mem_iUnion.mpr ⟨⟨s, rfl⟩, hx⟩)).1
  change ∀ x ∈ Metric.ball v r, (∃ i : I, x ∈ frontier (B i)) ↔
    ∃ s t : J,
      cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
        cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∧
      σ s ≠ σ t ∧ x ∈ segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s)
  intro x hxball
  constructor
  · rintro ⟨i, hxfront⟩
    by_cases hxv : x = v
    · have hchange : ∃ s t : J,
          cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
            cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∧ σ s ≠ σ t := by
        by_contra hn
        have hno (s t : J)
            (hadj : cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
                cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∨
              cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t =
                cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) s) : σ s = σ t := by
          by_contra hne
          rcases hadj with h | h
          · exact hn ⟨s, t, h, hne⟩
          · exact hn ⟨t, s, h, Ne.symm hne⟩
        obtain ⟨j, hj⟩ := (exists_unique_initialRegion_of_no_active_sector
          o k₀ Z C a b hC h₀ k z v hk₀ hz hv hno).exists
        have hxU : x ∈ interior (B j) := hj (Metric.ball_subset_closedBall hxball)
        have hxB : x ∈ B i := (hBclosed i).frontier_subset hxfront
        by_cases hij : i = j
        · exact (mem_frontier_iff_notMem_interior hxB).mp hxfront (hij.symm ▸ hxU)
        · have hxj := mem_frontier_of_mem_disjoint_regular (hBregular i)
            (hpair (Ne.symm hij)) (interior_subset hxU) hxB
          exact (mem_frontier_iff_notMem_interior (interior_subset hxU)).mp hxj hxU
      obtain ⟨s, t, hadj, hne⟩ := hchange
      refine ⟨s, t, hadj, hne, ?_⟩
      rw [hxv]
      exact left_mem_segment ℝ _ _
    · obtain ⟨s, t, hsi, hti, hxs, hxt⟩ := exists_distinct_local_sector_contact
        Q σ B v r hr hQclosed hQcover hBclosed hdecomp i x hxfront hxball
      have hσne : σ s ≠ σ t := by
        intro he
        exact hti (he.symm.trans hsi)
      have hst : s ≠ t := by
        intro he
        exact hσne (congrArg σ he)
      have hvQ : v ∈ Q s ∩ Q t := by
        rw [cellFanPolygons_inter_eq, hcenter]
        exact Or.inl rfl
      have hcontact : (Q s ∩ Q t).Nontrivial :=
        Set.nontrivial_of_mem_mem_ne ⟨hxs, hxt⟩ hvQ hxv
      rcases cellFanPolygons_nontrivial_inter_cases
          oSmall ℓ (0, 0) (fun _ ↦ true) s t hst hcontact with h | h
      · refine ⟨s, t, h.1, hσne, ?_⟩
        have hxseg : x ∈ segment ℝ (cellFanCenter oSmall ℓ (0, 0))
            (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s) :=
          h.2 ▸ (show x ∈ Q s ∩ Q t from ⟨hxs, hxt⟩)
        simpa only [hcenter] using hxseg
      · refine ⟨t, s, h.1, hσne.symm, ?_⟩
        have hxseg : x ∈ segment ℝ (cellFanCenter oSmall ℓ (0, 0))
            (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) t) :=
          h.2 ▸ (show x ∈ Q s ∩ Q t from ⟨hxs, hxt⟩)
        simpa only [hcenter] using hxseg
  · rintro ⟨s, t, hadj, hne, hxradial⟩
    have hxQ : x ∈ Q s ∩ Q t := by
      rw [cellFanPolygons_inter_eq]
      right
      refine mem_convexJoin.mpr ⟨cellFanCenter oSmall ℓ (0, 0), rfl,
        cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s, ⟨?_, ?_⟩, ?_⟩
      · exact right_mem_segment ℝ _ _
      · rw [hadj]
        exact left_mem_segment ℝ _ _
      · rw [hcenter]
        exact hxradial
    exact ⟨σ s, mem_frontier_of_mem_disjoint_regular (hBregular (σ t))
      (hpair hne) (hsub s hxQ.1) (hsub t hxQ.2)⟩

/-- The actual active radial description holds throughout the closed square
of half the smaller fan radius. Its strict inclusion in the open square
uses only positivity of that radius. For a realized minimum incident side,
this radius is one hundred and twenty-eighth of the side.
Source: Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–370, and `prop:two-families`, lines 308–323. -/
theorem initialRegion_frontier_small_closedBall_iff_active_radial
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
    ∀ x ∈ Metric.closedBall v (r / 2),
      (∃ i : I, x ∈ frontier (initialBirthRegion o k₀ Z C a b hC h₀ i)) ↔
      ∃ s t : J,
        cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s =
          cellFanStart oSmall ℓ (0, 0) (fun _ ↦ true) t ∧
        σ s ≠ σ t ∧
        x ∈ segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s) := by
  classical
  dsimp only
  intro x hx
  have hr : 0 < (2 : ℝ) ^ (fineScaleIndex k - 5) / 2 := by positivity
  exact initialRegion_frontier_near_mark_iff_active_radial
    o k₀ Z C a b hC h₀ k z v hk₀ hz hv x
    (Metric.closedBall_subset_ball (by linarith) hx)

/-- On the closed half-radius square, the actual initial birth frontiers
are exactly the directed rays at changes of the canonical sector identifier.
Ray membership includes the center. An empty change set contributes no ray;
repeated identifiers in separated sectors remain separate occurrences.

Source: OpenAI, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–370, and `prop:two-families`, lines 308–323,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem initialRegion_frontier_small_closedBall_iff_active_ray
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
    ∀ x ∈ Metric.closedBall v (r / 2),
      (∃ i : I, x ∈ frontier (initialBirthRegion o k₀ Z C a b hC h₀ i)) ↔
      ∃ s : J, σ s ≠ σ (cellFanNext s) ∧
        SameRay ℝ (x - v)
          (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s - v) := by
  dsimp only
  intro x hx
  rw [initialRegion_frontier_small_closedBall_iff_active_radial
    o k₀ Z C a b hC h₀ k z v hk₀ hz hv x hx]
  simp only [cellFanEnd_eq_cellFanStart_iff, exists_eq_left]
  refine exists_congr fun s ↦ and_congr Iff.rfl ?_
  have hcenter :
      cellFanCenter
        (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
          v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2)
        (fineScaleIndex k - 5) (0, 0) = v := by simp [cellFanCenter]
  have hfull : x ∈ Metric.closedBall v ((2 : ℝ) ^ (fineScaleIndex k - 5) / 2) :=
    Metric.closedBall_subset_closedBall
      (half_le_self (div_nonneg
        (pow_nonneg (le_of_lt zero_lt_two) _) (le_of_lt zero_lt_two))) hx
  simpa only [hcenter] using
    cellFan_mem_radial_iff_sameRay_of_mem_closedBall
      (v.1 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2,
        v.2 - (2 : ℝ) ^ (fineScaleIndex k - 5) / 2)
      (fineScaleIndex k - 5) (0, 0) (fun _ ↦ true) s x
      (hcenter.symm ▸ hfull)

end TNLean.PEPS.AreaLaw.Geometry
