/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorColors
import TNLean.PEPS.AreaLaw.Geometry.FanRunComponents
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorRuns
import TNLean.PEPS.AreaLaw.Geometry.InitialActiveRayCount

/-!
# Connected components and initial regions near a fine-cell mark

The connected components of the smaller open square, and of its concentric
closed square of half the radius, correspond uniquely to sector runs after
the identifier-change radial segments are removed. The sector assignment is
the canonical one derived from the initial regions. Neighboring sector colors
change exactly when their assigned identifiers change, so the radial deletion
agrees with that of the colored fan.

Every retained point of a run in the smaller open square belongs to its assigned
initial open region. The closed run decomposition supplies birth-region
membership, while the active-radial description excludes the frontier. The
change set may be empty; separated runs carrying the same initial identifier
remain distinct.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 361–370, and `prop:two-families`, lines 299–323.
These are local auxiliaries to the initial-star construction.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Connected components of the smaller open square, with the actual
identifier-change radial segments removed, correspond uniquely to the runs
of the derived initial sector assignment. A component is assigned to a run
exactly when any of its points belongs to that run's closed region.

The assignment is the unique one derived from the initial regions. Empty
cuts are permitted, and separated runs carrying the same initial identifier
remain distinct. No injectivity of the run-to-identifier assignment is asserted.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 333–370, especially 361–370, and
`prop:two-families`, lines 299–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This does not assert the full isolated-star or recursive repair theorem. -/
theorem initialRegion_angular_connectedComponents_equiv
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
    let family : J → Fin 2 :=
      fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
    let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
    let L : Set (ℝ × ℝ) :=
      ⋃ s : {s : J // σ s ≠ σ (cellFanNext s)},
        segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s.val)
    let Ω := Metric.ball v r \ L
    ∃! e : ConnectedComponents Ω ≃ G.ConnectedComponent,
      ∀ (x : Ω) (R : G.ConnectedComponent),
        e (ConnectedComponents.mk x) = R ↔
          x.val ∈ cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  let family : J → Fin 2 :=
    fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
  let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
  let L : Set (ℝ × ℝ) :=
    ⋃ s : {s : J // σ s ≠ σ (cellFanNext s)},
      segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s.val)
  let Ω := Metric.ball v r \ L
  change ∃! e : ConnectedComponents Ω ≃ G.ConnectedComponent,
    ∀ (x : Ω) (R : G.ConnectedComponent),
      e (ConnectedComponents.mk x) = R ↔
        x.val ∈ cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R
  have hcenter : cellFanCenter oSmall ℓ (0, 0) = v := by
    simp [cellFanCenter, oSmall, r]
  have hchange (s : J) :
      family s ≠ family (cellFanNext s) ↔ σ s ≠ σ (cellFanNext s) :=
    not_congr (initialRegion_sector_assignment_adjacent_colors_eq_iff
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv s (cellFanNext s)
      (Or.inl (cellFanEnd_eq_cellFanStart_next oSmall ℓ (0, 0) s)))
  have hcuts :
      (⋃ s ∈ {s : J | family s ≠ family (cellFanNext s)},
        segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s)) = L := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨s, (hchange s).mp hs⟩, hxs⟩
    · intro hx
      obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion₂.mpr
        ⟨s.val, (hchange s.val).mpr s.property, hxs⟩
  have hgeneric := cellFanRun_connectedComponents_equiv oSmall ℓ (0, 0) family
  dsimp only at hgeneric
  rw [hcenter, hcuts] at hgeneric
  change (∃! e : ConnectedComponents Ω ≃ G.ConnectedComponent,
    ∀ (x : Ω) (R : G.ConnectedComponent),
      e (ConnectedComponents.mk x) = R ↔
        x.val ∈ cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R) at hgeneric
  exact hgeneric

/-- Connected components of the closed square of half the smaller fan
radius, with the actual identifier-change radial segments removed, correspond
uniquely to runs of the derived initial sector assignment. Membership in a
closed run region characterizes the component of a retained point.

The sector assignment is canonical and the valid shifts are arbitrary. Empty
cuts are permitted, and separated runs carrying the same initial identifier
remain distinct.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 333–370, especially 361–370, and
`prop:two-families`, lines 299–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is a local component correspondence in the initial-star construction. -/
theorem initialRegion_closedHalf_angular_connectedComponents_equiv
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
    let family : J → Fin 2 :=
      fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
    let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
    let L : Set (ℝ × ℝ) :=
      ⋃ s : {s : J // σ s ≠ σ (cellFanNext s)},
        segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s.val)
    let Ω := Metric.closedBall v (r / 2) \ L
    ∃! e : ConnectedComponents Ω ≃ G.ConnectedComponent,
      ∀ (x : Ω) (R : G.ConnectedComponent),
        e (ConnectedComponents.mk x) = R ↔
          x.val ∈ cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  let family : J → Fin 2 :=
    fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
  let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
  let L : Set (ℝ × ℝ) :=
    ⋃ s : {s : J // σ s ≠ σ (cellFanNext s)},
      segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s.val)
  let Ω := Metric.closedBall v (r / 2) \ L
  change ∃! e : ConnectedComponents Ω ≃ G.ConnectedComponent,
    ∀ (x : Ω) (R : G.ConnectedComponent),
      e (ConnectedComponents.mk x) = R ↔
        x.val ∈ cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R
  have hcenter : cellFanCenter oSmall ℓ (0, 0) = v := by
    simp [cellFanCenter, oSmall, r]
  have hchange (s : J) :
      family s ≠ family (cellFanNext s) ↔ σ s ≠ σ (cellFanNext s) :=
    not_congr (initialRegion_sector_assignment_adjacent_colors_eq_iff
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv s (cellFanNext s)
      (Or.inl (cellFanEnd_eq_cellFanStart_next oSmall ℓ (0, 0) s)))
  have hcuts :
      (⋃ s ∈ {s : J | family s ≠ family (cellFanNext s)},
        segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s)) = L := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨s, (hchange s).mp hs⟩, hxs⟩
    · intro hx
      obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion₂.mpr
        ⟨s.val, (hchange s.val).mpr s.property, hxs⟩
  have hgeneric := cellFanRun_closedHalf_connectedComponents_equiv oSmall ℓ (0, 0) family
  dsimp only at hgeneric
  rw [hcenter, hcuts] at hgeneric
  exact hgeneric

/-- A point of an actual sector run inside the smaller open square, avoiding
the actual identifier-change radial segments, belongs to the initial open
region assigned to that run. The sector and run assignments are derived
uniquely from the actual initial-region family. Empty cuts are permitted,
and separated runs with the same assigned identifier remain distinct.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 333–370, especially 361–370, and
`prop:two-families`, lines 299–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem initialRegion_sector_run_mem_initialOpenRegion
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
    let family : J → Fin 2 :=
      fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
    let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
    let μ : G.ConnectedComponent → I := Classical.choose
      (exists_unique_initialRegion_sector_run_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
    let L : Set (ℝ × ℝ) :=
      ⋃ s : {s : J // σ s ≠ σ (cellFanNext s)},
        segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s.val)
    ∀ (R : G.ConnectedComponent) (x : ℝ × ℝ),
      x ∈ Metric.ball v r \ L →
      x ∈ cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R →
      x ∈ initialOpenRegion o k₀ Z C a b hC h₀ (μ R) := by
  classical
  dsimp only
  let ℓ := fineScaleIndex k - 5
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (v.1 - r, v.2 - r)
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let I := InitialRegionIndex o k₀ Z C a b hC h₀
  let σ : J → I :=
    initialSectorAssignment o k₀ Z C a b hC h₀ k z v hk₀ hz hv
  let family : J → Fin 2 :=
    fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s)
  let G := cellFanRunGraph oSmall ℓ (0, 0) (fun _ ↦ true) family
  let μ : G.ConnectedComponent → I := Classical.choose
    (exists_unique_initialRegion_sector_run_assignment
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
  let L : Set (ℝ × ℝ) :=
    ⋃ s : {s : J // σ s ≠ σ (cellFanNext s)},
      segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s.val)
  change ∀ (R : G.ConnectedComponent) (x : ℝ × ℝ),
    x ∈ Metric.ball v r \ L →
    x ∈ cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family R →
    x ∈ initialOpenRegion o k₀ Z C a b hC h₀ (μ R)
  intro R x hx hxR
  have hdecomp (i : I) :
      initialBirthRegion o k₀ Z C a b hC h₀ i ∩ Metric.closedBall v r =
        ⋃ T : {T : G.ConnectedComponent // μ T = i},
          cellFanRunRegion oSmall ℓ (0, 0) (fun _ ↦ true) family T.val :=
    (Classical.choose_spec
      (exists_unique_initialRegion_sector_run_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)).1.2 i
  have hbirth : x ∈ initialBirthRegion o k₀ Z C a b hC h₀ (μ R) := by
    have hmem : x ∈ initialBirthRegion o k₀ Z C a b hC h₀ (μ R) ∩
        Metric.closedBall v r := by
      rw [hdecomp (μ R)]
      exact Set.mem_iUnion.mpr ⟨⟨R, rfl⟩, hxR⟩
    exact hmem.1
  have hnot_frontier : x ∉ frontier (initialBirthRegion o k₀ Z C a b hC h₀ (μ R)) := by
    intro hxfront
    obtain ⟨s, hs, hxs⟩ :=
      (initialRegion_frontier_near_mark_iff_active_successor
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv x hx.1).mp ⟨μ R, hxfront⟩
    exact hx.2 (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hxs⟩)
  change x ∈ interior (initialBirthRegion o k₀ Z C a b hC h₀ (μ R))
  rw [← self_sdiff_frontier]
  exact ⟨hbirth, hnot_frontier⟩
end TNLean.PEPS.AreaLaw.Geometry
