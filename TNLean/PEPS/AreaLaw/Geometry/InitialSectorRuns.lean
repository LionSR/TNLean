/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorColors
import TNLean.PEPS.AreaLaw.Geometry.FanRuns
import Mathlib.Logic.Relation

/-!
# Actual initial identifiers on local sector runs

The actual assignment of the eight local sectors descends to the connected
components of the existing equal-colored fan graph. The resulting function
is unique, and every actual birth region in the smaller closed square is
exactly the union of the run regions carrying its identifier. Separated runs
with the same identifier remain separate components.

If every neighboring pair has the same assigned identifier, the proved
connectivity of a constant-colored fan makes the assignment constant. The
working fan lies in the corresponding birth region. Its strict margin puts
the entire smaller closed square in one unique actual open region.

## References

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
