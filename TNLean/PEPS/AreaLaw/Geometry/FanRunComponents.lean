/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRunConnectedness
import TNLean.PEPS.AreaLaw.Geometry.FanRunDisjointness
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows
import Mathlib.Topology.Connected.Clopen

/-!
# Connected components of a cut fan square

Remove the radial segments at color changes in an actual all-midpoint fan.
The connected components of the remaining open square correspond uniquely
to the runs of consecutive equally colored triangles. Membership in a closed
run region determines the component containing a point.

The correspondence follows from the finite cover by connected, relatively
open and closed retained run regions. It applies to arbitrary dyadic origins,
cell indices and natural exponents, including exponent zero. The change set
may be empty. Distinct runs carrying the same color give distinct components.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–370,
and `prop:two-families`, lines 308–323.
This is an auxiliary to the initial-star construction.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Connected components of the cut square correspond uniquely to actual fan runs.
Connectedness, disjointness, coverage and relative clopenness are derived from
the actual fan geometry.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and `prop:two-families`,
lines 308–323, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Empty cuts are allowed. Distinct runs bearing the same color remain distinct. -/
theorem cellFanRun_connectedComponents_equiv
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2) :
    let c := cellFanCenter o ℓ z
    let r := (2 : ℝ) ^ ℓ / 2
    let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
      {t | family t ≠ family (cellFanNext t)}
    let L := ⋃ t ∈ A,
      segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
    let Ω := Metric.ball c r \ L
    let W := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
      cellFanRunRegion o ℓ z (fun _ ↦ true) family R
    ∃! e : ConnectedComponents Ω ≃ CellFanRun o ℓ z (fun _ ↦ true) family,
      ∀ (x : Ω) (R : CellFanRun o ℓ z (fun _ ↦ true) family),
        e (ConnectedComponents.mk x) = R ↔ x.val ∈ W R := by
  classical
  dsimp only
  let c := cellFanCenter o ℓ z
  let r := (2 : ℝ) ^ ℓ / 2
  let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
    {t | family t ≠ family (cellFanNext t)}
  let L := ⋃ t ∈ A,
    segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
  let Ω := Metric.ball c r \ L
  let W := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
    cellFanRunRegion o ℓ z (fun _ ↦ true) family R
  let S := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
    (W R \ L) ∩ Metric.ball c r
  let U := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
    {x : Ω | x.val ∈ W R}
  have hconnected (R : CellFanRun o ℓ z (fun _ ↦ true) family) :
      IsConnected (S R) :=
    cellFanRunRegion_cut_inter_ball_isConnected o ℓ z family R
  have hdisjoint : Pairwise (fun R T ↦ Disjoint (S R) (S T)) := by
    intro R T hRT
    exact (cellFanRunRegion_sdiff_radials_pairwise_disjoint o ℓ z family hRT).mono
      Set.inter_subset_left Set.inter_subset_left
  have hball : Metric.ball c r ⊆ closure (dyadicCell o ℓ z) := by
    rw [← closedBall_cellFanCenter_eq_closure_dyadicCell o ℓ z]
    exact Metric.ball_subset_closedBall
  have hclosed (R : CellFanRun o ℓ z (fun _ ↦ true) family) : IsClosed (W R) := by
    change IsClosed (⋃ i ∈ R.supp, (cellFanPolygon o ℓ z (fun _ ↦ true) i).region)
    exact R.supp.toFinite.isClosed_biUnion fun i _ ↦
      (cellFanPolygon o ℓ z (fun _ ↦ true) i).isCompact_region.isClosed
  have hclosedU (R : CellFanRun o ℓ z (fun _ ↦ true) family) : IsClosed (U R) := by
    change IsClosed ((Subtype.val : Ω → ℝ × ℝ) ⁻¹' W R)
    exact (hclosed R).preimage continuous_subtype_val
  have himage (R : CellFanRun o ℓ z (fun _ ↦ true) family) :
      (Subtype.val : Ω → ℝ × ℝ) '' U R = S R := by
    change (Subtype.val : Ω → ℝ × ℝ) '' ((Subtype.val : Ω → ℝ × ℝ) ⁻¹' W R) = S R
    rw [Subtype.image_preimage_val]
    ext x
    constructor
    · rintro ⟨⟨hxBall, hxL⟩, hxR⟩
      exact ⟨⟨hxR, hxL⟩, hxBall⟩
    · rintro ⟨⟨hxR, hxL⟩, hxBall⟩
      exact ⟨⟨hxBall, hxL⟩, hxR⟩
  have hconnectedU (R : CellFanRun o ℓ z (fun _ ↦ true) family) :
      IsConnected (U R) := by
    exact ⟨Set.image_nonempty.mp ((himage R).symm ▸ (hconnected R).nonempty),
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        ((himage R).symm ▸ (hconnected R).isPreconnected)⟩
  have hcover : (⋃ R : CellFanRun o ℓ z (fun _ ↦ true) family, U R) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hxcell : x.val ∈ closure (dyadicCell o ℓ z) := hball x.property.1
      obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp
        ((cellFanRunRegions_cover o ℓ z (fun _ ↦ true) family).symm ▸ hxcell)
      exact Set.mem_iUnion.mpr ⟨R, hxR⟩
  have hdisjointU : Pairwise (fun R T ↦ Disjoint (U R) (U T)) := by
    intro R T hne
    rw [Set.disjoint_left]
    intro x hxR hxT
    exact Set.disjoint_left.mp (hdisjoint hne)
      ⟨⟨hxR, x.property.2⟩, x.property.1⟩
      ⟨⟨hxT, x.property.2⟩, x.property.1⟩
  have hclopen (R : CellFanRun o ℓ z (fun _ ↦ true) family) : IsClopen (U R) := by
    refine ⟨hclosedU R, ?_⟩
    rw [← isClosed_compl_iff, Set.compl_eq_univ_sdiff, ← hcover, Set.iUnion_sdiff]
    refine isClosed_iUnion_of_finite fun T ↦ ?_
    rcases eq_or_ne R T with rfl | hne
    · simp
    · simpa only [(hdisjointU hne.symm).sdiff_eq_left] using hclosedU T
  let E : ConnectedComponents Ω ≃ CellFanRun o ℓ z (fun _ ↦ true) family :=
    ConnectedComponents.equivOfIsClopenOfIsConnected
      hclopen hdisjointU hcover hconnectedU
  have hE (x : Ω) (R : CellFanRun o ℓ z (fun _ ↦ true) family) :
      E (ConnectedComponents.mk x) = R ↔ x.val ∈ W R := by
    constructor
    · intro hxE
      obtain ⟨T, hxT⟩ := Set.iUnion_eq_univ_iff.mp hcover x
      have hxET : E (ConnectedComponents.mk x) = T :=
        ConnectedComponents.equivOfIsClopenOfIsConnected_mk
          hclopen hdisjointU hcover hconnectedU x hxT
      exact (hxET.symm.trans hxE) ▸ hxT
    · intro hxR
      exact ConnectedComponents.equivOfIsClopenOfIsConnected_mk
        hclopen hdisjointU hcover hconnectedU x hxR
  refine ⟨E, hE, ?_⟩
  intro e he
  apply Equiv.ext
  intro q
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
  exact (he x (E (ConnectedComponents.mk x))).mpr
    ((hE x (E (ConnectedComponents.mk x))).mp rfl)

end TNLean.PEPS.AreaLaw.Geometry
