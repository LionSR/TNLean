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
# Connected components of cut fan squares

Remove the radial segments at color changes in an all-midpoint fan. The
connected components of the remaining open cell square, and of its concentric
closed square of half the radius, correspond uniquely to the runs of
consecutive equally colored triangles. Membership in a closed run region
determines the component containing a point.

Both correspondences follow from a finite cover by connected retained run
regions that are relatively open and closed. They apply to arbitrary dyadic
origins, cell indices and natural exponents, including exponent zero. The
change set may be empty. Distinct runs carrying the same color give distinct
components.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–370,
and `prop:two-families`, lines 308–323.
These are local auxiliaries to the initial-star construction.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A subset of the closed fan cell has one connected component for each
run whenever every retained run intersection is connected. Closedness of the
run regions, coverage and disjointness give relative clopenness. The window
need not itself be open or closed.

Common argument for the two centered-square correspondences below.
Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and `prop:two-families`,
lines 308–323, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
private theorem cellFanRun_connectedComponents_equiv_of_window
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2)
    (K : Set (ℝ × ℝ))
    (hK : K ⊆ closure (dyadicCell o ℓ z))
    (hconnectedWindow : ∀ R : CellFanRun o ℓ z (fun _ ↦ true) family,
      let c := cellFanCenter o ℓ z
      let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
        {t | family t ≠ family (cellFanNext t)}
      let L := ⋃ t ∈ A,
        segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
      IsConnected ((cellFanRunRegion o ℓ z (fun _ ↦ true) family R \ L) ∩ K)) :
    let c := cellFanCenter o ℓ z
    let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
      {t | family t ≠ family (cellFanNext t)}
    let L := ⋃ t ∈ A,
      segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
    let Ω := K \ L
    let W := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
      cellFanRunRegion o ℓ z (fun _ ↦ true) family R
    ∃! e : ConnectedComponents Ω ≃ CellFanRun o ℓ z (fun _ ↦ true) family,
      ∀ (x : Ω) (R : CellFanRun o ℓ z (fun _ ↦ true) family),
        e (ConnectedComponents.mk x) = R ↔ x.val ∈ W R := by
  classical
  dsimp only
  let c := cellFanCenter o ℓ z
  let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
    {t | family t ≠ family (cellFanNext t)}
  let L := ⋃ t ∈ A,
    segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
  let Ω := K \ L
  let W := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
    cellFanRunRegion o ℓ z (fun _ ↦ true) family R
  let S := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
    (W R \ L) ∩ K
  let U := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
    {x : Ω | x.val ∈ W R}
  have hconnected (R : CellFanRun o ℓ z (fun _ ↦ true) family) :
      IsConnected (S R) := hconnectedWindow R
  have hdisjoint : Pairwise (fun R T ↦ Disjoint (S R) (S T)) := by
    intro R T hRT
    exact (cellFanRunRegion_sdiff_radials_pairwise_disjoint o ℓ z family hRT).mono
      Set.inter_subset_left Set.inter_subset_left
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
      have hxcell : x.val ∈ closure (dyadicCell o ℓ z) := hK x.property.1
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
  refine cellFanRun_connectedComponents_equiv_of_window o ℓ z family
    (Metric.ball (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2)) ?_ ?_
  · rw [← closedBall_cellFanCenter_eq_closure_dyadicCell o ℓ z]
    exact Metric.ball_subset_closedBall
  · exact fun R ↦ cellFanRunRegion_cut_inter_ball_isConnected o ℓ z family R

/-- Connected components of the closed square of half the fan radius,
with the color-change radial segments removed, correspond uniquely to fan
runs. A component is assigned to a run exactly when one of its points belongs
to that run's closed region.

The origin and cell index are arbitrary, exponent zero and empty cuts are
permitted, and distinct runs bearing the same color remain distinct.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and `prop:two-families`,
lines 308–323, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is a local component correspondence in the initial-star construction. -/
theorem cellFanRun_closedHalf_connectedComponents_equiv
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2) :
    let c := cellFanCenter o ℓ z
    let r := (2 : ℝ) ^ ℓ / 2
    let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
      {t | family t ≠ family (cellFanNext t)}
    let L := ⋃ t ∈ A,
      segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
    let Ω := Metric.closedBall c (r / 2) \ L
    let W := fun R : CellFanRun o ℓ z (fun _ ↦ true) family ↦
      cellFanRunRegion o ℓ z (fun _ ↦ true) family R
    ∃! e : ConnectedComponents Ω ≃ CellFanRun o ℓ z (fun _ ↦ true) family,
      ∀ (x : Ω) (R : CellFanRun o ℓ z (fun _ ↦ true) family),
        e (ConnectedComponents.mk x) = R ↔ x.val ∈ W R := by
  refine cellFanRun_connectedComponents_equiv_of_window o ℓ z family
    (Metric.closedBall (cellFanCenter o ℓ z) (((2 : ℝ) ^ ℓ / 2) / 2)) ?_ ?_
  · rw [← closedBall_cellFanCenter_eq_closure_dyadicCell o ℓ z]
    exact Metric.closedBall_subset_closedBall
      (half_le_self (div_nonneg (pow_nonneg zero_le_two ℓ) zero_le_two))
  · exact fun R ↦ cellFanRunRegion_cut_inter_closedHalfBall_isConnected o ℓ z family R

end TNLean.PEPS.AreaLaw.Geometry
