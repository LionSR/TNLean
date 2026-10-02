/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGaugedVerticalFluxMove
import TNLean.PEPS.TorusSweptStringDeformation
import TNLean.Algebra.ZModSmallDifference
import TNLean.PEPS.RegularInternalGaugeTransport
import TNLean.PEPS.TwoPlaquetteTransportTable
/-!
# The first physical crossing in a four-endpoint string presentation
The upward six-spin operation extends the lower insertion to the middle chord,
while a common tree gauge retains the actual other-string background. The lower
bond remains as the partner-string continuation; its plaquette flux is vacated.
Source: SCP10, arXiv:1001.3807, Theorem 6.16 and Section 6.6, local lines
2271–2305 and 2361–2415. This auxiliary single crossing does not establish the
complete four-endpoint braid or its reunion protocol.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (6 < width)] [Fact (5 < height)]
local instance firstCrossingWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance firstCrossingWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance firstCrossingHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local instance firstCrossingHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local instance firstCrossingWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance firstCrossingHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]
/-- The lower-left vertex of the first upward movement tile.
Source: SCP10, the flux-moving construction and string crossing, lines 2271–2415. -/
def torusFirstStringCrossingBase (v : X) : X := (v.1 + 1, v.2 + 1)
/-- The other string is reconstructed by identity gauge on the lower row and
`g` on the middle and upper rows. Source: SCP10, lines 2361–2386. -/
def torusFirstStringCrossingGauge (v : X) (g : G)
    (w : {x : X // x ∈ verticalTwoPlaquetteRegion (torusFirstStringCrossingBase v)}) : G :=
  if w.1.2 = v.2 + 1 then 1 else g
private theorem initial_internal_eq (v : X) (g h : G) (e : Edge Γₜ)
    (he : e.1.1 ∈ verticalTwoPlaquetteRegion (torusFirstStringCrossingBase v) ∧
      e.1.2 ∈ verticalTwoPlaquetteRegion (torusFirstStringCrossingBase v)) :
    torusSweptStringInitialOperators v g h e =
      torusGaugedVerticalFluxAssignment (torusFirstStringCrossingBase v)
        (torusFirstStringCrossingGauge v g) false h⁻¹ e := by
  let p := torusFirstStringCrossingBase v
  let φ := verticalTwoPlaquetteIso p
  have h21 : (2 : ZMod height) ≠ 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 2 1 (by have := Fact.out (p := 5 < height); norm_num; omega)).not.mpr
      (by norm_num : (2 : ℤ) ≠ 1)
  have h31 : (3 : ZMod height) ≠ 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 3 1 (by have := Fact.out (p := 5 < height); norm_num; omega)).not.mpr
      (by norm_num : (3 : ℤ) ≠ 1)
  have h20 : (2 : ZMod height) ≠ (0) := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 2 (0) (by have := Fact.out (p := 5 < height); norm_num; omega)).not.mpr
      (by norm_num : (2 : ℤ) ≠ (0))
  have h30 : (3 : ZMod height) ≠ (0) := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 3 (0) (by have := Fact.out (p := 5 < height); norm_num; omega)).not.mpr
      (by norm_num : (3 : ℤ) ≠ (0))
  have h2m1 : (2 : ZMod height) ≠ (-1) := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 2 (-1) (by have := Fact.out (p := 5 < height); norm_num; omega)).not.mpr
      (by norm_num : (2 : ℤ) ≠ (-1))
  have h3m1 : (3 : ZMod height) ≠ (-1) := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 3 (-1) (by have := Fact.out (p := 5 < height); norm_num; omega)).not.mpr
      (by norm_num : (3 : ℤ) ≠ (-1))
  have h12 : (1 : ZMod height) + 2 = 3 := by norm_num
  have h23 : (2 : ZMod height) + 1 = 3 := by norm_num
  have hm (i : Fin 6) :
      (p.1 + ((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod width),
       p.2 + ((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod height)) ∈
        verticalTwoPlaquetteRegion p := by
    rw [← verticalTwoPlaquetteIso_apply p i]
    exact (φ i).2
  have hm0 := hm 0
  have hm1 := hm 1
  have hm2 := hm 2
  have hm3 := hm 3
  have hm4 := hm 4
  have hm5 := hm 5
  norm_num at hm0 hm1 hm2 hm3 hm4 hm5
  have hm2' : (p.1, p.2 + 1 + 1) ∈ verticalTwoPlaquetteRegion p := by
    simpa only [add_assoc, one_add_one_eq_two] using hm2
  have hm3' : (p.1 + 1, p.2 + 1 + 1) ∈ verticalTwoPlaquetteRegion p := by
    simpa only [add_assoc, one_add_one_eq_two] using hm3
  have hup (x : ZMod width) (y : ZMod height) :
      regularDirectedTransport (torusSweptStringInitialOperators v g h)
        (torusGraph_adj_up x y) = torusSweptStringInitialUp v g (x,y) :=
    torusSweptStringInitialOperators_up_transport v (x, y) g h
  have hright (x : ZMod width) (y : ZMod height) :
      regularDirectedTransport (torusSweptStringInitialOperators v g h)
        (torusGraph_adj_right x y) = torusSweptStringInitialRight v h (x, y) :=
    torusSweptStringInitialOperators_right_transport v (x, y) g h
  have hcup (x : ZMod width) (y : ZMod height) :
      regularDirectedTransport (torusVerticalFluxAssignment p false h⁻¹)
        (torusGraph_adj_up x y) = 1 :=
    torusVerticalFluxAssignment_up_transport p (x, y) false h⁻¹
  have hc := torusVerticalFluxAssignment_right_transport p false h⁻¹
  have hct : regularDirectedTransport (torusVerticalFluxAssignment p false h⁻¹)
      (torusGraph_adj_right p.1 (p.2 + 2)) = 1 := by
    apply torusVerticalFluxAssignment_right_transport_of_ne p (p.1, p.2 + 2) false h⁻¹
    · simpa using h20
    · simpa using h21
  refine verticalTwoPlaquette_internal_eq_of_transports p
    (torusSweptStringInitialOperators v g h)
    (torusGaugedVerticalFluxAssignment p (torusFirstStringCrossingGauge v g) false h⁻¹)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ e he
  all_goals
    rw [regularDirectedTransport_eq_of_internal_reconstruction
      (verticalTwoPlaquetteRegion p) (torusFirstStringCrossingGauge v g)
      (torusVerticalFluxAssignment p false h⁻¹)
      (torusGaugedVerticalFluxAssignment p (torusFirstStringCrossingGauge v g) false h⁻¹)
      (fun e he => by simp only [torusGaugedVerticalFluxAssignment, dite_eq_left he])
      _ (by assumption) (by assumption)]
  all_goals
    first
    | rw [hup p.1 p.2, hcup p.1 p.2]
    | rw [hright p.1 p.2, hc.1]
    | rw [hup p.1 (p.2 + 1), hcup p.1 (p.2 + 1)]
    | rw [hright p.1 (p.2 + 1), hc.2]
    | rw [hright p.1 (p.2 + 2), hct]
    | rw [hup (p.1 + 1) p.2, hcup (p.1 + 1) p.2]
    | rw [hup (p.1 + 1) (p.2 + 1), hcup (p.1 + 1) (p.2 + 1)]
  all_goals
    simp_all [torusFirstStringCrossingBase, p, torusFirstStringCrossingGauge,
      torusSweptStringInitialUp, torusSweptStringInitialRight, add_assoc,
      one_add_one_eq_two, sub_eq_add_neg]
/-- The actual starting string assignment has the common gauge reconstruction
on every internal bond of the upward movement tile. Source: SCP10, lines 2271–2386. -/
theorem torusFirstStringCrossing_initial_extension (v : X) (g h : G) :
    regularRegionBondExtension (verticalTwoPlaquetteRegion (torusFirstStringCrossingBase v))
      (torusGaugedVerticalFluxAssignment (torusFirstStringCrossingBase v)
        (torusFirstStringCrossingGauge v g) false h⁻¹)
      (torusSweptStringInitialOperators v g h) = torusSweptStringInitialOperators v g h := by
  apply regularRegionBondExtension_eq_of_internal
  intro e he
  exact (initial_internal_eq v g h e he).symm
/-- The output retains the common crossing and exterior operators. Its added
middle chord is reconstructed with the same vertex gauge as the input.
Source: SCP10, the elementary movement and string construction, lines 2271–2386. -/
def torusFirstStringCrossingOutput (v : X) (g h : G) : Edge Γₜ → G :=
  regularRegionBondExtension (verticalTwoPlaquetteRegion (torusFirstStringCrossingBase v))
    (torusGaugedVerticalFluxAssignment (torusFirstStringCrossingBase v)
      (torusFirstStringCrossingGauge v g) true h⁻¹)
    (torusSweptStringInitialOperators v g h)
/-- Apart from the middle horizontal bond, every ordered operator is retained.
Source: SCP10, the first elementary crossing in lines 2271–2386. -/
theorem torusFirstStringCrossingOutput_eq_of_ne (v : X) (g h : G) (e : Edge Γₜ)
    (he : e ≠ Edge.ofAdj (torusGraph_adj_right (v.1 + 1) (v.2 + 2))) :
    torusFirstStringCrossingOutput v g h e = torusSweptStringInitialOperators v g h e := by
  let p := torusFirstStringCrossingBase v
  have hm : Edge.ofAdj (torusGraph_adj_right p.1 (p.2 + 1)) =
      Edge.ofAdj (torusGraph_adj_right (v.1 + 1) (v.2 + 2)) := by
    change Edge.ofAdj (torusGraph_adj_right (v.1 + 1) (v.2 + 1 + 1)) = _
    have hy : v.2 + 1 + 1 = v.2 + 2 := by ring
    rw [hy]
  have he' : e ≠ Edge.ofAdj (torusGraph_adj_right p.1 (p.2 + 1)) := by
    intro H
    exact he (H.trans hm)
  have hc : torusVerticalFluxAssignment p true h⁻¹ e =
      torusVerticalFluxAssignment p false h⁻¹ e := by
    simp [torusVerticalFluxAssignment, he']
  have hd : torusGaugedVerticalFluxAssignment p (torusFirstStringCrossingGauge v g)
      true h⁻¹ e =
      torusGaugedVerticalFluxAssignment p (torusFirstStringCrossingGauge v g)
        false h⁻¹ e := by
    simp only [torusGaugedVerticalFluxAssignment]
    split_ifs
    · rw [hc]
    · rfl
  have H := congrFun (torusFirstStringCrossing_initial_extension v g h) e
  change (regularRegionBondExtension (verticalTwoPlaquetteRegion p)
    (torusGaugedVerticalFluxAssignment p (torusFirstStringCrossingGauge v g) false h⁻¹)
    (torusSweptStringInitialOperators v g h)) e = _ at H
  change (regularRegionBondExtension (verticalTwoPlaquetteRegion p)
    (torusGaugedVerticalFluxAssignment p (torusFirstStringCrossingGauge v g) true h⁻¹)
    (torusSweptStringInitialOperators v g h)) e = _
  simpa only [regularRegionBondExtension, hd] using H
/-- The additional middle rightward transport is the conjugated insertion,
including when the native ordered edge crosses a seam. Source: SCP10, lines 2361–2386. -/
theorem torusFirstStringCrossingOutput_middle_transport (v : X) (g h : G) :
    regularDirectedTransport (torusFirstStringCrossingOutput v g h)
      (torusGraph_adj_right (v.1 + 1) (v.2 + 2)) = g * h⁻¹ * g⁻¹ := by
  let p := torusFirstStringCrossingBase v
  have hx : (v.1 + 1, v.2 + 2) ∈ verticalTwoPlaquetteRegion p := by
    have H := (verticalTwoPlaquetteIso p 1).2
    rw [verticalTwoPlaquetteIso_apply p 1] at H
    simpa [p, torusFirstStringCrossingBase, add_assoc, one_add_one_eq_two] using H
  have hy : (v.1 + 1 + 1, v.2 + 2) ∈ verticalTwoPlaquetteRegion p := by
    have H := (verticalTwoPlaquetteIso p 4).2
    rw [verticalTwoPlaquetteIso_apply p 4] at H
    simpa [p, torusFirstStringCrossingBase, add_assoc, one_add_one_eq_two] using H
  have h21 : (2 : ZMod height) ≠ 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 2 1 (by have := Fact.out (p := 5 < height); norm_num; omega)).not.mpr
      (by norm_num : (2 : ℤ) ≠ 1)
  rw [regularDirectedTransport_eq_of_internal_reconstruction
    (verticalTwoPlaquetteRegion p) (torusFirstStringCrossingGauge v g)
    (torusVerticalFluxAssignment p true h⁻¹) (torusFirstStringCrossingOutput v g h)
    (fun e he => by
      change (if he' : e.1.1 ∈ verticalTwoPlaquetteRegion p ∧
          e.1.2 ∈ verticalTwoPlaquetteRegion p then
        (if he'' : e.1.1 ∈ verticalTwoPlaquetteRegion p ∧
            e.1.2 ∈ verticalTwoPlaquetteRegion p then
          _ else (1 : G)) else _) = _
      simp only [dite_eq_left he]
      rfl)
    (torusGraph_adj_right (v.1 + 1) (v.2 + 2)) hx hy]
  have hc : regularDirectedTransport (torusVerticalFluxAssignment p true h⁻¹)
      (torusGraph_adj_right (v.1 + 1) (v.2 + 2)) = h⁻¹ := by
    simpa [p, torusFirstStringCrossingBase, add_assoc, one_add_one_eq_two] using
      (torusVerticalFluxAssignment_right_transport p true h⁻¹).2
  rw [hc]
  simp [torusFirstStringCrossingGauge, h21]
variable [Fintype G] [DecidableEq G] {d : ℕ}
/-- A fixed original six-spin unitary implements the first upward crossing,
before both string labels and every boundary label. The literal partner string
and exterior assignment are retained. This auxiliary consequence of SCP10,
Theorem 6.16 and lines 2361–2386 does not assert the full braid. -/
theorem IsGIsometric.exists_unitary_torusFirstStringCrossing
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    let R := verticalTwoPlaquetteRegion (torusFirstStringCrossingBase v)
    ∃ W : Matrix ({x : X // x ∈ R} → Fin d) ({x : X // x ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({x : X // x ∈ R} → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (g h : G) (θ : {e : Edge Γₜ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusSweptStringInitialOperators v g h))) R
          (fun e => Fintype.equivFin G (θ e)) =
        openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusFirstStringCrossingOutput v g h))) R
          (fun e => Fintype.equivFin G (θ e))) ∧
      ∀ (g h : G), regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusSweptStringInitialOperators v g h))) =
        stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusFirstStringCrossingOutput v g h))) := by
  classical
  obtain ⟨W, hW, hglobal, hcols, hstates⟩ :=
    ha.exists_unitary_torusGaugedVerticalFluxMove (torusFirstStringCrossingBase v)
  refine ⟨W, hW, hglobal, ?_, ?_⟩
  · intro g h θ
    have H := hcols (torusFirstStringCrossingGauge v g) false h⁻¹
      (torusSweptStringInitialOperators v g h) θ
    simp only [Bool.false_eq_true, ite_false] at H
    rw [torusFirstStringCrossing_initial_extension v g h] at H
    exact H
  · intro g h
    have H := hstates (torusFirstStringCrossingGauge v g) false h⁻¹
      (torusSweptStringInitialOperators v g h)
    simp only [Bool.false_eq_true, ite_false] at H
    rw [torusFirstStringCrossing_initial_extension v g h] at H
    exact H
end TNLean.PEPS
