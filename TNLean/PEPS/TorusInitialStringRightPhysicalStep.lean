/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSweptHorizontalStep
import TNLean.PEPS.TorusGaugedHorizontalFluxMove
import TNLean.PEPS.RegularInternalGaugeTransport
import TNLean.PEPS.TwoPlaquetteTransportTable

/-!
# The original-spin first rightward step in the two-string configuration

The continuing first string is retained literally. The first rightward endpoint
step changes only the middle upward bond transport from g to g h. Its clockwise
plaquette flux h moves from (1,1) to (2,1), relative to the source patch.

Source: SCP10, arXiv:1001.3807, physical movement in Theorem 6.16 and the
four-endpoint braiding figure, lines 2271–2305 and 2340–2423.

**Scope restriction (finite-torus elementary movement):** The horizontal period
is at least eight and the vertical period at least seven. This calculation
handles the first rightward step; it does not establish the complete prescribed
braid. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance rightPhysicalStepWidthSix : Fact (6 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance rightPhysicalStepHeightFive : Fact (5 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance rightPhysicalStepWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance rightPhysicalStepWidthThree : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance rightPhysicalStepHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance rightPhysicalStepWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance rightPhysicalStepHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance rightPhysicalStepWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance rightPhysicalStepHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

open scoped Matrix

/-- The other-string tree background on the first rightward movement tile.
Source: SCP10, the four-endpoint route, lines 2340–2423. -/
def torusFirstRightStepGauge (v : X) (g h : G)
    (w : {x : X // x ∈ translatedTwoPlaquetteRegion (v.1 + 1, v.2 + 1)}) : G :=
  if w.1.2 = v.2+1 then (if w.1.1 = v.1+1 then h else 1) else g

private def rightStepFamily (v : X) (g h : G) (b : Bool) : Edge Γₜ → G :=
  if b then torusSweptStringRightStepOperators v g h
  else torusSweptStringInitialOperators v g h

private theorem horizontal_transport (p q : X) (b : Bool) (h : G) :
    regularDirectedTransport (torusTranslatedFluxAssignment p b h)
      (torusGraph_adj_right q.1 q.2) = 1 := by
  have hn₀ := torusRightEdge_ne_torusUpEdge q p
  have hn₁ := torusRightEdge_ne_torusUpEdge q (p.1+1,p.2)
  change Edge.ofAdj (torusGraph_adj_right q.1 q.2) ≠
    Edge.ofAdj (torusGraph_adj_up p.1 p.2) at hn₀
  change Edge.ofAdj (torusGraph_adj_right q.1 q.2) ≠
    Edge.ofAdj (torusGraph_adj_up (p.1+1) p.2) at hn₁
  simp [regularDirectedTransport, torusTranslatedFluxAssignment, hn₀, hn₁]

private theorem right_up_transport (p : X) (b : Bool) (h : G) :
    regularDirectedTransport (torusTranslatedFluxAssignment p b h)
      (torusGraph_adj_up (p.1+2) p.2) = 1 := by
  have hw := Fact.out (p := 7 < width)
  have h20 : (2 : ZMod width) ≠ 0 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := width) 2 0 (by norm_num; omega)).not.mpr (by norm_num : (2 : ℤ) ≠ 0)
  have h21 : (2 : ZMod width) ≠ 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := width) 2 1 (by norm_num; omega)).not.mpr (by norm_num : (2 : ℤ) ≠ 1)
  have he₀ : Edge.ofAdj (torusGraph_adj_up (p.1+2) p.2) ≠
      Edge.ofAdj (torusGraph_adj_up p.1 p.2) :=
    Edge.ofAdj_ne_of_endpoint_coordinates _ _ Prod.fst rfl (Or.inl (by simpa using h20))
  have he₁ : Edge.ofAdj (torusGraph_adj_up (p.1+2) p.2) ≠
      Edge.ofAdj (torusGraph_adj_up (p.1+1) p.2) :=
    Edge.ofAdj_ne_of_endpoint_coordinates _ _ Prod.fst rfl (Or.inl (by simpa using h21))
  simp [regularDirectedTransport, torusTranslatedFluxAssignment, he₀, he₁]

private theorem internal_eq (v : X) (g h : G) (b : Bool) (e : Edge Γₜ)
    (he : e.1.1 ∈ translatedTwoPlaquetteRegion (v.1 + 1, v.2 + 1) ∧
      e.1.2 ∈ translatedTwoPlaquetteRegion (v.1 + 1, v.2 + 1)) :
    rightStepFamily v g h b e =
      torusGaugedHorizontalFluxAssignment (v.1 + 1, v.2 + 1)
        (torusFirstRightStepGauge v g h) b h e := by
  let p : X := (v.1 + 1, v.2 + 1)
  have hw := Fact.out (p := 7 < width)
  have hh := Fact.out (p := 6 < height)
  have hx21 : (2 : ZMod width) ≠ 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := width) 2 1 (by norm_num; omega)).not.mpr (by norm_num : (2 : ℤ) ≠ 1)
  have hx31 : (3 : ZMod width) ≠ 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := width) 3 1 (by norm_num; omega)).not.mpr (by norm_num : (3 : ℤ) ≠ 1)
  have hx32 : (3 : ZMod width) ≠ 2 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := width) 3 2 (by norm_num; omega)).not.mpr (by norm_num : (3 : ℤ) ≠ 2)
  have hy20 : (2 : ZMod height) ≠ 0 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 2 0 (by norm_num; omega)).not.mpr (by norm_num : (2 : ℤ) ≠ 0)
  have hy21 : (2 : ZMod height) ≠ 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 2 1 (by norm_num; omega)).not.mpr (by norm_num : (2 : ℤ) ≠ 1)
  have hy2n : (2 : ZMod height) ≠ -1 := by
    simpa using (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
      (n := height) 2 (-1) (by norm_num; omega)).not.mpr (by norm_num : (2 : ℤ) ≠ -1)
  have hmem (i : Fin 6) :
      (p.1 + ((![0,1,2,2,1,0] i : ℕ) : ZMod width),
       p.2 + ((![0,0,0,1,1,1] i : ℕ) : ZMod height)) ∈ translatedTwoPlaquetteRegion p := by
    have H := (translatedTwoPlaquetteIso p i).2
    change (((![0,1,2,2,1,0] i : ℕ) : ZMod width) + p.1,
      ((![0,0,0,1,1,1] i : ℕ) : ZMod height) + p.2) ∈ _ at H
    simpa only [add_comm, Finset.mem_coe] using H
  have hrec {x y : X} (hxy : (Γₜ).Adj x y) (hx : x ∈ translatedTwoPlaquetteRegion p)
      (hy : y ∈ translatedTwoPlaquetteRegion p) :=
    regularDirectedTransport_eq_of_internal_reconstruction (translatedTwoPlaquetteRegion p)
      (torusFirstRightStepGauge v g h) (torusTranslatedFluxAssignment p b h)
      (torusGaugedHorizontalFluxAssignment p (torusFirstRightStepGauge v g h) b h)
      (fun f hf => by simp only [torusGaugedHorizontalFluxAssignment, dite_eq_left hf])
      hxy hx hy
  have hR (q : X) : regularDirectedTransport (rightStepFamily v g h b)
      (torusGraph_adj_right q.1 q.2) = torusSweptStringInitialRight v h q := by
    cases b
    exacts [torusSweptStringInitialOperators_right_transport v q g h,
      torusSweptStringRightStepOperators_right_transport v q g h]
  have hU (q : X) : regularDirectedTransport (rightStepFamily v g h b)
      (torusGraph_adj_up q.1 q.2) =
        if b ∧ q = (v.1 + 2, v.2 + 1) then g * h else torusSweptStringInitialUp v g q := by
    cases b
    · simpa [rightStepFamily] using torusSweptStringInitialOperators_up_transport v q g h
    · simpa [rightStepFamily] using torusSweptStringRightStepOperators_up_transport v q g h
  refine translatedTwoPlaquette_internal_eq_of_transports p (rightStepFamily v g h b)
    (torusGaugedHorizontalFluxAssignment p (torusFirstRightStepGauge v g h) b h)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ e he <;>
  [rw [hR (p.1,p.2), hrec (torusGraph_adj_right p.1 p.2)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 0)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 1),
      horizontal_transport p (p.1,p.2) _ h];
    rw [hU (p.1,p.2), hrec (torusGraph_adj_up p.1 p.2)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 0)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 5),
      (torusTranslatedFluxAssignment_up_transport p b h).1];
    rw [hR ((p.1+1),p.2), hrec (torusGraph_adj_right (p.1+1) p.2)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 1)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 2),
      horizontal_transport p ((p.1+1),p.2) _ h];
    rw [hU ((p.1+1),p.2), hrec (torusGraph_adj_up (p.1+1) p.2)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 1)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 4),
      (torusTranslatedFluxAssignment_up_transport p b h).2];
    rw [hU ((p.1+2),p.2), hrec (torusGraph_adj_up (p.1+2) p.2)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 2)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 3),
      right_up_transport p b h];
    rw [hR (p.1,(p.2+1)), hrec (torusGraph_adj_right p.1 (p.2+1))
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 5)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 4),
      horizontal_transport p (p.1,(p.2+1)) _ h];
    rw [hR ((p.1+1),(p.2+1)), hrec (torusGraph_adj_right (p.1+1) (p.2+1))
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 4)
      (by simpa [add_assoc, one_add_one_eq_two] using hmem 3),
      horizontal_transport p ((p.1+1),(p.2+1)) _ h]]
  all_goals
    cases b <;>
    norm_num [torusFirstRightStepGauge, torusSweptStringInitialRight,
      torusSweptStringInitialUp, p, add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx31,
      Ne.symm hx31, hx32, Ne.symm hx32, hy20, hy21, hy2n]

private theorem extension_eq (v : X) (g h : G) (b : Bool) (u : Edge Γₜ → G) :
    regularRegionBondExtension (translatedTwoPlaquetteRegion (v.1 + 1, v.2 + 1))
      (torusGaugedHorizontalFluxAssignment (v.1 + 1, v.2 + 1)
        (torusFirstRightStepGauge v g h) b h) u =
    regularRegionBondExtension (translatedTwoPlaquetteRegion (v.1 + 1, v.2 + 1))
      (rightStepFamily v g h b) u := by
  exact regularRegionBondExtension_congr_of_internal _ _ _ u
    (fun e he => (internal_eq v g h b e he).symm)

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- A fixed original-spin unitary effects the literal first rightward endpoint
step, retaining the partner string and every common exterior and crossing
operator. Source: SCP10, Theorem 6.16 and the four-endpoint route,
lines 2271–2305 and 2340–2423. -/
theorem IsGIsometric.exists_unitary_torusInitialStringRightPhysicalStep
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    let R := translatedTwoPlaquetteRegion (v.1 + 1, v.2 + 1)
    ∃ W : Matrix ({x : X // x ∈ R} → Fin d) ({x : X // x ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({x : X // x ∈ R} → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (g h : G) (u : Edge Γₜ → G)
        (θ : {e : Edge Γₜ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension R (torusSweptStringInitialOperators v g h) u))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension R (torusSweptStringRightStepOperators v g h) u))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (g h : G) (u : Edge Γₜ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension R (torusSweptStringInitialOperators v g h) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension R (torusSweptStringRightStepOperators v g h) u))) := by
  obtain ⟨W,hW,hglobal,hlocal,hact⟩ :=
    ha.exists_unitary_torusGaugedHorizontalFluxMove (v.1 + 1, v.2 + 1)
  refine ⟨W,hW,hglobal,?_,?_⟩
  · intro g h u θ
    have H := hlocal (torusFirstRightStepGauge v g h) false h u θ
    simp only [Bool.false_eq_true, ite_false] at H
    rw [extension_eq v g h false u, extension_eq v g h (!false) u] at H
    exact H
  · intro g h u
    have H := hact (torusFirstRightStepGauge v g h) false h u
    simp only [Bool.false_eq_true, ite_false] at H
    rw [extension_eq v g h false u, extension_eq v g h (!false) u] at H
    exact H

end TNLean.PEPS
