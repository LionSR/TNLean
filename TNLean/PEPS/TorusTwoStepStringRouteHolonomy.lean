/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSecondStringPhysicalCrossing
/-!
# Actual clockwise fluxes along the two-step endpoint route

The original endpoint, its rightward neighbour, and the upward neighbour of the
latter have fluxes (h,1,1), then (1,h,1), then (1,1,g h g⁻¹). These are computed
from the actual native bond assignments, including seam inversions. This is an
auxiliary part of SCP10, Section 6.6, lines 2361–2415, not a full braid.
-/
noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance routeFluxWidthSix : Fact (6 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeFluxHeightFive : Fact (5 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeFluxWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeFluxWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeFluxHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeFluxHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeFluxWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeFluxHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]
/-- The second step changes no upward transport.
Source: SCP10, the physical endpoint movement, lines 2271–2415. -/
theorem torusSecondStringCrossingOutput_up_transport (v p : X) (g h : G) :
    regularDirectedTransport (torusSecondStringCrossingOutput v g h)
      (torusGraph_adj_up p.1 p.2) =
      if p = (v.1 + 2, v.2 + 1) then g * h else torusSweptStringInitialUp v g p := by
  have he := torusSecondStringCrossingOutput_eq_of_ne v g h (torusUpEdge p)
    (torusRightEdge_ne_torusUpEdge (v.1 + 2, v.2 + 2) p).symm
  change torusSecondStringCrossingOutput v g h
      (Edge.ofAdj (torusGraph_adj_up p.1 p.2)) =
    torusSweptStringRightStepOperators v g h (Edge.ofAdj (torusGraph_adj_up p.1 p.2)) at he
  simpa only [regularDirectedTransport, he] using
    torusSweptStringRightStepOperators_up_transport v p g h
/-- Only the selected middle rightward transport is added in the second step.
Source: SCP10, the physical string crossing, lines 2361–2415. -/
theorem torusSecondStringCrossingOutput_right_transport (v p : X) (g h : G) :
    regularDirectedTransport (torusSecondStringCrossingOutput v g h)
      (torusGraph_adj_right p.1 p.2) =
      if p = (v.1 + 2, v.2 + 2) then g * h⁻¹ * g⁻¹
      else torusSweptStringInitialRight v h p := by
  by_cases hp : p = (v.1 + 2, v.2 + 2)
  · subst p
    simpa only [ite_true] using torusSecondStringCrossingOutput_middle_transport v g h
  · have he := torusSecondStringCrossingOutput_eq_of_ne v g h (torusRightEdge p)
      ((torusRightEdge_injective (width := width) (height := height)).ne hp)
    change torusSecondStringCrossingOutput v g h
        (Edge.ofAdj (torusGraph_adj_right p.1 p.2)) =
      torusSweptStringRightStepOperators v g h (Edge.ofAdj (torusGraph_adj_right p.1 p.2)) at he
    simpa only [regularDirectedTransport, he, ite_eq_right hp] using
      torusSweptStringRightStepOperators_right_transport v p g h
/-- The actual three plaquettes visited by the first two physical steps.
Source: SCP10, the four-endpoint movement construction, lines 2361–2415. -/
def torusTwoStepStringPlaquette (v : X) (i : Fin 3) : X :=
  ![(v.1 + 1, v.2 + 1), (v.1 + 2, v.2 + 1), (v.1 + 2, v.2 + 2)] i
omit [NeZero width] [NeZero height] in
private theorem route_coordinate_ne :
    (2 : ZMod width) ≠ 1 ∧ (3 : ZMod width) ≠ 2 ∧
    (2 : ZMod height) ≠ 0 ∧ (2 : ZMod height) ≠ 1 ∧
    (3 : ZMod height) ≠ 1 ∧ (3 : ZMod height) ≠ 0 ∧
    (2 : ZMod height) ≠ -1 ∧ (3 : ZMod height) ≠ -1 ∧
    (3 : ZMod height) ≠ 2 := by
  have hw := Fact.out (p := 7 < width)
  have hh := Fact.out (p := 6 < height)
  have hx21 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) 2 (1)
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ (1))
  have hx32 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) 3 (2)
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ (2))
  have hy20 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 2 (0)
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ (0))
  have hy21 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 2 (1)
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ (1))
  have hy31 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 3 (1)
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ (1))
  have hy30 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 3 (0)
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ (0))
  have hy2n := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 2 (-1)
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ (-1))
  have hy3n := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 3 (-1)
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ (-1))
  have hy32 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 3 2
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ 2)
  norm_num only at hx21 hx32 hy20 hy21 hy31 hy30 hy2n hy3n hy32
  exact ⟨hx21, hx32, hy20, hy21, hy31, hy30, hy2n, hy3n, hy32⟩
/-- The actual initial clockwise fluxes along the two-step route.
Source: SCP10, Section 6.6, lines 2361–2415. -/
theorem regularWalkHolonomy_torusTwoStepString_initial (v : X) (g h : G) (i : Fin 3) :
    regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusPlaquetteWalk (torusTwoStepStringPlaquette v i)).reverse = ![h, 1, 1] i := by
  obtain ⟨hx21, hx32, hy20, hy21, hy31, hy30, hy2n, hy3n, hy32⟩ :=
    route_coordinate_ne (width := width) (height := height)
  fin_cases i
  · change regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusPlaquetteWalk ((v.1 + 1, v.2 + 1) : X)).reverse = h
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringInitialOperators_right_transport v (v.1 + 1, v.2 + 1) g h,
      torusSweptStringInitialOperators_up_transport v (v.1 + 1 + 1, v.2 + 1) g h,
      torusSweptStringInitialOperators_right_transport v (v.1 + 1, v.2 + 1 + 1) g h,
      torusSweptStringInitialOperators_up_transport v (v.1 + 1, v.2 + 1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
  · change regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusPlaquetteWalk ((v.1 + 2, v.2 + 1) : X)).reverse = 1
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringInitialOperators_right_transport v (v.1 + 2, v.2 + 1) g h,
      torusSweptStringInitialOperators_up_transport v (v.1 + 2 + 1, v.2 + 1) g h,
      torusSweptStringInitialOperators_right_transport v (v.1 + 2, v.2 + 1 + 1) g h,
      torusSweptStringInitialOperators_up_transport v (v.1 + 2, v.2 + 1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
  · change regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusPlaquetteWalk ((v.1 + 2, v.2 + 2) : X)).reverse = 1
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringInitialOperators_right_transport v (v.1 + 2, v.2 + 2) g h,
      torusSweptStringInitialOperators_up_transport v (v.1 + 2 + 1, v.2 + 2) g h,
      torusSweptStringInitialOperators_right_transport v (v.1 + 2, v.2 + 2 + 1) g h,
      torusSweptStringInitialOperators_up_transport v (v.1 + 2, v.2 + 2) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
/-- The actual intermediate clockwise fluxes along the two-step route.
Source: SCP10, Section 6.6, lines 2361–2415. -/
theorem regularWalkHolonomy_torusTwoStepString_intermediate (v : X) (g h : G) (i : Fin 3) :
    regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusPlaquetteWalk (torusTwoStepStringPlaquette v i)).reverse = ![1, h, 1] i := by
  obtain ⟨hx21, hx32, hy20, hy21, hy31, hy30, hy2n, hy3n, hy32⟩ :=
    route_coordinate_ne (width := width) (height := height)
  fin_cases i
  · change regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusPlaquetteWalk ((v.1 + 1, v.2 + 1) : X)).reverse = 1
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringRightStepOperators_right_transport v (v.1 + 1, v.2 + 1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1 + 1 + 1, v.2 + 1) g h,
      torusSweptStringRightStepOperators_right_transport v (v.1 + 1, v.2 + 1 + 1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1 + 1, v.2 + 1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
  · change regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusPlaquetteWalk ((v.1 + 2, v.2 + 1) : X)).reverse = h
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringRightStepOperators_right_transport v (v.1 + 2, v.2 + 1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1 + 2 + 1, v.2 + 1) g h,
      torusSweptStringRightStepOperators_right_transport v (v.1 + 2, v.2 + 1 + 1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1 + 2, v.2 + 1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
  · change regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusPlaquetteWalk ((v.1 + 2, v.2 + 2) : X)).reverse = 1
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringRightStepOperators_right_transport v (v.1 + 2, v.2 + 2) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1 + 2 + 1, v.2 + 2) g h,
      torusSweptStringRightStepOperators_right_transport v (v.1 + 2, v.2 + 2 + 1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1 + 2, v.2 + 2) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
/-- The actual final clockwise fluxes along the two-step route.
Source: SCP10, Section 6.6, lines 2361–2415. -/
theorem regularWalkHolonomy_torusTwoStepString_final (v : X) (g h : G) (i : Fin 3) :
    regularWalkHolonomy (torusSecondStringCrossingOutput v g h)
      (torusPlaquetteWalk (torusTwoStepStringPlaquette v i)).reverse = ![1, 1, g * h * g⁻¹] i := by
  obtain ⟨hx21, hx32, hy20, hy21, hy31, hy30, hy2n, hy3n, hy32⟩ :=
    route_coordinate_ne (width := width) (height := height)
  fin_cases i
  · change regularWalkHolonomy (torusSecondStringCrossingOutput v g h)
      (torusPlaquetteWalk ((v.1 + 1, v.2 + 1) : X)).reverse = 1
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSecondStringCrossingOutput_right_transport v (v.1 + 1, v.2 + 1) g h,
      torusSecondStringCrossingOutput_up_transport v (v.1 + 1 + 1, v.2 + 1) g h,
      torusSecondStringCrossingOutput_right_transport v (v.1 + 1, v.2 + 1 + 1) g h,
      torusSecondStringCrossingOutput_up_transport v (v.1 + 1, v.2 + 1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
  · change regularWalkHolonomy (torusSecondStringCrossingOutput v g h)
      (torusPlaquetteWalk ((v.1 + 2, v.2 + 1) : X)).reverse = 1
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSecondStringCrossingOutput_right_transport v (v.1 + 2, v.2 + 1) g h,
      torusSecondStringCrossingOutput_up_transport v (v.1 + 2 + 1, v.2 + 1) g h,
      torusSecondStringCrossingOutput_right_transport v (v.1 + 2, v.2 + 1 + 1) g h,
      torusSecondStringCrossingOutput_up_transport v (v.1 + 2, v.2 + 1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
  · change regularWalkHolonomy (torusSecondStringCrossingOutput v g h)
      (torusPlaquetteWalk ((v.1 + 2, v.2 + 2) : X)).reverse = g * h * g⁻¹
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSecondStringCrossingOutput_right_transport v (v.1 + 2, v.2 + 2) g h,
      torusSecondStringCrossingOutput_up_transport v (v.1 + 2 + 1, v.2 + 2) g h,
      torusSecondStringCrossingOutput_right_transport v (v.1 + 2, v.2 + 2 + 1) g h,
      torusSecondStringCrossingOutput_up_transport v (v.1 + 2, v.2 + 2) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, Ne.symm hy21, hy31, hy30, hy2n, hy3n, hy32, mul_assoc]
/-- The two first-string endpoints and the distant second-string partner retain
all three actual clockwise fluxes in both stages. Source: SCP10, lines 2361–2415. -/
theorem regularWalkHolonomy_torusTwoStepString_partners (v : X) (g h : G) :
    (∀ i : Fin 3, regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusSweptPatchEndpointLoop v (![0, 1, 3] i)) = ![g⁻¹, g, h⁻¹] i) ∧
    (∀ i : Fin 3, regularWalkHolonomy (torusSecondStringCrossingOutput v g h)
      (torusSweptPatchEndpointLoop v (![0, 1, 3] i)) = ![g⁻¹, g, h⁻¹] i) := by
  have hw := Fact.out (p := 7 < width)
  have hh := Fact.out (p := 6 < height)
  have xn0 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (-1) (0)
    (by norm_num; omega)).mp (by decide : (-1 : ℤ) ≠ (0))
  have xn1 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (-1) (1)
    (by norm_num; omega)).mp (by decide : (-1 : ℤ) ≠ (1))
  have xn2 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (-1) (2)
    (by norm_num; omega)).mp (by decide : (-1 : ℤ) ≠ (2))
  have xn3 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (-1) (3)
    (by norm_num; omega)).mp (by decide : (-1 : ℤ) ≠ (3))
  have x02 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (0) (2)
    (by norm_num; omega)).mp (by decide : (0 : ℤ) ≠ (2))
  have x31 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (3) (1)
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ (1))
  have x32 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (3) (2)
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ (2))
  have x40 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (4) (0)
    (by norm_num; omega)).mp (by decide : (4 : ℤ) ≠ (0))
  have x41 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (4) (1)
    (by norm_num; omega)).mp (by decide : (4 : ℤ) ≠ (1))
  have x42 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (4) (2)
    (by norm_num; omega)).mp (by decide : (4 : ℤ) ≠ (2))
  have x43 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (4) (3)
    (by norm_num; omega)).mp (by decide : (4 : ℤ) ≠ (3))
  have x12 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) (1) (2)
    (by norm_num; omega)).mp (by decide : (1 : ℤ) ≠ (2))
  have yn20 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) (-2) (0)
    (by norm_num; omega)).mp (by decide : (-2 : ℤ) ≠ (0))
  have yn21 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) (-2) (1)
    (by norm_num; omega)).mp (by decide : (-2 : ℤ) ≠ (1))
  have yn22 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) (-2) (2)
    (by norm_num; omega)).mp (by decide : (-2 : ℤ) ≠ (2))
  have yn11 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) (-1) (1)
    (by norm_num; omega)).mp (by decide : (-1 : ℤ) ≠ (1))
  have yn12 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) (-1) (2)
    (by norm_num; omega)).mp (by decide : (-1 : ℤ) ≠ (2))
  have y12 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) (1) (2)
    (by norm_num; omega)).mp (by decide : (1 : ℤ) ≠ (2))
  norm_num only at xn0 xn1 xn2 xn3 x02 x31 x32 x40 x41
  norm_num only at x42 x43 x12 yn20 yn21 yn22 yn11 yn12 y12
  have x20 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) 2 0
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ 0)
  norm_num only at x20
  obtain ⟨hx21, _, _, hy21, _, _, _, _, _⟩ :=
    route_coordinate_ne (width := width) (height := height)
  constructor
  · intro i
    let p := torusSweptPatchEndpoint v (![0, 1, 3] i)
    change regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusPlaquetteWalk p).reverse = _
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringRightStepOperators_right_transport v p g h,
      torusSweptStringRightStepOperators_up_transport v (p.1 + 1, p.2) g h,
      torusSweptStringRightStepOperators_right_transport v (p.1, p.2 + 1) g h,
      torusSweptStringRightStepOperators_up_transport v p g h]
    dsimp only [p]
    simp only [torusSweptPatchEndpoint_eq]
    fin_cases i <;>
      norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
        add_assoc, sub_eq_add_neg,
        xn0, xn1, xn2, xn3, x02, x31, x32, x40, x41,
        x42, x43, x12, yn20, yn21, yn22, yn11, yn12, y12, x20, hx21, hy21]
  · intro i
    let p := torusSweptPatchEndpoint v (![0, 1, 3] i)
    change regularWalkHolonomy (torusSecondStringCrossingOutput v g h)
      (torusPlaquetteWalk p).reverse = _
    rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSecondStringCrossingOutput_right_transport v p g h,
      torusSecondStringCrossingOutput_up_transport v (p.1 + 1, p.2) g h,
      torusSecondStringCrossingOutput_right_transport v (p.1, p.2 + 1) g h,
      torusSecondStringCrossingOutput_up_transport v p g h]
    dsimp only [p]
    simp only [torusSweptPatchEndpoint_eq]
    fin_cases i <;>
      norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
        add_assoc, sub_eq_add_neg,
        xn0, xn1, xn2, xn3, x02, x31, x32, x40, x41,
        x42, x43, x12, yn20, yn21, yn22, yn11, yn12, y12, x20, hx21, hy21]
end TNLean.PEPS
