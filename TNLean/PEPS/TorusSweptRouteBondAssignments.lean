/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDirectedBondUpdate
import TNLean.PEPS.TorusSweptPhysicalEndpointRoute
import TNLean.PEPS.TorusSweptStringDeformation
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.Algebra.ZModSmallDifference
import TNLean.PEPS.RegularConnectorHolonomy
import TNLean.Algebra.ConjClassesConjugation
import Mathlib.GroupTheory.Commutator.Basic
/-!
# Literal ordered-bond assignments along the twelve-step endpoint route

Each coefficient update is computed from the actual preceding assignment and
retains every other bond, including the partner strings. The four directions
vacate the source plaquette by group multiplication. Physical implementation
is a separate assertion and is not supplied as a hypothesis here.
Source: SCP10, arXiv:1001.3807, Section 6.6, lines 2340–2423.
**Scope restriction (finite torus and regular action):** The width is at least
eight and the height at least seven. Every position and both periodic seams
are allowed. The results concern the displayed endpoint route and its original
physical contractions. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance routeBondsWidthSix : Fact (6 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeBondsHeightFive : Fact (5 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeBondsWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeBondsHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeBondsWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeBondsHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeBondsWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeBondsHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]
/-- Right, up, left, and down are numbered `0,1,2,3`.
Source: SCP10, the physical endpoint route, lines 2340–2423. -/
def sweptPhysicalBRouteDirection : Fin 12 → Fin 4 :=
  ![0, 1, 0, 0, 3, 3, 2, 2, 2, 2, 3, 3]
/-- One literal shared-edge update, determined from the actual source plaquette.
Source: SCP10, elementary movement in Section 6.6, lines 2340–2423.
This coefficient operation alone does not assert a physical unitary. -/
def torusVacatingPlaquetteMove (direction : Fin 4) (p : X) (u : Edge Γₜ → G) :
    Edge Γₜ → G :=
  let B := torusDirectedBondTransport false u p
  let V := torusDirectedBondTransport true u (p.1 + 1, p.2)
  let T := torusDirectedBondTransport false u (p.1, p.2 + 1)
  let L := torusDirectedBondTransport true u p
  if direction = 0 then torusDirectedBondUpdate true (p.1 + 1, p.2) (T * L * B⁻¹) u
  else if direction = 1 then torusDirectedBondUpdate false (p.1, p.2 + 1) (V * B * L⁻¹) u
  else if direction = 2 then torusDirectedBondUpdate true p (T⁻¹ * V * B) u
  else torusDirectedBondUpdate false p (V⁻¹ * T * L) u
/-- The actual successive assignment, initialized by the four-endpoint strings.
Source: SCP10, the endpoint route, lines 2340–2423. -/
def torusSweptPhysicalRouteOperators (v : X) (g h : G) : ℕ → Edge Γₜ → G
  | 0 => torusSweptStringInitialOperators v g h
  | n + 1 => if hn : n < 12 then
      torusVacatingPlaquetteMove (sweptPhysicalBRouteDirection ⟨n, hn⟩)
        (torusSweptPhysicalBRouteVertex v ⟨n, by omega⟩)
        (torusSweptPhysicalRouteOperators v g h n)
    else torusSweptPhysicalRouteOperators v g h n
private theorem operators_zero (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 0 = torusSweptStringInitialOperators v g h := rfl
private theorem clockwise_eq (u : Edge Γₜ → G) (p : X) :
    regularWalkHolonomy u (torusPlaquetteWalk p).reverse =
      (torusDirectedBondTransport false u p)⁻¹ *
        (torusDirectedBondTransport true u (p.1 + 1, p.2))⁻¹ *
        torusDirectedBondTransport false u (p.1, p.2 + 1) *
        torusDirectedBondTransport true u p :=
  regularWalkHolonomy_torusPlaquetteWalk_reverse u p
private theorem initial_transport (axis : Bool) (v p : X) (g h : G) :
    torusDirectedBondTransport axis (torusSweptStringInitialOperators v g h) p =
      if axis then torusSweptStringInitialUp v g p else torusSweptStringInitialRight v h p := by
  cases axis
  · exact torusSweptStringInitialOperators_right_transport v p g h
  · exact torusSweptStringInitialOperators_up_transport v p g h
/-- Every one of the four literal updates vacates its actual source plaquette.
Source: SCP10, elementary flux movement in Section 6.6, lines 2340–2423. -/
theorem regularWalkHolonomy_torusVacatingPlaquetteMove (direction : Fin 4)
    (p : X) (u : Edge Γₜ → G) :
    regularWalkHolonomy (torusVacatingPlaquetteMove direction p u)
      (torusPlaquetteWalk p).reverse = 1 := by
  have hx : p.1 + 1 ≠ p.1 := by simp
  have hy : p.2 + 1 ≠ p.2 := by simp
  rw [clockwise_eq]
  fin_cases direction <;>
    simp [torusVacatingPlaquetteMove, torusDirectedBondTransport_update, Prod.ext_iff,
      hx, hy, Ne.symm hx, Ne.symm hy] <;> group
private theorem x_eq (v : X) (p : Fin 7 × Fin 6) (c : ℤ)
    (hc : -1 ≤ c ∧ c ≤ 5) :
    (torusSweptPhysicalRouteCoordinate v p).1 = v.1 + (c : ZMod width) ↔
      (p.1.val : ℤ) = c + 1 := by
  have hp := p.1.isLt
  have hw := Fact.out (p := 7 < width)
  have hd : ((c + 1) - (p.1.val : ℤ)).natAbs < width := by
    omega
  have he := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (p.1.val : ℤ) (c + 1) hd
  have hrew : (torusSweptPhysicalRouteCoordinate v p).1 = v.1 + (c : ZMod width) ↔
      ((p.1.val : ℤ) : ZMod width) = ((c + 1 : ℤ) : ZMod width) := by
    simp only [torusSweptPhysicalRouteCoordinate, translate_apply, Int.cast_add,
      Int.cast_one, Int.cast_natCast]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  exact hrew.trans he
private theorem y_eq (v : X) (p : Fin 7 × Fin 6) (c : ℤ)
    (hc : -2 ≤ c ∧ c ≤ 3) :
    (torusSweptPhysicalRouteCoordinate v p).2 = v.2 + (c : ZMod height) ↔
      (p.2.val : ℤ) = c + 2 := by
  have hp := p.2.isLt
  have hh := Fact.out (p := 6 < height)
  have hd : ((c + 2) - (p.2.val : ℤ)).natAbs < height := by
    omega
  have he := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (p.2.val : ℤ) (c + 2) hd
  have hrew : (torusSweptPhysicalRouteCoordinate v p).2 = v.2 + (c : ZMod height) ↔
      ((p.2.val : ℤ) : ZMod height) = ((c + 2 : ℤ) : ZMod height) := by
    simp only [torusSweptPhysicalRouteCoordinate, translate_apply, Int.cast_add,
      Int.cast_ofNat, Int.cast_natCast]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  exact hrew.trans he
private theorem initial_coordinate_transport (axis : Bool) (v : X)
    (p : Fin 7 × Fin 6) (g h : G) :
    torusDirectedBondTransport axis (torusSweptStringInitialOperators v g h)
      (torusSweptPhysicalRouteCoordinate v p) =
      if axis then
        if (p.1.val : ℤ) ∈ ({1,2,3,4} : Finset ℤ) ∧ (p.2.val : ℤ) = 3 then g else 1
      else if (p.1.val : ℤ) = 2 ∧ (p.2.val : ℤ) ∈ ({1,2,3} : Finset ℤ) then h⁻¹ else 1 := by
  have hx0 := x_eq v p 0 (by omega)
  have hx1 := x_eq v p 1 (by omega)
  have hx2 := x_eq v p 2 (by omega)
  have hx3 := x_eq v p 3 (by omega)
  have hym := y_eq v p (-1) (by omega)
  have hy0 := y_eq v p 0 (by omega)
  have hy1 := y_eq v p 1 (by omega)
  norm_num at hx0 hx1 hx2 hx3 hym hy0 hy1
  cases axis <;>
    simp [initial_transport, torusSweptStringInitialRight, torusSweptStringInitialUp,
      sub_eq_add_neg, hx0, hx1, hx2, hx3, hym, hy0, hy1]
private theorem coordinate_east (v : X) (p : Fin 7 × Fin 6) (hx : p.1.val + 1 < 7) :
    ((torusSweptPhysicalRouteCoordinate v p).1 + 1,
      (torusSweptPhysicalRouteCoordinate v p).2) =
      torusSweptPhysicalRouteCoordinate v (⟨p.1.val + 1, hx⟩, p.2) := by
  ext <;> simp [torusSweptPhysicalRouteCoordinate, translate_apply, Nat.cast_add]
  all_goals ring
private theorem coordinate_north (v : X) (p : Fin 7 × Fin 6) (hy : p.2.val + 1 < 6) :
    ((torusSweptPhysicalRouteCoordinate v p).1,
      (torusSweptPhysicalRouteCoordinate v p).2 + 1) =
      torusSweptPhysicalRouteCoordinate v (p.1, ⟨p.2.val + 1, hy⟩) := by
  ext <;> simp [torusSweptPhysicalRouteCoordinate, translate_apply, Nat.cast_add]
  all_goals ring
private theorem coordinate_inj (v : X) (p q : Fin 7 × Fin 6) :
    torusSweptPhysicalRouteCoordinate v p = torusSweptPhysicalRouteCoordinate v q ↔ p = q :=
  (torusSweptPhysicalRouteCoordinate_injective v).eq_iff
private theorem step_zero (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 1 =
      torusDirectedBondUpdate true (torusSweptPhysicalRouteCoordinate v (3,3)) (g*h)
        (torusSweptPhysicalRouteOperators v g h 0) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 0 (torusSweptPhysicalRouteCoordinate v (2,3)) _ = _
  simp only [torusVacatingPlaquetteMove, ite_true]
  rw [coordinate_east v (2,3) (by decide), coordinate_north v (2,3) (by decide)]
  simp [torusSweptPhysicalRouteOperators, initial_coordinate_transport]
private theorem step_1 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 2 =
      torusDirectedBondUpdate false (torusSweptPhysicalRouteCoordinate v (3,4))
        (g*h⁻¹*g⁻¹) (torusSweptPhysicalRouteOperators v g h 1) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 1 (torusSweptPhysicalRouteCoordinate v (3,3)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (3,3) (by decide), coordinate_north v (3,3) (by decide)]
  congr 1
  simp only [step_zero, torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
  group
private theorem step_2 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 3 =
      torusDirectedBondUpdate true (torusSweptPhysicalRouteCoordinate v (4,4))
        (g*h*g⁻¹) (torusSweptPhysicalRouteOperators v g h 2) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 0 (torusSweptPhysicalRouteCoordinate v (3,4)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (3,4) (by decide), coordinate_north v (3,4) (by decide)]
  congr 1
  simp only [step_zero, step_1, torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
  group
private theorem step_3 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 4 =
      torusDirectedBondUpdate true (torusSweptPhysicalRouteCoordinate v (5,4))
        (g*h*g⁻¹) (torusSweptPhysicalRouteOperators v g h 3) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 0 (torusSweptPhysicalRouteCoordinate v (4,4)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (4,4) (by decide), coordinate_north v (4,4) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
private theorem step_4 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 5 =
      torusDirectedBondUpdate false (torusSweptPhysicalRouteCoordinate v (5,4))
        (g*h*g⁻¹) (torusSweptPhysicalRouteOperators v g h 4) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 3 (torusSweptPhysicalRouteCoordinate v (5,4)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (5,4) (by decide), coordinate_north v (5,4) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
private theorem step_5 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 6 =
      torusDirectedBondUpdate false (torusSweptPhysicalRouteCoordinate v (5,3))
        (g*h*g⁻¹) (torusSweptPhysicalRouteOperators v g h 5) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 3 (torusSweptPhysicalRouteCoordinate v (5,3)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (5,3) (by decide), coordinate_north v (5,3) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, step_4, torusDirectedBondTransport_update,
    coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
private theorem step_6 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 7 =
      torusDirectedBondUpdate true (torusSweptPhysicalRouteCoordinate v (5,2))
        (g*h⁻¹*g⁻¹) (torusSweptPhysicalRouteOperators v g h 6) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 2 (torusSweptPhysicalRouteCoordinate v (5,2)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (5,2) (by decide), coordinate_north v (5,2) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, step_4, step_5,
    torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
  group
private theorem step_7 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 8 =
      torusDirectedBondUpdate true (torusSweptPhysicalRouteCoordinate v (4,2))
        (g*h⁻¹*g⁻¹) (torusSweptPhysicalRouteOperators v g h 7) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 2 (torusSweptPhysicalRouteCoordinate v (4,2)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (4,2) (by decide), coordinate_north v (4,2) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, step_4, step_5, step_6,
    torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
private theorem step_8 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 9 =
      torusDirectedBondUpdate true (torusSweptPhysicalRouteCoordinate v (3,2))
        (g*h⁻¹*g⁻¹) (torusSweptPhysicalRouteOperators v g h 8) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 2 (torusSweptPhysicalRouteCoordinate v (3,2)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (3,2) (by decide), coordinate_north v (3,2) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, step_4, step_5, step_6, step_7,
    torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
private theorem step_9 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 10 =
      torusDirectedBondUpdate true (torusSweptPhysicalRouteCoordinate v (2,2))
        (h*g*h⁻¹*g⁻¹*h⁻¹) (torusSweptPhysicalRouteOperators v g h 9) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 2 (torusSweptPhysicalRouteCoordinate v (2,2)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (2,2) (by decide), coordinate_north v (2,2) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, step_4, step_5, step_6, step_7, step_8,
    torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
  group
private theorem step_10 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 11 =
      torusDirectedBondUpdate false (torusSweptPhysicalRouteCoordinate v (1,2))
        (h*g*h*g⁻¹*h⁻¹) (torusSweptPhysicalRouteOperators v g h 10) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 3 (torusSweptPhysicalRouteCoordinate v (1,2)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (1,2) (by decide), coordinate_north v (1,2) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, step_4, step_5, step_6, step_7, step_8, step_9,
    torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
  group
private theorem step_11 (v : X) (g h : G) :
    torusSweptPhysicalRouteOperators v g h 12 =
      torusDirectedBondUpdate false (torusSweptPhysicalRouteCoordinate v (1,1))
        (h*g*h*g⁻¹*h⁻¹) (torusSweptPhysicalRouteOperators v g h 11) := by
  conv_lhs => rw [torusSweptPhysicalRouteOperators]
  change torusVacatingPlaquetteMove 3 (torusSweptPhysicalRouteCoordinate v (1,1)) _ = _
  simp only [torusVacatingPlaquetteMove, Fin.reduceEq, reduceIte]
  rw [coordinate_east v (1,1) (by decide), coordinate_north v (1,1) (by decide)]
  congr 1
  simp only [step_zero, step_1, step_2, step_3, step_4, step_5, step_6, step_7, step_8, step_9,
    step_10, torusDirectedBondTransport_update, coordinate_inj,
    operators_zero, initial_coordinate_transport]
  norm_num
private def routeCoordinates : Fin 13 → Fin 7 × Fin 6 :=
  ![(2,3),(3,3),(3,4),(4,4),(5,4),(5,3),(5,2),
    (4,2),(3,2),(2,2),(1,2),(1,1),(1,0)]
private theorem routeVertex_eq_coordinate (v : X) (i : Fin 13) :
    torusSweptPhysicalBRouteVertex v i =
      torusSweptPhysicalRouteCoordinate v (routeCoordinates i) := by
  fin_cases i <;> rfl
private def updateAxis : Fin 12 → Bool :=
  ![true,false,true,true,false,false,true,true,true,true,false,false]
private def updatePoint : Fin 12 → Fin 7 × Fin 6 :=
  ![(3,3),(3,4),(4,4),(5,4),(5,4),(5,3),(5,2),(4,2),(3,2),(2,2),(1,2),(1,1)]
private def updateLabel (g h : G) : Fin 12 → G :=
  ![g*h, g*h⁻¹*g⁻¹, g*h*g⁻¹, g*h*g⁻¹, g*h*g⁻¹, g*h*g⁻¹,
    g*h⁻¹*g⁻¹, g*h⁻¹*g⁻¹, g*h⁻¹*g⁻¹, h*g*h⁻¹*g⁻¹*h⁻¹,
    h*g*h*g⁻¹*h⁻¹, h*g*h*g⁻¹*h⁻¹]
private theorem operators_step_table (v : X) (g h : G) (i : Fin 12) :
    torusSweptPhysicalRouteOperators v g h (i.val + 1) =
      torusDirectedBondUpdate (updateAxis i)
        (torusSweptPhysicalRouteCoordinate v (updatePoint i)) (updateLabel g h i)
        (torusSweptPhysicalRouteOperators v g h i.val) := by
  fin_cases i
  · exact step_zero v g h
  · exact step_1 v g h
  · exact step_2 v g h
  · exact step_3 v g h
  · exact step_4 v g h
  · exact step_5 v g h
  · exact step_6 v g h
  · exact step_7 v g h
  · exact step_8 v g h
  · exact step_9 v g h
  · exact step_10 v g h
  · exact step_11 v g h
private def referenceOperators (v : X) (g h : G) : ℕ → Edge Γₜ → G
  | 0 => torusSweptStringInitialOperators v g h
  | n + 1 => if hn : n < 12 then
      torusDirectedBondUpdate (updateAxis ⟨n,hn⟩)
        (torusSweptPhysicalRouteCoordinate v (updatePoint ⟨n,hn⟩))
        (updateLabel g h ⟨n,hn⟩) (referenceOperators v g h n)
    else referenceOperators v g h n
private theorem operators_eq_reference (v : X) (g h : G) (n : ℕ) (hn : n ≤ 12) :
    torusSweptPhysicalRouteOperators v g h n = referenceOperators v g h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [operators_step_table v g h ⟨n, by omega⟩, referenceOperators]
    simp only [show n < 12 by omega, dite_true, ih (by omega)]
private theorem coordinate_clockwise (v : X) (u : Edge Γₜ → G)
    (p : Fin 7 × Fin 6) (hx : p.1.val + 1 < 7) (hy : p.2.val + 1 < 6) :
    regularWalkHolonomy u (torusPlaquetteWalk
      (torusSweptPhysicalRouteCoordinate v p)).reverse =
      (torusDirectedBondTransport false u (torusSweptPhysicalRouteCoordinate v p))⁻¹ *
        (torusDirectedBondTransport true u
          (torusSweptPhysicalRouteCoordinate v (⟨p.1.val + 1,hx⟩,p.2)))⁻¹ *
        torusDirectedBondTransport false u
          (torusSweptPhysicalRouteCoordinate v (p.1,⟨p.2.val + 1,hy⟩)) *
        torusDirectedBondTransport true u (torusSweptPhysicalRouteCoordinate v p) := by
  rw [clockwise_eq, coordinate_east v p hx, coordinate_north v p hy]
/-- Each target is vacant in the actual preceding assignment of the twelve-step route.
Source: SCP10, the successive flux motion in Section 6.6, lines 2340–2423.
The conclusion is derived from the recursive bond coefficients, not from an assumed table. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_target_vacancy
    (v : X) (g h : G) (i : Fin 12) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h i.val)
      (torusPlaquetteWalk (torusSweptPhysicalBRouteVertex v i.succ)).reverse = 1 := by
  rw [routeVertex_eq_coordinate]
  fin_cases i <;> rw [coordinate_clockwise v _ _ (by decide) (by decide)]
  all_goals rw [operators_eq_reference v g h _ (by omega)]
  · simp [routeCoordinates, referenceOperators, initial_coordinate_transport]
  all_goals
    simp [routeCoordinates, referenceOperators, updateAxis, updatePoint, updateLabel,
      torusDirectedBondTransport_update, coordinate_inj, initial_coordinate_transport]
/-- The actual moving clockwise flux at each successive base, including its
change of based representative when the retained partner string is crossed.
Source: SCP10, the endpoint route and flux alignment, lines 2340–2423. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_movingFlux
    (v : X) (g h : G) (i : Fin 13) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h i.val)
      (torusPlaquetteWalk (torusSweptPhysicalBRouteVertex v i)).reverse =
      ![h,h,g*h*g⁻¹,g*h*g⁻¹,g*h*g⁻¹,g*h*g⁻¹,g*h*g⁻¹,g*h*g⁻¹,g*h*g⁻¹,
        h*g*h*g⁻¹*h⁻¹,h*g*h*g⁻¹*h⁻¹,h*g*h*g⁻¹*h⁻¹,h*g*h*g⁻¹*h⁻¹] i := by
  rw [routeVertex_eq_coordinate]
  fin_cases i <;> rw [coordinate_clockwise v _ _ (by decide) (by decide)]
  all_goals rw [operators_eq_reference v g h _ (by omega)]
  · simp [routeCoordinates, referenceOperators, initial_coordinate_transport]
  all_goals
    simp [routeCoordinates, referenceOperators, updateAxis, updatePoint, updateLabel,
      torusDirectedBondTransport_update, coordinate_inj, initial_coordinate_transport]
  all_goals group
/-- The final endpoint bases retain the three stationary partners and replace
B1 by the end of its actual twelve-step route. Source: SCP10, lines 2340–2423. -/
def torusSweptPhysicalRouteFinalEndpoint (v : X) (i : Fin 4) : X :=
  if i = 2 then torusSweptPhysicalBRouteVertex v 12 else torusSweptPatchEndpoint v i
/-- The four final based clockwise fluxes, before transporting partner loops
along their connecting paths. Source: SCP10, flux alignment, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_finalEndpoints
    (v : X) (g h : G) (i : Fin 4) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusPlaquetteWalk (torusSweptPhysicalRouteFinalEndpoint v i)).reverse =
      ![g⁻¹,g,h*g*h*g⁻¹*h⁻¹,h⁻¹] i := by
  fin_cases i
  · change regularWalkHolonomy _ (torusPlaquetteWalk
      (torusSweptPhysicalRouteCoordinate v (0,3))).reverse = g⁻¹
    rw [coordinate_clockwise v _ _ (by decide) (by decide),
      operators_eq_reference v g h 12 (by omega)]
    simp [referenceOperators, updateAxis, updatePoint, updateLabel,
      torusDirectedBondTransport_update, coordinate_inj, initial_coordinate_transport]
  · change regularWalkHolonomy _ (torusPlaquetteWalk
      (torusSweptPhysicalRouteCoordinate v (4,3))).reverse = g
    rw [coordinate_clockwise v _ _ (by decide) (by decide),
      operators_eq_reference v g h 12 (by omega)]
    simp [referenceOperators, updateAxis, updatePoint, updateLabel,
      torusDirectedBondTransport_update, coordinate_inj, initial_coordinate_transport]
  · exact regularWalkHolonomy_torusSweptPhysicalRoute_movingFlux v g h 12
  · change regularWalkHolonomy _ (torusPlaquetteWalk
      (torusSweptPhysicalRouteCoordinate v (2,0))).reverse = h⁻¹
    rw [coordinate_clockwise v _ _ (by decide) (by decide),
      operators_eq_reference v g h 12 (by omega)]
    simp [referenceOperators, updateAxis, updatePoint, updateLabel,
      torusDirectedBondTransport_update, coordinate_inj, initial_coordinate_transport]
private theorem coordinate_integer_offsets (v : X) (p : Fin 7 × Fin 6) :
    torusSweptPhysicalRouteCoordinate v p =
      (v.1 + (((p.1.val : ℤ) - 1 : ℤ) : ZMod width),
        v.2 + (((p.2.val : ℤ) - 2 : ℤ) : ZMod height)) := by
  ext <;> simp [torusSweptPhysicalRouteCoordinate, translate_apply] <;> ring
/-- The retained actual A connector changes even though both of its based
endpoint fluxes are stationary. Source: SCP10, joint-flux alignment, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_finalConnectorA (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPatchConnectorA v) = h⁻¹ * g⁻¹ := by
  rw [regularWalkHolonomy_torusSweptPatchConnectorA]
  change (torusDirectedBondTransport true _ (v.1+3,v.2+1))⁻¹ *
    torusDirectedBondTransport false _ (v.1+2,v.2+2) *
    torusDirectedBondTransport false _ (v.1+1,v.2+2) *
    torusDirectedBondTransport false _ (v.1,v.2+2) *
    torusDirectedBondTransport false _ (v.1-1,v.2+2) *
    torusDirectedBondTransport true _ (v.1-1,v.2+1) = h⁻¹*g⁻¹
  have h43 := coordinate_integer_offsets v (4,3)
  have h34 := coordinate_integer_offsets v (3,4)
  have h24 := coordinate_integer_offsets v (2,4)
  have h14 := coordinate_integer_offsets v (1,4)
  have h04 := coordinate_integer_offsets v (0,4)
  have h03 := coordinate_integer_offsets v (0,3)
  norm_num at h43 h34 h24 h14 h04 h03
  simp only [sub_eq_add_neg]
  rw [← h43, ← h34, ← h24, ← h14, ← h04, ← h03,
    operators_eq_reference v g h 12 (by omega)]
  simp [referenceOperators, updateAxis, updatePoint, updateLabel,
    torusDirectedBondTransport_update, coordinate_inj, initial_coordinate_transport, mul_assoc]
/-- The actual partner-first A joint loop is based at the unchanged left endpoint.
Source: SCP10, partner alignment after braiding, lines 2387–2415. -/
def torusSweptPhysicalRouteAJointLoop (v : X) :
    (Γₜ).Walk (torusSweptPatchEndpoint v 0) (torusSweptPatchEndpoint v 0) :=
  (((torusSweptPatchConnectorA v).append (torusSweptPatchEndpointLoop v 1)).append
    (torusSweptPatchConnectorA v).reverse).append (torusSweptPatchEndpointLoop v 0)
/-- The actual final A comparison records the changed connector, although its
right endpoint retains based flux `g`. Source: SCP10, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_AJointLoop (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPhysicalRouteAJointLoop v) = h*g*h⁻¹*g⁻¹ := by
  have h0 := regularWalkHolonomy_torusSweptPhysicalRoute_finalEndpoints v g h 0
  have h1 := regularWalkHolonomy_torusSweptPhysicalRoute_finalEndpoints v g h 1
  change regularWalkHolonomy _ (torusSweptPatchEndpointLoop v 0) = g⁻¹ at h0
  change regularWalkHolonomy _ (torusSweptPatchEndpointLoop v 1) = g at h1
  rw [torusSweptPhysicalRouteAJointLoop, regularWalkHolonomy_append,
    regularWalkHolonomy_transportLoop, regularWalkHolonomy_torusSweptPhysicalRoute_finalConnectorA,
    h0, h1]
  group
/-- The final neighbouring B partners are compared along the actual rightward
edge from the route endpoint. Source: SCP10, partner reunion, lines 2387–2415. -/
def torusSweptPhysicalRouteReunionConnector (v : X) :
    (Γₜ).Walk (v.1,v.2-2) (v.1+1,v.2-2) :=
  .cons (torusGraph_adj_right v.1 (v.2-2)) .nil
/-- The final B reunion connector has literal identity transport.
Source: SCP10, actual partner alignment, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_reunionConnector (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPhysicalRouteReunionConnector v) = 1 := by
  simp only [torusSweptPhysicalRouteReunionConnector, regularWalkHolonomy_cons,
    regularWalkHolonomy_nil, one_mul]
  change torusDirectedBondTransport false _ (v.1,v.2-2) = 1
  have h10 := coordinate_integer_offsets v (1,0)
  norm_num at h10
  simp only [sub_eq_add_neg]
  rw [← h10, operators_eq_reference v g h 12 (by omega)]
  simp [referenceOperators, updateAxis, updatePoint, updateLabel,
    torusDirectedBondTransport_update, coordinate_inj, initial_coordinate_transport]
/-- Traverse the remote B partner loop along the reunion connector first, then
traverse the moving loop. The base is the final moving endpoint `(0,-2)` relative
to the initial patch. Source: SCP10, reunion joint flux, lines 2387–2415. -/
def torusSweptPhysicalRouteBReunionLoop (v : X) :
    (Γₜ).Walk (v.1,v.2-2) (v.1,v.2-2) :=
  (((torusSweptPhysicalRouteReunionConnector v).append
    (torusPlaquetteWalk (v.1+1,v.2-2)).reverse).append
      (torusSweptPhysicalRouteReunionConnector v).reverse).append
        (torusPlaquetteWalk (v.1,v.2-2)).reverse
/-- The final actual B joint flux is a conjugate of the commutator; its exact
based representative retains the partner-string crossing.
Source: SCP10, the joint-flux alignment discussion, lines 2387–2415.
This coefficient calculation does not itself assert physical implementation of all steps. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_BReunionLoop (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPhysicalRouteBReunionLoop v) = h*(g*h*g⁻¹*h⁻¹)*h⁻¹ := by
  have hm := regularWalkHolonomy_torusSweptPhysicalRoute_movingFlux v g h 12
  rw [torusSweptPhysicalBRoute_end] at hm
  change regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
    (torusPlaquetteWalk (v.1,v.2-2)).reverse = h*g*h*g⁻¹*h⁻¹ at hm
  have hp := regularWalkHolonomy_torusSweptPhysicalRoute_finalEndpoints v g h 3
  change regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
    (torusPlaquetteWalk (torusSweptPatchEndpoint v 3)).reverse = h⁻¹ at hp
  rw [torusSweptPatchEndpoint_eq] at hp
  change regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
    (torusPlaquetteWalk (v.1+1,v.2-2)).reverse = h⁻¹ at hp
  rw [torusSweptPhysicalRouteBReunionLoop, regularWalkHolonomy_append,
    regularWalkHolonomy_transportLoop, regularWalkHolonomy_torusSweptPhysicalRoute_reunionConnector,
    hm, hp]
  simp only [inv_one, one_mul, mul_one]
  group
/-- The transported A1 partner, compared at the actual A2 base along the
retained connector, records its backreaction. Source: SCP10, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_transportedAPartner
    (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (((torusSweptPatchConnectorA v).append (torusSweptPatchEndpointLoop v 1)).append
        (torusSweptPatchConnectorA v).reverse) = g*h*g*h⁻¹*g⁻¹ := by
  have h1 := regularWalkHolonomy_torusSweptPhysicalRoute_finalEndpoints v g h 1
  change regularWalkHolonomy _ (torusSweptPatchEndpointLoop v 1) = g at h1
  rw [regularWalkHolonomy_transportLoop,
    regularWalkHolonomy_torusSweptPhysicalRoute_finalConnectorA, h1]
  group
/-- The actual reunion joint loop has the conjugacy class of the commutator.
Source: SCP10, joint-flux detection following the route, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_BReunionLoop_conjClass
    (v : X) (g h : G) :
    ConjClasses.mk (regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPhysicalRouteBReunionLoop v)) = ConjClasses.mk (g*h*g⁻¹*h⁻¹) := by
  rw [regularWalkHolonomy_torusSweptPhysicalRoute_BReunionLoop]
  exact ConjClasses.mk_conjugate (g*h*g⁻¹*h⁻¹) h
/-- The derived reunion loop has trivial joint flux precisely when the two
initial flux labels commute. Source: SCP10, flux detection, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPhysicalRoute_BReunionLoop_eq_one_iff
    (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPhysicalRouteBReunionLoop v) = 1 ↔ Commute g h := by
  rw [regularWalkHolonomy_torusSweptPhysicalRoute_BReunionLoop,
    mul_inv_eq_one, mul_eq_left, ← commutatorElement_def,
    commutatorElement_eq_one_iff_commute]
end TNLean.PEPS
