/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSweptStringDeformation
import TNLean.PEPS.TorusSweptPatchEndpointGeometry
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.Algebra.ZModSmallDifference

/-!
# Four actual endpoint holonomies of the swept string presentations

The clockwise loops use the finite twenty-site completion of the source
figure. Their initial values are obtained from the literal native bond table;
vertex-gauge telescoping then determines the two swept presentations.

Source: SCP10, arXiv:1001.3807, lines 2361–2386 and the figure
`fluxon-braiding-virtuallevel`.

**Scope restriction (finite torus endpoint loops):** Width at least seven and
height at least six distinguish all four actual partner loops. The conclusions
describe a change of gauge presentation of the same actual closed contraction,
not a physical braiding operation. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/


namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (6 < width)] [Fact (5 < height)]
local instance sweptEndpointWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptEndpointHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local instance sweptEndpointWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptEndpointHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local instance sweptEndpointWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptEndpointHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

/-- The four actual clockwise endpoint loops have the intended paired initial
fluxes, with no supplied holonomy relation. Source: SCP10, lines 2361–2386. -/
theorem regularWalkHolonomy_torusSweptStringInitial (v : X) (g h : G) (i : Fin 4) :
    regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusSweptPatchEndpointLoop v i) = ![g⁻¹, g, h, h⁻¹] i := by
  have hw := Fact.out (p := 6 < width)
  have hh := Fact.out (p := 5 < height)
  have hx (a b : ℤ) (hne : a ≠ b) (hd : (b - a).natAbs < width) :
      (a : ZMod width) ≠ (b : ZMod width) :=
    fun h => hne ((ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt a b hd).mp h)
  have hy (a b : ℤ) (hne : a ≠ b) (hd : (b - a).natAbs < height) :
      (a : ZMod height) ≠ (b : ZMod height) :=
    fun h => hne ((ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt a b hd).mp h)
  have hx0 : (-1 : ZMod width) ≠ (1 : ZMod width) := by
    simpa using hx (-1) (1) (by decide) (by norm_num; omega)
  have hx1 : (-1 : ZMod width) ≠ (2 : ZMod width) := by
    simpa using hx (-1) (2) (by decide) (by norm_num; omega)
  have hx2 : (-1 : ZMod width) ≠ (3 : ZMod width) := by
    simpa using hx (-1) (3) (by decide) (by norm_num; omega)
  have hx3 : (3 : ZMod width) ≠ (1 : ZMod width) := by
    simpa using hx (3) (1) (by decide) (by norm_num; omega)
  have hx4 : (4 : ZMod width) ≠ (0 : ZMod width) := by
    simpa using hx (4) (0) (by decide) (by norm_num; omega)
  have hx5 : (4 : ZMod width) ≠ (1 : ZMod width) := by
    simpa using hx (4) (1) (by decide) (by norm_num; omega)
  have hx6 : (4 : ZMod width) ≠ (2 : ZMod width) := by
    simpa using hx (4) (2) (by decide) (by norm_num; omega)
  have hx7 : (4 : ZMod width) ≠ (3 : ZMod width) := by
    simpa using hx (4) (3) (by decide) (by norm_num; omega)
  have hy0 : (2 : ZMod height) ≠ (-1 : ZMod height) := by
    simpa using hy (2) (-1) (by decide) (by norm_num; omega)
  have hy1 : (2 : ZMod height) ≠ (0 : ZMod height) := by
    simpa using hy (2) (0) (by decide) (by norm_num; omega)
  have hy2 : (2 : ZMod height) ≠ (1 : ZMod height) := by
    simpa using hy (2) (1) (by decide) (by norm_num; omega)
  have hy3 : (-2 : ZMod height) ≠ (1 : ZMod height) := by
    simpa using hy (-2) (1) (by decide) (by norm_num; omega)
  let p := torusSweptPatchEndpoint v i
  change regularWalkHolonomy (torusSweptStringInitialOperators v g h)
    (torusPlaquetteWalk p).reverse = _
  rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
    torusSweptStringInitialOperators_right_transport v p g h,
    torusSweptStringInitialOperators_up_transport v (p.1 + 1, p.2) g h,
    torusSweptStringInitialOperators_right_transport v (p.1, p.2 + 1) g h,
    torusSweptStringInitialOperators_up_transport v p g h]
  dsimp only [p]
  simp only [torusSweptPatchEndpoint_eq]
  fin_cases i <;>
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      Finset.mem_insert, Finset.mem_singleton, add_assoc, sub_eq_add_neg,
      hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hy0, hy1, hy2, hy3]

/-- Among the four source endpoints, precisely the upper endpoint of the second
string belongs to either swept patch. Source: SCP10, lines 2361–2386. -/
theorem torusSweptPatchEndpoint_mem_sweptStringVertices (v : X) (second : Bool) (i : Fin 4) :
    torusSweptPatchEndpoint v i ∈ torusSweptStringVertices v second ↔ i = 2 := by
  have hw := Fact.out (p := 6 < width)
  have hh := Fact.out (p := 5 < height)
  have hx (a b : ℤ) (hne : a ≠ b) (hd : (b - a).natAbs < width) :
      (a : ZMod width) ≠ (b : ZMod width) :=
    fun h => hne ((ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt a b hd).mp h)
  have hy (a b : ℤ) (hne : a ≠ b) (hd : (b - a).natAbs < height) :
      (a : ZMod height) ≠ (b : ZMod height) :=
    fun h => hne ((ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt a b hd).mp h)
  have hx0 : (-1 : ZMod width) ≠ (1 : ZMod width) := by
    simpa using hx (-1) 1 (by decide) (by norm_num; omega)
  have hx1 : (-1 : ZMod width) ≠ (2 : ZMod width) := by
    simpa using hx (-1) 2 (by decide) (by norm_num; omega)
  have hx2 : (3 : ZMod width) ≠ (1 : ZMod width) := by
    simpa using hx 3 1 (by decide) (by norm_num; omega)
  have hx3 : (3 : ZMod width) ≠ (2 : ZMod width) := by
    simpa using hx 3 2 (by decide) (by norm_num; omega)
  have hy0 : (-2 : ZMod height) ≠ (0 : ZMod height) := by
    simpa using hy (-2) 0 (by decide) (by norm_num; omega)
  have hy1 : (-2 : ZMod height) ≠ (1 : ZMod height) := by
    simpa using hy (-2) 1 (by decide) (by norm_num; omega)
  cases second <;> fin_cases i <;>
    norm_num [torusSweptPatchEndpoint_eq, torusSweptStringVertices,
      Prod.ext_iff, add_assoc, sub_eq_add_neg, hx0, hx1, hx2, hx3, hy0, hy1]

/-- Under either displayed sweep only the upper endpoint of the second string
is conjugated. All four values are derived from actual loop-gauge telescoping.
Source: SCP10, the virtual string-crossing figure in lines 2361–2386. -/
theorem regularWalkHolonomy_torusSweptStringOperators
    (v : X) (second : Bool) (g h : G) (i : Fin 4) :
    regularWalkHolonomy (torusSweptStringOperators v second g h)
      (torusSweptPatchEndpointLoop v i) = ![g⁻¹, g, g * h * g⁻¹, h⁻¹] i := by
  unfold torusSweptStringOperators
  rw [regularSweptPatchOperators_eq_vertexGauge, regularWalkHolonomy_gauge_loop,
    regularWalkHolonomy_torusSweptStringInitial]
  simp only [regularSweptPatchGauge, torusSweptPatchEndpoint_mem_sweptStringVertices]
  fin_cases i <;> simp

end TNLean.PEPS
