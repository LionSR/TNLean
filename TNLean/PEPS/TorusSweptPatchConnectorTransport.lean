/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSweptPatchEndpointGeometry
import TNLean.PEPS.RegularConnectorHolonomy
import TNLean.PEPS.TorusSweptStringEndpointHolonomy

/-!
# Actual partner comparison in the swept-string presentation

The two native connectors compare flux loops at a common base. Both ends of the
first connector lie outside the sweep, whereas the second connector starts at
the swept endpoint and ends at its unchanged partner. Gauge telescoping changes
the second connecting transport, and consequently also conjugates the partner
flux when it is compared at the first base. Their based joint product remains
identity. This is a precise property of the same-connector gauge presentation,
not a counterexample to the source or an implementation of physical braiding.

**Scope restriction:** These identities concern the same-connector gauge
presentation on the explicit twenty-site finite-torus witness. Physical
reunion and rerouting remain separate in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: SCP10, arXiv:1001.3807, the virtual-level fluxon-braiding figure and
joint-flux alignment discussion, local lines 2361–2415.
-/

namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (6 < width)] [Fact (5 < height)]
local instance sweptConnectorWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptConnectorHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local instance sweptConnectorWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptConnectorHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local instance sweptConnectorWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptConnectorHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

/-- The actual first partner connector initially transports by `g⁻¹`.
Source: SCP10, the explicit partner comparison in lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptStringInitial_connectorA (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusSweptPatchConnectorA v) = g⁻¹ := by
  have hw := Fact.out (p := 6 < width)
  have hh := Fact.out (p := 5 < height)
  have hx0 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := width) (-1) 0 (by norm_num; omega)
  have hx1 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := width) (-1) 1 (by norm_num; omega)
  have hx2 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := width) (-1) 2 (by norm_num; omega)
  have hx3 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := width) (-1) 3 (by norm_num; omega)
  have hy0 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := height) 2 (-1) (by norm_num; omega)
  have hy1 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := height) 2 0 (by norm_num; omega)
  have hy2 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := height) 2 1 (by norm_num; omega)
  norm_num at hx0 hx1 hx2 hx3 hy0 hy1 hy2
  rw [regularWalkHolonomy_torusSweptPatchConnectorA,
    torusSweptStringInitialOperators_up_transport v (v.1 + 3, v.2 + 1) g h,
    torusSweptStringInitialOperators_right_transport v (v.1 + 2, v.2 + 2) g h,
    torusSweptStringInitialOperators_right_transport v (v.1 + 1, v.2 + 2) g h,
    torusSweptStringInitialOperators_right_transport v (v.1, v.2 + 2) g h,
    torusSweptStringInitialOperators_right_transport v (v.1 - 1, v.2 + 2) g h,
    torusSweptStringInitialOperators_up_transport v (v.1 - 1, v.2 + 1) g h]
  norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
    add_assoc, sub_eq_add_neg, hx0, hx1, hx2, hx3, hy0, hy1, hy2]

/-- The actual second partner connector initially has identity transport.
Source: SCP10, the explicit partner comparison in lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptStringInitial_connectorB (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusSweptPatchConnectorB v) = 1 := by
  have hh := Fact.out (p := 5 < height)
  have hy0 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := height) (-2) 1 (by norm_num; omega)
  have hy1 := ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt
    (n := height) (-1) 1 (by norm_num; omega)
  norm_num at hy0 hy1
  rw [regularWalkHolonomy_torusSweptPatchConnectorB,
    torusSweptStringInitialOperators_up_transport v (v.1 + 1, v.2 - 2) g h,
    torusSweptStringInitialOperators_up_transport v (v.1 + 1, v.2 - 1) g h,
    torusSweptStringInitialOperators_up_transport v (v.1 + 1, v.2) g h]
  norm_num [torusSweptStringInitialUp, add_assoc, sub_eq_add_neg, hy0, hy1]

/-- The first connector is unchanged by either swept gauge, because both of
its endpoint bases are outside the sweep. Source: SCP10, lines 2361–2415. -/
theorem regularWalkHolonomy_torusSweptStringOperators_connectorA
    (v : X) (second : Bool) (g h : G) :
    regularWalkHolonomy (torusSweptStringOperators v second g h)
      (torusSweptPatchConnectorA v) = g⁻¹ := by
  unfold torusSweptStringOperators
  rw [regularSweptPatchOperators_eq_vertexGauge, regularWalkHolonomy_gauge,
    regularWalkHolonomy_torusSweptStringInitial_connectorA]
  simp [regularSweptPatchGauge, torusSweptPatchEndpoint_mem_sweptStringVertices]

/-- The second connector acquires inverse `g` transport, since its starting
base is swept and its partner base is not. Source: SCP10, lines 2361–2415. -/
theorem regularWalkHolonomy_torusSweptStringOperators_connectorB
    (v : X) (second : Bool) (g h : G) :
    regularWalkHolonomy (torusSweptStringOperators v second g h)
      (torusSweptPatchConnectorB v) = g⁻¹ := by
  unfold torusSweptStringOperators
  rw [regularSweptPatchOperators_eq_vertexGauge, regularWalkHolonomy_gauge,
    regularWalkHolonomy_torusSweptStringInitial_connectorB]
  simp [regularSweptPatchGauge, torusSweptPatchEndpoint_mem_sweptStringVertices]

/-- The actual two-partner loop at the first B base. Traverse the partner loop
along the actual B connector and then the first endpoint loop; the reverse
product is first based flux times transported partner flux.
Source: SCP10, joint-flux alignment discussion, lines 2387–2415. -/
def torusSweptPatchBJointLoop (v : X) :
    (Γₜ).Walk (torusSweptPatchEndpoint v 2) (torusSweptPatchEndpoint v 2) :=
  (((torusSweptPatchConnectorB v).append (torusSweptPatchEndpointLoop v 3)).append
    (torusSweptPatchConnectorB v).reverse).append (torusSweptPatchEndpointLoop v 2)

/-- Initially the actual based B-partner comparison has trivial joint flux.
Source: SCP10, the initial paired fluxes and alignment discussion, lines 2340–2415. -/
theorem regularWalkHolonomy_torusSweptStringInitial_BJointLoop (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptStringInitialOperators v g h)
      (torusSweptPatchBJointLoop v) = 1 := by
  unfold torusSweptPatchBJointLoop
  rw [regularWalkHolonomy_append, regularWalkHolonomy_transportLoop,
    regularWalkHolonomy_torusSweptStringInitial_connectorB,
    regularWalkHolonomy_torusSweptStringInitial,
    regularWalkHolonomy_torusSweptStringInitial]
  simp

/-- The swept partner, compared at the B1 base along the same actual connector,
has conjugated inverse flux. Source: SCP10, alignment after sweeping, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptStringOperators_transportedBPartner
    (v : X) (second : Bool) (g h : G) :
    regularWalkHolonomy (torusSweptStringOperators v second g h)
      (((torusSweptPatchConnectorB v).append (torusSweptPatchEndpointLoop v 3)).append
        (torusSweptPatchConnectorB v).reverse) = g * h⁻¹ * g⁻¹ := by
  rw [regularWalkHolonomy_transportLoop,
    regularWalkHolonomy_torusSweptStringOperators_connectorB,
    regularWalkHolonomy_torusSweptStringOperators]
  simp

/-- Comparing both actual B loops along the same connector still gives trivial
joint flux after either gauge sweep. This is a statement about the gauge
presentation, not a counterexample to the source physical braid.
Source: SCP10, the virtual-level figure and alignment discussion, lines 2361–2415. -/
theorem regularWalkHolonomy_torusSweptStringOperators_BJointLoop
    (v : X) (second : Bool) (g h : G) :
    regularWalkHolonomy (torusSweptStringOperators v second g h)
      (torusSweptPatchBJointLoop v) = 1 := by
  unfold torusSweptPatchBJointLoop
  rw [regularWalkHolonomy_append,
    regularWalkHolonomy_torusSweptStringOperators_transportedBPartner,
    regularWalkHolonomy_torusSweptStringOperators]
  change (g * h * g⁻¹) * (g * h⁻¹ * g⁻¹) = 1
  group

end TNLean.PEPS
