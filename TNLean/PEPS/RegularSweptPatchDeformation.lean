/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWalkHolonomy

/-!
# Constant gauges on swept vertex patches

A constant gauge on a finite vertex patch conjugates the internal directed
transports and changes crossing transports on the appropriate side. Local
regular invariance gives equality of the actual closed contraction before and
after this explicit bond assignment change.

Source: SCP10, arXiv:1001.3807, lines 2361–2386, equation
`eq:anyons:fluxon-braiding-lazy` and the virtual string-deformation figure.
These are auxiliary finite-patch identities. The figure's native geometry,
four endpoints and partner strings are not instantiated here; no prescribed
braiding transformation or parent-Hamiltonian assertion is made.
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G]

/-- The inverse constant group gauge on the swept patch.
Source: SCP10, virtual deformation in lines 2361–2386. -/
def regularSweptPatchGauge (R : Finset V) (g : G) : V → G :=
  fun v => if v ∈ R then g⁻¹ else 1

/-- The literal ordered-edge assignment after sweeping a constant gauge.
Source: SCP10, virtual deformation in lines 2361–2386. -/
def regularSweptPatchOperators (R : Finset V) (g : G) (u : Edge Γ → G) : Edge Γ → G :=
  fun e => if e.1.2 ∈ R then
    if e.1.1 ∈ R then g * u e * g⁻¹ else g * u e
  else if e.1.1 ∈ R then u e * g⁻¹ else u e

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- The four literal bond cases are exactly the endpoint gauge formula.
Source: SCP10, virtual deformation in lines 2361–2386. -/
theorem regularSweptPatchOperators_eq_vertexGauge
    (R : Finset V) (g : G) (u : Edge Γ → G) :
    regularSweptPatchOperators R g u =
      regularVertexGaugeOperators (regularSweptPatchGauge R g) u := by
  funext e
  by_cases hh : e.1.2 ∈ R <;> by_cases ht : e.1.1 ∈ R <;>
    simp [regularSweptPatchOperators, regularVertexGaugeOperators,
      regularSweptPatchGauge, hh, ht]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Arbitrarily oriented edges obey the same four cases, including edges
whose ordered orientation is opposite to their traversal direction.
Source: SCP10, virtual deformation in lines 2361–2386. -/
theorem regularDirectedTransport_regularSweptPatchOperators
    (R : Finset V) (g : G) (u : Edge Γ → G) {v w : V} (h : Γ.Adj v w) :
    regularDirectedTransport (regularSweptPatchOperators R g u) h =
      if w ∈ R then
        if v ∈ R then g * regularDirectedTransport u h * g⁻¹
        else g * regularDirectedTransport u h
      else if v ∈ R then regularDirectedTransport u h * g⁻¹
      else regularDirectedTransport u h := by
  rw [regularSweptPatchOperators_eq_vertexGauge, regularDirectedTransport_gauge]
  by_cases hw : w ∈ R <;> by_cases hv : v ∈ R <;>
    simp [regularSweptPatchGauge, hw, hv]

/-- Local regular invariance derives equality of actual closed coefficient
vectors for every swept patch, group label and original bond assignment.
Source: SCP10, virtual deformation in lines 2361–2386. -/
theorem stateCoeff_regularSweptPatchOperators {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ x v η s, a v (fun e => x * η e) s = a v η s)
    (R : Finset V) (g : G) (u : Edge Γ → G) :
    stateCoeff (groupBondTensor (regularTwistedSite a u)) =
      stateCoeff (groupBondTensor (regularTwistedSite a (regularSweptPatchOperators R g u))) := by
  rw [regularSweptPatchOperators_eq_vertexGauge]
  funext σ
  exact sameState_regularVertexGauge a ha (regularSweptPatchGauge R g) u σ

end TNLean.PEPS
