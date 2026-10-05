/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutBoundaryBasis
import Mathlib.Logic.Equiv.Basic

/-!
# Edge-dependent contractions on directed multigraphs

Every labelled edge has two distinct endpoints and its own finite virtual
alphabet. The endpoint fibers at a vertex supply its local input space.
Parallel edges and self edges remain distinct, and neither the virtual nor
the physical dimensions need be uniform. Cutting a set of edges exposes both
endpoints to one arbitrary joint boundary tensor.

This is a coordinate foundation for the dimension-independent form of SCP10,
arXiv:1001.3807, Theorem 5.5 and equation `eq:2d:closure-intersection`.
No injectivity, representation, or graph simplicity assumption is made here.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*}

/-- The two endpoints of a labelled edge; false denotes its tail. -/
abbrev Endpoint (Edge : Type*) := Edge × Bool

/-- The vertex at an endpoint, with true denoting the head. -/
def endpointVertex (tail head : Edge → Vertex) (p : Endpoint Edge) : Vertex :=
  if p.2 then head p.1 else tail p.1

/-- All endpoint incidences at a vertex, including both incidences of a self edge. -/
abbrev IncidentEndpoint (tail head : Edge → Vertex) (v : Vertex) :=
  {p : Endpoint Edge // endpointVertex tail head p = v}

/-- A configuration of independent labels on both endpoints of every edge. -/
abbrev EndpointConfig (D : Edge → Type*) := (p : Endpoint Edge) → D p.1

/-- The local virtual configuration at a vertex. -/
abbrev LocalConfig (tail head : Edge → Vertex) (D : Edge → Type*) (v : Vertex) :=
  (p : IncidentEndpoint tail head v) → D p.1.1

variable (tail head : Edge → Vertex) (D : Edge → Type*)

/-- Regrouping independent endpoint labels by the vertex where they occur. -/
def endpointSiteEquiv : EndpointConfig D ≃ ((v : Vertex) → LocalConfig tail head D v) where
  toFun β _ p := β p.1
  invFun η p := η (endpointVertex tail head p) ⟨p, rfl⟩
  left_inv _ := rfl
  right_inv η := by
    funext v p
    rcases p with ⟨p, hp⟩
    subst v
    rfl

@[simp]
theorem endpointSiteEquiv_apply (β : EndpointConfig D) (v : Vertex)
    (p : IncidentEndpoint tail head v) : endpointSiteEquiv tail head D β v p = β p.1 := rfl

@[simp]
theorem endpointSiteEquiv_symm_apply (η : (v : Vertex) → LocalConfig tail head D v)
    (p : Endpoint Edge) :
    (endpointSiteEquiv tail head D).symm η p =
      η (endpointVertex tail head p) ⟨p, rfl⟩ := rfl

/-- Regrouping endpoint configurations as one head/tail pair per edge. -/
def endpointPairEquiv : EndpointConfig D ≃ ((e : Edge) → D e × D e) where
  toFun β e := (β (e, true), β (e, false))
  invFun η p := if p.2 then (η p.1).1 else (η p.1).2
  left_inv β := by
    funext p
    rcases p with ⟨e, b⟩
    cases b <;> rfl
  right_inv _ := rfl

@[simp]
theorem endpointPairEquiv_apply (β : EndpointConfig D) (e : Edge) :
    endpointPairEquiv D β e = (β (e, true), β (e, false)) := rfl

section Finite
variable [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]

/-- A product over site-local incidences is exactly the product over all endpoints. -/
theorem prod_incident_eq_prod_endpoint {M : Type*} [CommMonoid M]
    (f : Endpoint Edge → M) :
    (∏ v, ∏ p : IncidentEndpoint tail head v, f p.1) = ∏ p, f p := by
  classical
  exact Fintype.prod_fiberwise (endpointVertex tail head) f

/-- Splitting the product of endpoint factors into the two factors on each edge. -/
theorem prod_endpoint_eq_prod_edge {M : Type*} [CommMonoid M]
    (f : Endpoint Edge → M) :
    (∏ p, f p) = ∏ e, f (e, false) * f (e, true) := by
  rw [Fintype.prod_prod_type]
  simp [mul_comm]

/-- Product regrouping from vertex incidences to independently labelled edges. -/
theorem prod_incident_eq_prod_edge {M : Type*} [CommMonoid M]
    (f : Endpoint Edge → M) :
    (∏ v, ∏ p : IncidentEndpoint tail head v, f p.1) =
      ∏ e, f (e, false) * f (e, true) := by
  rw [prod_incident_eq_prod_endpoint, prod_endpoint_eq_prod_edge]

variable [DecidableEq Edge] [∀ e, Fintype (D e)]
/-- Independent head/tail summation separates into one double sum per edge. -/
theorem sum_endpoint_prod_eq_prod_sum {R : Type*} [CommSemiring R]
    (f : (e : Edge) → D e → D e → R) :
    (∑ β : EndpointConfig D, ∏ e, f e (β (e, true)) (β (e, false))) =
      ∏ e, ∑ h : D e, ∑ t : D e, f e h t := by
  classical
  rw [← (endpointPairEquiv D).symm.sum_comp]
  simp only [endpointPairEquiv, Equiv.coe_fn_symm_mk, Bool.false_eq_true, ↓reduceIte]
  rw [← Fintype.prod_sum (fun e (p : D e × D e) ↦ f e p.1 p.2)]
  simp only [Fintype.sum_prod_type]

variable {Phys : Vertex → Type*}

/-- Product of arbitrary inserted edge matrices. The head is the row index. -/
def bondWeight (B : (e : Edge) → Matrix (D e) (D e) ℂ) (β : EndpointConfig D) : ℂ :=
  ∏ e, B e (β (e, true)) (β (e, false))

/-- The literal independent-endpoint tensor contraction, with dependent alphabets. -/
def network (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (σ : (v : Vertex) → Phys v) : ℂ :=
  ∑ β : EndpointConfig D, bondWeight D B β *
    ∏ v, A v (endpointSiteEquiv tail head D β v) (σ v)

/-- The same contraction written as a sum over site-local configurations. -/
theorem network_eq_sum_site
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (σ : (v : Vertex) → Phys v) :
    network tail head D A B σ =
      ∑ η : (v : Vertex) → LocalConfig tail head D v,
        bondWeight D B ((endpointSiteEquiv tail head D).symm η) *
          ∏ v, A v (η v) (σ v) := by
  classical
  unfold network
  rw [← (endpointSiteEquiv tail head D).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]

end Finite

end TNLean.PEPS.DependentBondNetwork
