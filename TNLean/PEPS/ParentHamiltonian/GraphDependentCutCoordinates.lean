/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentDiagonalContraction
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian

/-!
# Actual graph tensors in dependent endpoint coordinates

The existing finite-simple-graph PEPS tensor has an independent dimension on
every bond. Its incident-edge coordinates identify with the labelled head/tail
incidences of the dependent network. No tensor, bond dimension, or physical
coefficient is changed by this identification.

A region cuts precisely the bonds that are not internal to it. Closing the
extra cut endpoints by identities relates this literal cut boundary to the
existing genuine open-region contraction, with its explicitly accounted
exterior multiplicity.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS
open DependentBondNetwork

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The native orientation of an ordered simple-graph edge. -/
def graphEdgeTail (e : Edge Γ) : V := e.1.1

/-- The head in the native orientation of an ordered simple-graph edge. -/
def graphEdgeHead (e : Edge Γ) : V := e.1.2

/-- Each original graph bond keeps its own finite virtual alphabet. -/
abbrev graphBondAlphabet (A : Tensor Γ d) (e : Edge Γ) := Fin (A.bondDim e)

/-- The unique endpoint of an incident edge lying at the specified vertex. -/
def graphIncidentEndpoint (v : V) (e : IncidentEdge Γ v) :
    IncidentEndpoint (graphEdgeTail (Γ := Γ)) graphEdgeHead v :=
  ⟨(e.1, if e.1.1.1 = v then false else true), by
    rcases e.2 with ht | hh
    · simp [endpointVertex, ht, graphEdgeTail]
    · by_cases ht : e.1.1.1 = v
      · simp [endpointVertex, ht, graphEdgeTail]
      · simp [endpointVertex, ht, graphEdgeHead, hh]⟩

/-- A graph tensor read in its exact dependent endpoint coordinates. -/
def graphDependentTensor (A : Tensor Γ d) (v : V)
    (η : LocalConfig graphEdgeTail graphEdgeHead (graphBondAlphabet A) v) (s : Fin d) : ℂ :=
  A.component v (fun e ↦ η (graphIncidentEndpoint v e)) s

omit [Fintype V] in
/-- Identifying both endpoints of each edge recovers the original site input. -/
@[simp] theorem graphDependentTensor_diagonal (A : Tensor Γ d)
    (η : VirtualConfig A) (v : V) (s : Fin d) :
    graphDependentTensor A v
      (endpointSiteEquiv graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (diagonalEndpointConfig (graphBondAlphabet A) η) v) s =
      A.component v (fun e ↦ η e.1) s := rfl

/-- The literal uninserted dependent network is the original PEPS vector. -/
theorem network_graphDependentTensor_one (A : Tensor Γ d) (σ : V → Fin d) :
    network graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A)
      (fun _ ↦ 1) σ = stateCoeff A σ := by
  exact sum_identityWeight_mul (graphBondAlphabet A)
    (fun β ↦ ∏ v, graphDependentTensor A v (endpointSiteEquiv _ _ _ β v) (σ v))

/-- Every bond except the wholly internal bonds is exposed by the regional cut. -/
def regionExteriorCut (R : Finset V) : Finset (Edge Γ) :=
  Finset.univ.filter fun e ↦ ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R)

/-- A crossing bond belongs to the actual regional cut. -/
theorem mem_regionExteriorCut_of_boundary (R : Finset V)
    (e : {e : Edge Γ // IsRegionBoundaryEdge R e}) : e.1 ∈ regionExteriorCut R := by
  simp only [regionExteriorCut, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases e.2 with h | h <;> tauto

/-- Every endpoint omitted by the region lies on an exposed bond. -/
theorem mem_regionExteriorCut_of_outside (R : Finset V) (p : Endpoint (Edge Γ))
    (hp : endpointVertex graphEdgeTail graphEdgeHead p ∉ R) :
    p.1 ∈ regionExteriorCut R := by
  simp only [regionExteriorCut, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases p with ⟨e, b⟩
  cases b <;> simp only [endpointVertex, Bool.false_eq_true, ↓reduceIte,
    graphEdgeTail, graphEdgeHead] at hp <;> tauto

/-- Read one label on each crossing bond from the complete regional cut.
The other endpoint is closed by an explicit identity in the construction. -/
def regionCutBoundaryLabel (A : Tensor Γ d) (R : Finset V)
    (θ : CutConfig (regionExteriorCut (Γ := Γ) R) (graphBondAlphabet A)) :
    RegionBoundaryConfig A R :=
  fun e ↦ θ (⟨e.1, mem_regionExteriorCut_of_boundary R e⟩, false)

/-- On diagonal bond labels the dependent boundary is the original graph boundary. -/
@[simp] theorem regionCutBoundaryLabel_diagonal (A : Tensor Γ d) (R : Finset V)
    (η : VirtualConfig A) :
    regionCutBoundaryLabel A R (cutRestriction (graphBondAlphabet A) (regionExteriorCut R)
      (diagonalEndpointConfig (graphBondAlphabet A) η)) = regionBoundaryLabel A R η := rfl

/-- Summing the globally indexed regional tensors against boundary coefficients
counts each actual open-region contraction by its known exterior multiplicity. -/
theorem sum_regionBoundaryLabel_mul_eq_openRegionMap (A : Tensor Γ d) (R : Finset V)
    (x : RegionBoundaryConfig A R → ℂ) (σ : RegionPhysicalConfig (d := d) R) :
    (∑ η : VirtualConfig A, x (regionBoundaryLabel A R η) *
      ∏ w : {w : V // w ∈ R}, A.component w.1 (fun e ↦ η e.1) (σ w)) =
      (regionExteriorMultiplicity A R : ℂ) * openRegionMap A R x σ := by
  classical
  calc
    _ = ∑ μ, x μ * regionBlockedWeight A R μ σ := by
      unfold regionBlockedWeight
      simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro η _
      simp
    _ = _ := by
      simp only [regionBlockedWeight_eq_exterior_mul_openRegionWeight,
        openRegionMap_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      ring

end TNLean.PEPS
