/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.GaugeAction
import TNLean.PEPS.RegularOpenRegion
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual graph contraction and physical bond coordinates

A local physical alphabet may depend on the vertex. Contracting one virtual
index on every native edge gives the same finite sum as the existing tensor
coefficients whenever the physical alphabet is uniformly numbered. This
requires no additional tensor structure. Regrouping the incident physical
coordinates gives the head-tail pair on every edge and is a Hilbert-space
coordinate permutation.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2938–3019.
These are finite-simple-graph versions of the local bond-coordinate argument;
no connectedness, valence, or topology assumption is imposed. They make no
parent-Hamiltonian claim.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X : Type*}

/-- Regroup all incident site coordinates into the head-tail pair on each edge. Source: SCP10,
Section 7, lines 2977–3019. -/
def graphSiteBondEndpointEquiv :
    ((v : V) → IncidentEdge Γ v → X) ≃ (Edge Γ → X × X) where
  toFun σ e := (σ e.1.2 (edgeRightIncident e), σ e.1.1 (edgeLeftIncident e))
  invFun β v f := if f.1.1.1 = v then (β f.1).2 else (β f.1).1
  left_inv σ := by
    funext v f
    rcases f with ⟨e, hf⟩
    rcases hf with h | h
    · subst v
      dsimp only
      rw [ite_eq_left rfl]
      rfl
    · subst v
      simp only [ite_eq_right (ne_of_lt e.2.1)]
      rfl
  right_inv β := by
    funext e
    exact Prod.ext (by simp [edgeRightIncident, ne_of_lt e.2.1])
      (by simp [edgeLeftIncident])

omit [Fintype V] [DecidableRel Γ.Adj] in
@[simp] theorem graphSiteBondEndpointEquiv_symm_tail
    (β : Edge Γ → X × X) (e : Edge Γ) :
    graphSiteBondEndpointEquiv.symm β e.1.1 (edgeLeftIncident e) = (β e).2 := by
  simp [graphSiteBondEndpointEquiv, edgeLeftIncident]

omit [Fintype V] [DecidableRel Γ.Adj] in
@[simp] theorem graphSiteBondEndpointEquiv_symm_head
    (β : Edge Γ → X × X) (e : Edge Γ) :
    graphSiteBondEndpointEquiv.symm β e.1.2 (edgeRightIncident e) = (β e).1 := by
  simp [graphSiteBondEndpointEquiv, edgeRightIncident, ne_of_lt e.2.1]

/-- The regrouped physical coefficients are the same literal coefficients. Source: SCP10, Section
7, lines 2977–3019. -/
def graphBondRegrouping :
    (((v : V) → IncidentEdge Γ v → X) → ℂ) ≃ₗ[ℂ]
      ((Edge Γ → X × X) → ℂ) :=
  LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) graphSiteBondEndpointEquiv

omit [Fintype V] [DecidableRel Γ.Adj] in
@[simp] theorem graphBondRegrouping_apply
    (ψ : ((v : V) → IncidentEdge Γ v → X) → ℂ) (β : Edge Γ → X × X) :
    graphBondRegrouping ψ β = ψ (graphSiteBondEndpointEquiv.symm β) := rfl

variable [Fintype X]
/-- The actual incidence contraction with dependent physical alphabets. Source: SCP10, Section 7,
lines 2977–3019. -/
def graphBondNetwork {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ)
    (σ : (v : V) → P v) : ℂ :=
  ∑ η : Edge Γ → X, ∏ v, a v (fun f => η f.1) (σ v)

/-- Uniform finite physical alphabets recover the existing tensor contraction. Source: SCP10,
Section 7, lines 2977–3019. -/
theorem stateCoeff_groupBondTensor_eq_graphBondNetwork {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ) (σ : V → Fin d) :
    stateCoeff (groupBondTensor a) σ = graphBondNetwork a σ := by
  let E : (Edge Γ → X) ≃ VirtualConfig (groupBondTensor a) :=
    Equiv.piCongrRight fun _ => Fintype.equivFin X
  rw [stateCoeff, ← E.sum_comp]
  simp only [groupBondTensor, E, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply,
    graphBondNetwork]

/-- The site-to-bond coordinate permutation preserves every physical overlap. Source: SCP10,
Section 7, lines 2977–3019. -/
theorem graphBondRegrouping_dotProduct
    (ψ φ : ((v : V) → IncidentEdge Γ v → X) → ℂ) :
    star (graphBondRegrouping ψ) ⬝ᵥ graphBondRegrouping φ = star ψ ⬝ᵥ φ :=
  graphSiteBondEndpointEquiv.symm.sum_comp (fun σ => star (ψ σ) * φ σ)

/-- The regrouping is the induced Hilbert-space coordinate isometry. Source: SCP10, Section 7,
lines 2977–3019. -/
def graphBondRegroupingIsometry :
    EuclideanSpace ℂ ((v : V) → IncidentEdge Γ v → X) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Edge Γ → X × X) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ graphSiteBondEndpointEquiv
end TNLean.PEPS
