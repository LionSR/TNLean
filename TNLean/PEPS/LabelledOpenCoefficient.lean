/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondNetwork
import Mathlib.Logic.Equiv.Prod

/-!
# Open coefficients on labelled bonds

The open coefficient sums region incidence labels, fixes crossing incidences
by boundary data, and inserts arbitrary matrices on internal labelled bonds.
An exact delta-exterior completion realizes this independent sum as a closed
contraction. Parallel bonds and both incidences of self bonds are retained.
This is the finite-coordinate bridge for the collared specialization of SCP10,
arXiv:1001.3807v3, Lemma 6.14; no vacuum-density assertion is made.
-/

noncomputable section
open scoped BigOperators Classical

namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge V : Type*} [Fintype Vertex] [Fintype Edge]
variable [DecidableEq Vertex] [DecidableEq Edge] [Fintype V] [DecidableEq V]
variable (tail head : Edge → Vertex) (R : Set Vertex)

/-- Region-side incidences of crossing labelled bonds. -/
def RegionBoundaryEndpoint :=
  {p : Endpoint Edge // endpointVertex tail head p ∈ R ∧
    endpointVertex tail head (p.1, !p.2) ∉ R}

/-- Independent labels at every incidence of every region vertex. -/
abbrev RegionSiteConfig := (v : R) → LocalConfig tail head (fun _ ↦ V) v.1

/-- Glue independent region and exterior site configurations. -/
def joinRegionConfig (η : RegionSiteConfig tail head R (V := V))
    (ξ : (v : {v // v ∉ R}) → LocalConfig tail head (fun _ ↦ V) v.1) :
    (v : Vertex) → LocalConfig tail head (fun _ ↦ V) v := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ R) _).symm (η, ξ)

/-- Internal matrices, crossing boundary deltas, and unit exterior factors. -/
def openBondFactor (O : Edge → Matrix V V ℂ)
    (θ : RegionBoundaryEndpoint tail head R → V)
    (η : RegionSiteConfig tail head R (V := V)) (e : Edge) : ℂ := by
  classical
  exact if ht : tail e ∈ R then
    if hh : head e ∈ R then
      O e (η ⟨head e, hh⟩ ⟨(e, true), rfl⟩) (η ⟨tail e, ht⟩ ⟨(e, false), rfl⟩)
    else if η ⟨tail e, ht⟩ ⟨(e, false), rfl⟩ = θ ⟨(e, false), ht, hh⟩ then 1 else 0
  else if hh : head e ∈ R then
    if η ⟨head e, hh⟩ ⟨(e, true), rfl⟩ = θ ⟨(e, true), hh, ht⟩ then 1 else 0
  else 1

/-- Literal open sum over region half-edge labels with fixed boundary indices. -/
def openCoefficient (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (O : Edge → Matrix V V ℂ) (θ : RegionBoundaryEndpoint tail head R → V) : ℂ :=
  ∑ η : RegionSiteConfig tail head R,
    (∏ e, openBondFactor tail head R O θ η e) * ∏ v, A v (η v)

/-- Contract against one arbitrary joint boundary tensor. -/
def openBoundaryContraction
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (O : Edge → Matrix V V ℂ) (B : (RegionBoundaryEndpoint tail head R → V) → ℂ) : ℂ :=
  ∑ θ, B θ * openCoefficient tail head R A O θ

/-- The unique fixed exterior assignment: match crossing boundary labels and
use the same chosen label on every remaining exterior incidence. -/
def deltaExteriorConfig (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (v : {v // v ∉ R}) : LocalConfig tail head (fun _ ↦ V) v.1 := by
  classical
  exact fun p ↦ if h : endpointVertex tail head (p.1.1, !p.1.2) ∈ R then
    θ ⟨(p.1.1, !p.1.2), h, by simpa only [Bool.not_not, p.2] using v.2⟩ else v₀

/-- Region tensors with exterior Kronecker deltas; the physical alphabet is a singleton. -/
def deltaCompletedTensor
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (v : Vertex) (c : LocalConfig tail head (fun _ ↦ V) v) (_ : PUnit) : ℂ := by
  classical
  exact if h : v ∈ R then A ⟨v, h⟩ c
    else if c = deltaExteriorConfig tail head R v₀ θ ⟨v, h⟩ then 1 else 0

/-- Keep arbitrary internal bond matrices and put identity on every other bond. -/
def internalBondMatrices (O : Edge → Matrix V V ℂ) (e : Edge) : Matrix V V ℂ := by
  classical
  exact if tail e ∈ R ∧ head e ∈ R then O e else 1

private theorem completed_bondWeight
    (O : Edge → Matrix V V ℂ) (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (η : RegionSiteConfig tail head R (V := V)) :
    bondWeight (fun _ ↦ V) (internalBondMatrices tail head R O)
      ((endpointSiteEquiv tail head (fun _ ↦ V)).symm
        (joinRegionConfig tail head R η (deltaExteriorConfig tail head R v₀ θ))) =
      ∏ e, openBondFactor tail head R O θ η e := by
  classical
  apply Finset.prod_congr rfl
  intro e _
  by_cases ht : tail e ∈ R <;> by_cases hh : head e ∈ R
  all_goals simp [bondWeight, internalBondMatrices, openBondFactor, joinRegionConfig,
    Equiv.piEquivPiSubtypeProd, endpointVertex, deltaExteriorConfig, ht, hh,
    Matrix.one_apply, eq_comm]

private theorem completed_siteWeight
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (η : RegionSiteConfig tail head R (V := V))
    (ξ : (v : {v // v ∉ R}) → LocalConfig tail head (fun _ ↦ V) v.1) :
    (∏ v, deltaCompletedTensor tail head R A v₀ θ v
      (joinRegionConfig tail head R η ξ v) PUnit.unit) =
    (∏ v, A v (η v)) * if ξ = deltaExteriorConfig tail head R v₀ θ then 1 else 0 := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v ↦ v ∈ R)]
  have heq : (∀ v, ξ v = deltaExteriorConfig tail head R v₀ θ v) ↔
      ξ = deltaExteriorConfig tail head R v₀ θ := funext_iff.symm
  simp [deltaCompletedTensor, joinRegionConfig, Equiv.piEquivPiSubtypeProd,
    Fintype.prod_ite_zero, heq]

/-- Exact delta-exterior bridge. There is no dimension scalar and no product
assumption on subsequent boundary tensors. -/
theorem network_deltaCompletedTensor
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (O : Edge → Matrix V V ℂ) (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V) :
    network tail head (fun _ ↦ V) (deltaCompletedTensor tail head R A v₀ θ)
      (internalBondMatrices tail head R O) (fun _ ↦ PUnit.unit) =
        openCoefficient tail head R A O θ := by
  classical
  rw [network_eq_sum_site]
  rw [← (Equiv.piEquivPiSubtypeProd (· ∈ R)
    (LocalConfig tail head (fun _ ↦ V))).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ η, ∑ ξ, _ * ∏ v, deltaCompletedTensor tail head R A v₀ θ v
    (joinRegionConfig tail head R η ξ v) PUnit.unit) = _
  simp_rw [completed_siteWeight, ← mul_assoc]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [completed_bondWeight, openCoefficient]

end TNLean.PEPS.DependentBondNetwork
