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
This finite-coordinate identity serves the collared specialization of SCP10,
arXiv:1001.3807v3, Lemma 6.14; no vacuum-density assertion is made.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge V : Type*} [Fintype Vertex] [Fintype Edge]
variable [DecidableEq Vertex] [DecidableEq Edge] [Fintype V] [DecidableEq V]
variable (tail head : Edge → Vertex) (R : Set Vertex)

open Classical in
/-- Region-side incidences of crossing labelled bonds. -/
abbrev RegionBoundaryEndpoint :=
  {p : Endpoint Edge // endpointVertex tail head p ∈ R ∧
    endpointVertex tail head (p.1, !p.2) ∉ R}

open Classical in
/-- Independent labels at every incidence of every region vertex. -/
abbrev RegionSiteConfig := (v : R) → LocalConfig tail head (fun _ ↦ V) v.1

open Classical in
/-- Glue independent region and exterior site configurations. -/
def joinRegionConfig (η : RegionSiteConfig tail head R (V := V))
    (ξ : (v : {v // v ∉ R}) → LocalConfig tail head (fun _ ↦ V) v.1) :
    (v : Vertex) → LocalConfig tail head (fun _ ↦ V) v := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ R) _).symm (η, ξ)

open Classical in
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

open Classical in
/-- Literal open sum over region half-edge labels with fixed boundary indices. -/
def openCoefficient (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (O : Edge → Matrix V V ℂ) (θ : RegionBoundaryEndpoint tail head R → V) : ℂ :=
  ∑ η : RegionSiteConfig tail head R,
    (∏ e, openBondFactor tail head R O θ η e) * ∏ v, A v (η v)

open Classical in
/-- Contract against one arbitrary joint boundary tensor. -/
def openBoundaryContraction
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (O : Edge → Matrix V V ℂ) (B : (RegionBoundaryEndpoint tail head R → V) → ℂ) : ℂ :=
  ∑ θ, B θ * openCoefficient tail head R A O θ

open Classical in
/-- The unique fixed exterior assignment: match crossing boundary labels and
use the same chosen label on every remaining exterior incidence. -/
def deltaExteriorConfig (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (v : {v // v ∉ R}) : LocalConfig tail head (fun _ ↦ V) v.1 := by
  classical
  exact fun p ↦ if h : endpointVertex tail head (p.1.1, !p.1.2) ∈ R then
    θ ⟨(p.1.1, !p.1.2), h, by simpa only [Bool.not_not, p.2] using v.2⟩ else v₀

open Classical in
/-- Region tensors with exterior Kronecker deltas; the physical alphabet is a singleton. -/
def deltaCompletedTensor
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (v : Vertex) (c : LocalConfig tail head (fun _ ↦ V) v) (_ : PUnit.{1}) : ℂ := by
  classical
  exact if h : v ∈ R then A ⟨v, h⟩ c
    else if c = deltaExteriorConfig tail head R v₀ θ ⟨v, h⟩ then 1 else 0

open Classical in
/-- Keep arbitrary internal bond matrices and put identity on every other bond. -/
def internalBondMatrices (O : Edge → Matrix V V ℂ) (e : Edge) : Matrix V V ℂ := by
  classical
  exact if tail e ∈ R ∧ head e ∈ R then O e else 1

omit [DecidableEq Vertex] [DecidableEq Edge] [Fintype Vertex] [Fintype V] in
open Classical in
private theorem completed_bondWeight
    (O : Edge → Matrix V V ℂ) (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (η : RegionSiteConfig tail head R (V := V)) :
    bondWeight (fun _ ↦ V) (internalBondMatrices tail head R O)
      ((endpointSiteEquiv tail head (fun _ ↦ V)).symm
        (joinRegionConfig tail head R η (deltaExteriorConfig tail head R v₀ θ))) =
      ∏ e, openBondFactor tail head R O θ η e := by
  classical
  let β := (endpointSiteEquiv tail head (fun _ ↦ V)).symm
    (joinRegionConfig tail head R η (deltaExteriorConfig tail head R v₀ θ))
  change (∏ e, internalBondMatrices tail head R O e (β (e, true)) (β (e, false))) = _
  apply Finset.prod_congr rfl
  intro e _
  have hhead : β (e, true) =
      if hh : head e ∈ R then η ⟨head e, hh⟩ ⟨(e, true), rfl⟩
      else if ht : tail e ∈ R then θ ⟨(e, false), ht, hh⟩ else v₀ := by
    by_cases hh : head e ∈ R
    all_goals simp [β, joinRegionConfig, Equiv.piEquivPiSubtypeProd,
      endpointVertex, deltaExteriorConfig, hh]
  have htail : β (e, false) =
      if ht : tail e ∈ R then η ⟨tail e, ht⟩ ⟨(e, false), rfl⟩
      else if hh : head e ∈ R then θ ⟨(e, true), hh, ht⟩ else v₀ := by
    by_cases ht : tail e ∈ R
    all_goals simp [β, joinRegionConfig, Equiv.piEquivPiSubtypeProd,
      endpointVertex, deltaExteriorConfig, ht]
  rw [hhead, htail]
  by_cases ht : tail e ∈ R <;> by_cases hh : head e ∈ R
  all_goals simp only [internalBondMatrices, openBondFactor, ht, hh,
    and_self, and_false, and_true, ite_true, ite_false, dite_true, dite_false,
    Matrix.one_apply]
  all_goals simp only [eq_comm]

omit [DecidableEq Edge] [Fintype V] in
open Classical in
private theorem completed_siteWeight
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V)
    (η : RegionSiteConfig tail head R (V := V))
    (ξ : (v : {v // v ∉ R}) → LocalConfig tail head (fun _ ↦ V) v.1) :
    (∏ v, deltaCompletedTensor tail head R A v₀ θ v
      (joinRegionConfig tail head R η ξ v) PUnit.unit.{1}) =
    (∏ v, A v (η v)) * if ξ = deltaExteriorConfig tail head R v₀ θ then 1 else 0 := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v ↦ v ∈ R)]
  have hin (v : R) : deltaCompletedTensor tail head R A v₀ θ v.1
      (joinRegionConfig tail head R η ξ v.1) PUnit.unit.{1} = A v (η v) := by
    simp [deltaCompletedTensor, joinRegionConfig, Equiv.piEquivPiSubtypeProd, v.2]
  have hout (v : {v // v ∉ R}) : deltaCompletedTensor tail head R A v₀ θ v.1
      (joinRegionConfig tail head R η ξ v.1) PUnit.unit.{1} =
      if ξ v = deltaExteriorConfig tail head R v₀ θ v then 1 else 0 := by
    simp [deltaCompletedTensor, joinRegionConfig, Equiv.piEquivPiSubtypeProd, v.2]
  calc
    _ = (∏ v, A v (η v)) *
        ∏ v : {v // v ∉ R},
          (if ξ v = deltaExteriorConfig tail head R v₀ θ v then (1 : ℂ) else 0) := by
      congr 1
      · exact Finset.prod_congr rfl fun v _ ↦ hin v
      · exact Finset.prod_congr rfl fun v _ ↦ hout v
    _ = _ := by
      rw [Fintype.prod_ite_zero]
      simp only [Finset.prod_const_one]
      congr 2
      exact propext funext_iff.symm

open Classical in
/-- Exact delta-exterior identity. There is no dimension scalar and no product
assumption on subsequent boundary tensors. -/
theorem network_deltaCompletedTensor
    (A : (v : R) → LocalConfig tail head (fun _ ↦ V) v.1 → ℂ)
    (O : Edge → Matrix V V ℂ) (v₀ : V) (θ : RegionBoundaryEndpoint tail head R → V) :
    network tail head (fun _ ↦ V) (deltaCompletedTensor tail head R A v₀ θ)
      (internalBondMatrices tail head R O) (fun _ ↦ PUnit.unit.{1}) =
        openCoefficient tail head R A O θ := by
  classical
  rw [network_eq_sum_site]
  rw [← (Equiv.piEquivPiSubtypeProd (· ∈ R)
    (LocalConfig tail head (fun _ ↦ V))).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ η, ∑ ξ, _ * ∏ v, deltaCompletedTensor tail head R A v₀ θ v
    (joinRegionConfig tail head R η ξ v) PUnit.unit.{1}) = _
  simp_rw [completed_siteWeight, ← mul_assoc]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold openCoefficient
  apply Finset.sum_congr rfl
  intro η _
  change bondWeight _ _ ((endpointSiteEquiv tail head _).symm
    (joinRegionConfig tail head R η (deltaExteriorConfig tail head R v₀ θ))) * _ = _
  rw [completed_bondWeight]

end TNLean.PEPS.DependentBondNetwork
