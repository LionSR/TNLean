/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularOpenRegion

/-!
# Actual open graph coefficients with dependent physical alphabets

The native incident-edge labels split into internal labels and prescribed crossing
labels. Summing the actual contraction over incident assignments with this boundary
condition therefore sums each internal assignment exactly once. The physical
alphabet may depend on the vertex. For a uniform numbered physical alphabet the
coefficients are exactly the existing open-region coefficients of the same site
family, with the virtual alphabet enumerated into finite indices.

Source: SCP10, arXiv:1001.3807, regional contraction algebra, lines 1765–1920
and 1935–1957, and Section 7, lines 2977–3019. These are finite-simple-graph
contraction identities. No boundary-state equivalence, Gram identity, energy,
or parent-Hamiltonian membership statement is asserted.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X : Type*} [Fintype X]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
private abbrev RE (R : Finset V) := {e : Edge Γ // IsRegionIncidentEdge R e}

private def incidentSplit (R : Finset V) : RE (Γ := Γ) R ≃ RI (Γ := Γ) R ⊕ RB (Γ := Γ) R where
  toFun e := if h : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R then .inl ⟨e.1, h⟩ else
    .inr ⟨e.1, by
      rcases e.2 with ht | hh
      · exact Or.inl ⟨ht, fun hh => h ⟨ht, hh⟩⟩
      · exact Or.inr ⟨fun ht => h ⟨ht, hh⟩, hh⟩⟩
  invFun
    | .inl e => ⟨e.1, Or.inl e.2.1⟩
    | .inr e => ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩
  left_inv e := by
    dsimp only
    split_ifs <;> rfl
  right_inv e := by
    rcases e with e | e
    · simp [e.2]
    · have hn : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
        rcases e.2 with ht | hh
        · exact fun h => ht.2 h.2
        · exact fun h => hh.1 h.1
      simp [hn]

/-- The native incident virtual labels split into internal and crossing labels.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
def graphRegionIncidentConfigEquiv (R : Finset V) :
    (RE (Γ := Γ) R → X) ≃ (RI (Γ := Γ) R → X) × (RB (Γ := Γ) R → X) :=
  ((incidentSplit R).arrowCongr (Equiv.refl X)).trans
    (Equiv.sumArrowEquivProdArrow _ _ X)

open scoped Classical in
/-- The actual open-region coefficient with a vertex-dependent physical alphabet.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
def graphOpenRegionNetwork {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) (R : Finset V)
    (θ : RB (Γ := Γ) R → X) (σ : (v : RV R) → P v.1) : ℂ :=
  ∑ η : RE (Γ := Γ) R → X,
    if (fun e : RB (Γ := Γ) R => η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = θ then
      ∏ v : RV R, a v.1 (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) (σ v)
    else 0

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype X] in
/-- The internal factor reads the same native incident-edge label.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
@[simp] theorem graphRegionIncidentConfigEquiv_apply_internal (R : Finset V)
    (η : RE (Γ := Γ) R → X) (e : RI (Γ := Γ) R) :
    (graphRegionIncidentConfigEquiv R η).1 e = η ⟨e.1, Or.inl e.2.1⟩ := rfl

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype X] in
/-- The boundary factor reads the same native crossing-edge label.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
@[simp] theorem graphRegionIncidentConfigEquiv_apply_boundary (R : Finset V)
    (η : RE (Γ := Γ) R → X) (e : RB (Γ := Γ) R) :
    (graphRegionIncidentConfigEquiv R η).2 e =
      η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩ := rfl

/-- Fixing the crossing labels leaves exactly one sum over internal bond labels.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
theorem graphOpenRegionNetwork_eq_sum_internal {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) (R : Finset V)
    (θ : RB (Γ := Γ) R → X) (σ : (v : RV R) → P v.1) :
    graphOpenRegionNetwork a R θ σ =
      ∑ ξ : RI (Γ := Γ) R → X, ∏ v : RV R,
        a v.1 (fun e => (graphRegionIncidentConfigEquiv R).symm (ξ, θ)
          ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) (σ v) := by
  classical
  unfold graphOpenRegionNetwork
  rw [← (graphRegionIncidentConfigEquiv (X := X) R).symm.sum_comp, Fintype.sum_prod_type]
  have hb (ξ : RI (Γ := Γ) R → X) (ζ : RB (Γ := Γ) R → X) :
      (fun e : RB (Γ := Γ) R => (graphRegionIncidentConfigEquiv R).symm (ξ, ζ)
        ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = ζ := by
    funext e
    rw [← graphRegionIncidentConfigEquiv_apply_boundary R
      ((graphRegionIncidentConfigEquiv R).symm (ξ, ζ)) e, Equiv.apply_symm_apply]
  simp_rw [hb]
  simp

/-- Numbering the virtual alphabet gives the existing actual open-region coefficient.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
theorem openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) (σ : RegionPhysicalConfig (d := d) R) :
    openRegionWeight (groupBondTensor a) R (fun e => Fintype.equivFin X (θ e)) σ =
      graphOpenRegionNetwork a R θ σ := by
  classical
  let E : (RE (Γ := Γ) R → X) ≃ RegionIncidentConfig (groupBondTensor a) R :=
    Equiv.piCongrRight fun _ => Fintype.equivFin X
  rw [openRegionWeight, ← E.sum_comp]
  unfold graphOpenRegionNetwork
  apply Finset.sum_congr rfl
  intro η _
  have hlabel : regionIncidentBoundaryLabel (groupBondTensor a) R (E η) =
      (fun e => Fintype.equivFin X (θ e)) ↔
      (fun e : RB (Γ := Γ) R => η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = θ :=
    (Equiv.piCongrRight (fun _ : RB (Γ := Γ) R => Fintype.equivFin X)).injective.eq_iff
  simp only [hlabel]
  split_ifs
  · simp only [regionIncidentWeight, groupBondTensor, E, Equiv.piCongrRight_apply,
      Pi.map_apply, Equiv.symm_apply_apply]
  · rfl
end TNLean.PEPS
