/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionTreeGauge
import TNLean.PEPS.RegularProjectorOpenRegion

/-!
# Vertex gauges in actual regular-region contractions

A vertex gauge changes each internal operator to its residual and transfers all
crossing operators into the prescribed boundary labels. Reindexing the actual
incident-bond sum by these reversible label changes leaves the physical column
unchanged whenever the original sites are invariant under simultaneous regular
translation. If every internal residual is the identity, the result is the
original untwisted block evaluated at the transported boundary configuration.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, accessible virtual
systems and controlled coordinate changes, local source lines 1765–1920.
These are contraction identities with arbitrary crossing operators; no
connectedness, flatness, or Gram identity is assumed in the gauge identity.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V]
variable {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- Residual operators on internal edges, with identity operators on every
other edge. Source: SCP10, controlled regular blocking, lines 1765–1920. -/
def regularRegionGaugeEdgeOperators (R : Finset V) (k : {v : V // v ∈ R} → G)
    (u : Edge Γ → G) : Edge Γ → G :=
  fun e => if h : e.1.1 ∈ R ∧ e.1.2 ∈ R then
    regularRegionGaugeResidual R k u ⟨e, h⟩ else 1

/-- The reversible change of incident reference labels. On an internal edge it
uses the inverse gauge at the tail; on a crossing edge it is the prescribed
boundary transport. Source: SCP10, lines 1765–1920. -/
def regularRegionGaugeIncidentLabels (R : Finset V) (k : {v : V // v ∈ R} → G)
    (u : Edge Γ → G) :
    ({e : Edge Γ // IsRegionIncidentEdge R e} → G) ≃
      ({e : Edge Γ // IsRegionIncidentEdge R e} → G) :=
  Equiv.piCongrRight fun e => Equiv.mulLeft
    (if ht : e.1.1.1 ∈ R then (k ⟨e.1.1.1, ht⟩)⁻¹ else
      (k ⟨e.1.1.2, e.2.resolve_left ht⟩)⁻¹ * u e.1)

/-- Restricting the incident-label change to crossing edges gives the existing
boundary transport. -/
theorem regularRegionGaugeIncidentLabels_boundary (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    (fun e : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
      regularRegionGaugeIncidentLabels R k u η
        ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) =
      regularRegionBoundaryTransport R k u
        (fun e => η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) := by
  funext e
  rfl

/-- The transformed twisted half-edge labels at a region vertex are the original
ones multiplied by its inverse gauge. Source: SCP10, lines 1765–1920. -/
theorem regularRegionGaugeIncidentLabels_twisted (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G) (v : {v : V // v ∈ R}) :
    regularTwistedLabels (regularRegionGaugeEdgeOperators R k u) v.1
        (fun e => regularRegionGaugeIncidentLabels R k u η
          ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) =
      fun e => (k v)⁻¹ * regularTwistedLabels u v.1
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) e := by
  funext e
  rcases e.2 with ht | hh
  · have hv : v.1 ≠ e.1.1.2 := by
      exact fun h => (ne_of_lt e.1.2.1) (ht.trans h)
    have htail : e.1.1.1 ∈ R := (congrArg (fun x => x ∈ R) ht).mpr v.2
    simp only [regularTwistedLabels, ite_eq_right hv, regularRegionGaugeIncidentLabels,
      Equiv.piCongrRight_apply, Pi.map_apply, Equiv.mulLeft, dite_eq_left htail]
    exact congrArg (fun x => x⁻¹ * η ⟨e.1,
      isRegionIncidentEdge_of_regionVertex R v e⟩) (congrArg k (Subtype.ext ht))
  · have hhead : e.1.1.2 ∈ R := (congrArg (fun x => x ∈ R) hh).mpr v.2
    by_cases htail : e.1.1.1 ∈ R
    · have hboth : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R := ⟨htail, hhead⟩
      simp only [regularTwistedLabels, ite_eq_left hh.symm, regularRegionGaugeEdgeOperators,
        dite_eq_left hboth, regularRegionGaugeResidual,
        regularRegionGaugeIncidentLabels, Equiv.piCongrRight_apply,
        Pi.map_apply, Equiv.mulLeft, dite_eq_left htail]
      have hk : k ⟨e.1.1.2, hhead⟩ = k v := congrArg k (Subtype.ext hh)
      rw [hk]
      change ((k v)⁻¹ * u e.1 * k ⟨e.1.1.1, htail⟩) *
        ((k ⟨e.1.1.1, htail⟩)⁻¹ * η _) = _
      group
    · have hboth : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := fun h => htail h.1
      simp only [regularTwistedLabels, ite_eq_left hh.symm, regularRegionGaugeEdgeOperators,
        dite_eq_right hboth, one_mul, regularRegionGaugeIncidentLabels,
        Equiv.piCongrRight_apply, Pi.map_apply, Equiv.mulLeft, dite_eq_right htail]
      have hk : k ⟨e.1.1.2, hhead⟩ = k v := congrArg k (Subtype.ext hh)
      rw [hk]
      change ((k v)⁻¹ * u e.1) * η _ = _
      exact mul_assoc _ _ _

variable [Fintype V] [DecidableRel Γ.Adj] [Fintype G] {d : ℕ}

/-- An arbitrary vertex gauge reduces the internal operators of the actual
region contraction and transports its boundary labels. Only the original local
regular invariance is required. Source: SCP10, lines 1765–1920. -/
theorem openRegionWeight_regularRegionGauge
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (R : Finset V) (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (σ : RegionPhysicalConfig (d := d) R) :
    openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
        (fun e => Fintype.equivFin G (θ e)) σ =
      openRegionWeight (groupBondTensor
        (regularTwistedSite a (regularRegionGaugeEdgeOperators R k u))) R
        (fun e => Fintype.equivFin G (regularRegionBoundaryTransport R k u θ e)) σ := by
  classical
  unfold openRegionWeight
  rw [← Equiv.sum_comp (regularRegionIncidentConfigEquiv (regularTwistedSite a u) R),
    ← Equiv.sum_comp (regularRegionIncidentConfigEquiv
      (regularTwistedSite a (regularRegionGaugeEdgeOperators R k u)) R)]
  conv_rhs => rw [← Equiv.sum_comp (regularRegionGaugeIncidentLabels R k u)]
  apply Finset.sum_congr rfl
  intro η _
  simp only [regionIncidentBoundaryLabel_regularGroup_iff,
    regularRegionGaugeIncidentLabels_boundary,
    (regularRegionBoundaryTransport R k u).injective.eq_iff]
  split_ifs
  · unfold regionIncidentWeight
    apply Finset.prod_congr rfl
    intro v _
    simp only [groupBondTensor, regularRegionIncidentConfigEquiv,
      Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply, regularTwistedSite]
    rw [regularRegionGaugeIncidentLabels_twisted]
    exact (ha (k v)⁻¹ v.1 _ (σ v)).symm
  · rfl

/-- When all internal residual operators are identities, the actual twisted
region is the original untwisted block at the transported boundary label.
Source: SCP10, lines 1765–1920. -/
theorem openRegionWeight_eq_untwisted_of_regularRegionGaugeResidual_eq_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (R : Finset V) (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (hflat : ∀ e, regularRegionGaugeResidual R k u e = 1)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (σ : RegionPhysicalConfig (d := d) R) :
    openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
        (fun e => Fintype.equivFin G (θ e)) σ =
      openRegionWeight (groupBondTensor a) R
        (fun e => Fintype.equivFin G (regularRegionBoundaryTransport R k u θ e)) σ := by
  rw [openRegionWeight_regularRegionGauge a ha R k u θ σ]
  have hop : regularRegionGaugeEdgeOperators R k u = fun _ => 1 := by
    funext e
    unfold regularRegionGaugeEdgeOperators
    split_ifs
    · exact hflat _
    · rfl
  have hsite : regularTwistedSite a (fun _ => 1) = a := by
    funext v η s
    unfold regularTwistedSite
    congr 1
    funext e
    simp only [regularTwistedLabels, one_mul, ite_self]
  rw [hop, hsite]

end TNLean.PEPS
