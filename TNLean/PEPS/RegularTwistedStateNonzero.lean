/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularProjectorTwistedRegion
import TNLean.PEPS.RegularTorusEntropy
import TNLean.PEPS.NormalComparisonScalar

/-!
# Nonvanishing of actual regular-bond states with inserted operators

The identity boundary column of each actual twisted canonical projector block
has a nonzero coefficient. Choose every incident bond label and vertex translation
to be the identity, and choose the physical half-edge row to be the resulting
inserted labels. This gives a positive term in the finite indicator expansion;
all other terms are nonnegative. The derived local physical inverse of a regular
G-injective tensor exposes this canonical column. Consequently the original
open-region vector, and in particular the globally contracted state, is nonzero.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`eq:2d:peps-with-ug-uh`, lines 1515–1525; the accessibility argument of
lines 1765–1820; and the flux-string measurements of Theorem 6.15,
lines 2217–2267. Nonvanishing is an auxiliary consequence of these actual
coefficient formulas, not an assumed state or region Gram identity.

**Scope restriction (regular-bond states):** The argument uses regular virtual
representations; the native torus specialization has periods at least three.
Arbitrary inserted group elements are allowed algebraically. No assertion of
parent-Hamiltonian ground-state membership is made; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators ComplexOrder Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The identity boundary column of an actual twisted canonical block is nonzero.
Source: SCP10, actual projector contraction, lines 1765–1820 and 1935–1957. -/
theorem regularProjectorTwistedRegionMatrix_one_column_ne_zero (R : Finset V) (u : Edge Γ → G) :
    (fun α => regularProjectorTwistedRegionMatrix (G := G) R u α (fun _ => 1)) ≠ 0 := by
  classical
  let α : RegionHalfEdgeConfig (Γ := Γ) G R :=
    fun w => regularTwistedLabels u w.1 (fun _ => 1)
  let θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G := fun _ => 1
  let P (η : {f : Edge Γ // IsRegionIncidentEdge R f} → G)
      (q : {w : V // w ∈ R} → G) : Prop :=
    (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ ∧
      ∀ w : {w : V // w ∈ R}, α w = q w • regularTwistedLabels u w.1
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)
  have hpos : 0 < ∑ η, ∑ q, if P η q then (1 : ℂ) else 0 := by
    apply Finset.sum_pos'
    · intro η hη
      apply Finset.sum_nonneg
      intro q hq
      split_ifs <;> norm_num
    · refine ⟨fun _ => 1, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos'
      · intro q hq
        split_ifs <;> norm_num
      · refine ⟨fun _ => 1, Finset.mem_univ _, ?_⟩
        have hp : P (fun _ => 1) (fun _ => 1) := by
          exact ⟨rfl, fun w => by simp only [α, one_smul]⟩
        simp only [hp, ↓reduceIte]
        norm_num
  have hentry : regularProjectorTwistedRegionMatrix R u α θ ≠ 0 := by
    rw [regularProjectorTwistedRegionMatrix_apply]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr
      Fintype.card_ne_zero))) (ne_of_gt hpos)
  intro hzero
  exact hentry (congrFun hzero α)

variable {d : ℕ}
omit [DecidableEq G] in
/-- Derived local physical inverses preserve the nonzero canonical column.
Source: SCP10, accessibility argument, lines 1765–1820. -/
theorem openRegionWeight_regularTwistedSite_ne_zero_of_isGInjective
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) (u : Edge Γ → G) :
    openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
      (fun _ => Fintype.equivFin G 1) ≠ 0 := by
  classical
  obtain ⟨F, hF⟩ := exists_regularProjectorTwistedRegionMatrix_of_isGInjective a ha
  intro hz
  apply regularProjectorTwistedRegionMatrix_one_column_ne_zero R u
  funext α
  rw [← hF R u α (fun _ => 1), hz, map_zero]

private theorem openRegionWeight_univ_apply (A : Tensor Γ d)
    (μ : RegionBoundaryConfig A Finset.univ)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ : Finset V)) :
    openRegionWeight A Finset.univ μ τ =
      stateCoeff A (fun v => τ ⟨v, Finset.mem_univ v⟩) := by
  classical
  have hm : regionExteriorMultiplicity A Finset.univ = 1 := by
    rw [regionExteriorMultiplicity_eq_prod]
    simp [IsRegionIncidentEdge]
  have h := regionBlockedWeight_eq_exterior_mul_openRegionWeight A Finset.univ μ τ
  rw [hm, Nat.cast_one, one_mul, regionBlockedWeight_univ] at h
  exact h.symm

omit [DecidableEq G] in
/-- A regular G-injective family has a nonzero actual closed state for every
inserted group-valued bond assignment. Source: auxiliary consequence of SCP10,
lines 1515–1525 and 1765–1820, supporting Theorem 6.15, lines 2217–2267. -/
theorem stateCoeff_regularTwistedSite_ne_zero_of_isGInjective
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (u : Edge Γ → G) :
    stateCoeff (groupBondTensor (regularTwistedSite a u)) ≠ 0 := by
  classical
  intro hz
  apply openRegionWeight_regularTwistedSite_ne_zero_of_isGInjective a ha Finset.univ u
  funext τ
  rw [openRegionWeight_univ_apply, hz]
  rfl

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
/-- Every actual native regular G-isometric torus state with inserted bond
operators is nonzero. This includes all four plaquette flux-string attachment sides.
Source: auxiliary nonvanishing for SCP10, Theorem 6.15, lines 2217–2267. -/
theorem IsGIsometric.stateCoeff_torusRegularTwistedSite_ne_zero
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (u : Edge (torusGraph width height) → G) :
    stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) ≠ 0 :=
  stateCoeff_regularTwistedSite_ne_zero_of_isGInjective (torusIncidentSite a)
    (fun v => (ha.isGIsometric_torusIncidentSite v).toIsGInjective) u
end TNLean.PEPS
