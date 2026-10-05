/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGraphPhysicalBlocking

/-!
# Original regular sites with explicit surplus Bell registers

Adjoining an identity map on the relative coordinates of a regular bond bundle
retains the original physical tensor and its isometry factor. Contracting these
sites gives precisely the original graph state times the residual Bell product.
The identity and the local Gram operator are derived from the coefficient sums.

Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6, lines 1825–1909.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G : Type*} [Group G]
variable (K : Type*)

/-- Read the regular reference label and every relative surplus label.
Source: SCP10, the change of variables in lines 1840–1873. -/
def regularSurplusCoordinates (ι : Type*) :
    (ι → G × (K → G)) ≃ (ι → G) × (ι → K → G) where
  toFun η := (fun i => (η i).1, fun i => (η i).1⁻¹ • (η i).2)
  invFun p i := (p.1 i, p.1 i • p.2 i)
  left_inv η := by funext i; simp
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      simp

/-- Simultaneous regular translation affects only the reference coordinate.
Source: SCP10, regular-pair separation in lines 1840–1873. -/
theorem regularSurplusCoordinates_smul {ι : Type*} (g : G) (η : ι → G × (K → G)) :
    regularSurplusCoordinates K ι (g • η) =
      (g • (regularSurplusCoordinates K ι η).1, (regularSurplusCoordinates K ι η).2) := by
  apply Prod.ext
  · rfl
  · funext i k
    simp [regularSurplusCoordinates, Pi.smul_apply, mul_inv_rev, mul_assoc]

private theorem regularSurplusCoordinates_translation_iff {ι : Type*}
    (η θ : ι → G × (K → G)) (g : G) :
    η = g • θ ↔
      (regularSurplusCoordinates K ι η).1 = g • (regularSurplusCoordinates K ι θ).1 ∧
        (regularSurplusCoordinates K ι η).2 = (regularSurplusCoordinates K ι θ).2 := by
  rw [← (regularSurplusCoordinates K ι).injective.eq_iff,
    regularSurplusCoordinates_smul, Prod.ext_iff]

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {P : V → Type*}
variable [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K]

/-- Keep the original physical tensor on the reference regular labels and
copy the relative surplus labels into additional physical registers.
Source: SCP10, the identity tensors in Observation 6.6. -/
def regularGraphSurplusSite
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (v : V) (η : IncidentEdge Γ v → G × (K → G))
    (s : P v × (IncidentEdge Γ v → K → G)) : ℂ :=
  a v (regularSurplusCoordinates K _ η).1 s.1 *
    if s.2 = (regularSurplusCoordinates K _ η).2 then 1 else 0

variable [∀ v, Fintype (P v)]

private theorem regularGraphSurplusSite_gram
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (v : V) (η θ : IncidentEdge Γ v → G × (K → G)) :
    (∑ s : P v × (IncidentEdge Γ v → K → G),
      star (regularGraphSurplusSite K a v η s) * regularGraphSurplusSite K a v θ s) =
      (∑ s : P v,
        star (a v (regularSurplusCoordinates K _ η).1 s) *
          a v (regularSurplusCoordinates K _ θ).1 s) *
        if (regularSurplusCoordinates K _ η).2 = (regularSurplusCoordinates K _ θ).2
          then 1 else 0 := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp only [regularGraphSurplusSite]
  rw [Finset.sum_eq_single (regularSurplusCoordinates K _ η).2]
  · simp only [ite_true, mul_one]
    split_ifs <;> simp
  · intro r _ hr
    simp only [hr, ite_false, mul_zero, star_zero, zero_mul]
  · simp

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The original regular G-isometric site remains G-isometric after adjoining
the explicit surplus registers. Its positive isometry factor is unchanged.
Source: SCP10, Observations 6.5–6.6. -/
theorem isGIsometric_regularGraphSurplusSite
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (v : V) :
    IsGIsometric (graphIncidentRepresentation (regularBundleMatrix K) v)
      (regularSiteMap (regularGraphSurplusSite K a v)) := by
  classical
  obtain ⟨c, hc, hgram⟩ := (ha v).exists_regularSiteGram
  have htrans (g : G) (η : IncidentEdge Γ v → G × (K → G))
      (s : P v × (IncidentEdge Γ v → K → G)) :
      regularGraphSurplusSite K a v (g • η) s = regularGraphSurplusSite K a v η s := by
    simp only [regularGraphSurplusSite, regularSurplusCoordinates_smul]
    rw [(ha v).toIsGInjective.regularSiteMap_translation]
  have hinv (g : G) : regularSiteMap (regularGraphSurplusSite K a v) ∘ₗ
      graphIncidentRepresentation (regularBundleMatrix K) v g =
        regularSiteMap (regularGraphSurplusSite K a v) := by
    apply LinearMap.ext
    intro x
    funext s
    change (∑ η, regularGraphSurplusSite K a v η s *
      (graphIncidentRepresentation (regularBundleMatrix K) v g x) η) =
        ∑ η, regularGraphSurplusSite K a v η s * x η
    simp only [graphIncidentRepresentation_regularBundle_apply]
    rw [← Equiv.sum_comp (MulAction.toPermHom G (IncidentEdge Γ v → G × (K → G)) g)]
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, inv_smul_smul, htrans]
  apply isGIsometric_of_coordinateAdjoint_comp hinv hc
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, coordinateAdjoint, LinearMap.toMatrix'_toLin',
    toMatrix_regularSiteMap, map_smul]
  rw [← regularSiteMap_graphAveragingSite, toMatrix_regularSiteMap]
  ext η θ
  change (∑ s : P v × (IncidentEdge Γ v → K → G),
    star (regularGraphSurplusSite K a v η s) * regularGraphSurplusSite K a v θ s) =
      (c : ℂ) * graphAveragingSite (regularBundleMatrix K) v θ η
  rw [regularGraphSurplusSite_gram, hgram]
  have hcanonical : graphAveragingSite (regularBundleMatrix (G := G) K) v θ η =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, if η = g • θ then 1 else 0 := by
    change (Fintype.card G : ℂ)⁻¹ *
      (∑ g : G, graphIncidentMatrix (regularBundleMatrix K) v g η θ) = _
    simp only [graphIncidentMatrix_regularBundle_apply]
  rw [hcanonical]
  simp_rw [regularSurplusCoordinates_translation_iff]
  by_cases hr : (regularSurplusCoordinates K _ η).2 = (regularSurplusCoordinates K _ θ).2
  · simp only [hr, and_true, ite_true, mul_one, div_eq_mul_inv, mul_assoc]
  · simp only [hr, and_false, ite_false, mul_zero, Finset.sum_const_zero]

omit [∀ v, Fintype (P v)] in
omit [Group G] in
private theorem sum_identity_incident_eq_residualBell
    (τ : (v : V) → IncidentEdge Γ v → K → G) :
    (∑ r : Edge Γ → K → G, ∏ v,
      if τ v = (fun f => r f.1) then (1 : ℂ) else 0) =
        regularGraphResidualBell K τ := by
  classical
  have h (v : V) (r : Edge Γ → K → G) :
      (if τ v = (fun f => r f.1) then (1 : ℂ) else 0) =
        ∏ f : IncidentEdge Γ v, if τ v f = r f.1 then 1 else 0 := by
    simp only [Fintype.prod_boole, ← funext_iff]
  simp_rw [h, prod_incident_eq_prod_edge]
  let F (e : Edge Γ) (r : K → G) : ℂ :=
    (if τ e.1.1 (edgeLeftIncident e) = r then 1 else 0) *
      (if τ e.1.2 (edgeRightIncident e) = r then 1 else 0)
  change (∑ r : Edge Γ → K → G, ∏ e, F e (r e)) = _
  rw [← Fintype.prod_sum F]
  unfold regularGraphResidualBell
  apply Finset.prod_congr rfl
  intro e _
  simp [F, eq_comm]

omit [∀ v, Fintype (P v)] in
/-- The actual augmented contraction is the original tensor network times
the unnormalized surplus Bell product, with all physical indices retained.
Source: SCP10, Observation 6.6, the original-tensor coarse factor. -/
theorem graphBondNetwork_regularGraphSurplusSite
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (σ : (v : V) → P v) (τ : (v : V) → IncidentEdge Γ v → K → G) :
    graphBondNetwork (regularGraphSurplusSite K a) (fun v => (σ v, τ v)) =
      graphBondNetwork a σ * regularGraphResidualBell K τ := by
  classical
  rw [graphBondNetwork, ← (regularSurplusCoordinates K (Edge Γ)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, regularGraphSurplusSite, regularSurplusCoordinates,
    Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, inv_smul_smul, Finset.prod_mul_distrib]
  simp_rw [← Finset.mul_sum]
  calc
    _ = (∑ x : Edge Γ → G, ∏ v, a v (fun f => x f.1) (σ v)) *
        (∑ r : Edge Γ → K → G, ∏ v,
          if τ v = (fun f => r f.1) then (1 : ℂ) else 0) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [sum_identity_incident_eq_residualBell]; rfl

end TNLean.PEPS
