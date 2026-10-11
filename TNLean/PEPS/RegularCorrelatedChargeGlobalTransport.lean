/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularEdgeChargeContraction
import TNLean.PEPS.GraphBondContraction
import TNLean.PEPS.RegularCoherentGlobalTransport
import TNLean.PEPS.RegularWeightedOpenContraction

/-!
# Actual correlated charge coefficients across a physical cut

The remote reference remains summed in the actual globally contracted tensor.
The correlation is obtained by resolving only that reference, rather than by
replacing the character pair with independent character insertions.

Source: SCP10, arXiv:1001.3807, lines 2505–2535 and 2560–2581.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- A literal diagonal insertion with its tail in the region is the actual
weighted open contraction. Source: SCP10, lines 2449–2486 and 2560–2581. -/
theorem openRegionWeight_regularEdgeCharacterSite_eq_weighted
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (u : Edge Γ → G) (e : Edge Γ) (he : e.1.1 ∈ R)
    (χ : G → ℂ) (p : G) (θ : RB (Γ := Γ) R → G) :
    openRegionWeight (groupBondTensor
        (regularEdgeCharacterSite (regularTwistedSite a u) e χ p)) R
        (fun f => Fintype.equivFin G (θ f)) =
      regularWeightedOpenRegionWeight a R u
        (fun η => χ (p * η ⟨e,Or.inl he⟩)) θ := by
  classical
  funext σ
  rw [openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork]
  unfold graphOpenRegionNetwork regularWeightedOpenRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · have hf : ∀ w : {v : V // v ∈ R},
        regularEdgeCharacterSite (regularTwistedSite a u) e χ p w.1
          (fun f => η ⟨f.1,isRegionIncidentEdge_of_regionVertex R w f⟩) (σ w) =
        (if w.1 = e.1.1 then χ (p * η ⟨e,Or.inl he⟩) else 1) *
          regularTwistedSite a u w.1
            (fun f => η ⟨f.1,isRegionIncidentEdge_of_regionVertex R w f⟩) (σ w) := by
      intro w
      unfold regularEdgeCharacterSite
      split_ifs <;> simp
    simp_rw [hf]
    rw [Finset.prod_mul_distrib]
    have hi : ∀ w : {v : V // v ∈ R}, w.1 = e.1.1 ↔ w = ⟨e.1.1,he⟩ := by
      intro w
      exact (Subtype.ext_iff : w = ⟨e.1.1,he⟩ ↔ w.1 = e.1.1).symm
    simp_rw [hi]
    rw [Fintype.prod_ite_eq']
    rfl
  · rfl

omit [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem prod_character_site
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (e : Edge Γ) (χ : G → ℂ) (p : G)
    (β : (v : V) → IncidentEdge Γ v → G) (σ : V → Fin d) :
    (∏ v, regularEdgeCharacterSite a e χ p v (β v) (σ v)) =
      χ (p * β e.1.1 (regularEdgeTailLeg e)) * ∏ v, a v (β v) (σ v) := by
  classical
  have hf : ∀ v,
      regularEdgeCharacterSite a e χ p v (β v) (σ v) =
        (if v = e.1.1 then χ (p * β e.1.1 (regularEdgeTailLeg e)) else 1) *
          a v (β v) (σ v) := by
    intro v
    unfold regularEdgeCharacterSite
    split_ifs with h
    · subst v
      rfl
    · simp
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

/-- Resolve only the remote shared label in the actual closed tensor contraction.
Source: SCP10, literal correlated charge-pair state, lines 2505–2535. -/
def regularCorrelatedChargeState
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (u : Edge Γ → G) (e₀ e₁ : Edge Γ) (χ : G → ℂ) (p k : G) :
    (V → Fin d) → ℂ :=
  ∑ q : G, stateCoeff (groupBondTensor
    (regularEdgeCharacterSite
      (regularEdgeCharacterSite (regularTwistedSite a u) e₀
        (fun t => χ (p * q⁻¹ * k * t)) 1)
      e₁ (fun t => if t = q then 1 else 0) 1))

/-- The remote-label resolution retains the literal joint character weight.
Source: SCP10, lines 2505–2535. No product of independent character factors appears. -/
theorem regularCorrelatedChargeState_apply
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (u : Edge Γ → G) (e₀ e₁ : Edge Γ) (χ : G → ℂ) (p k : G) (σ : V → Fin d) :
    regularCorrelatedChargeState a u e₀ e₁ χ p k σ =
      ∑ η : Edge Γ → G, χ (p * (η e₁)⁻¹ * k * η e₀) *
        ∏ v, a v (regularTwistedLabels u v (fun f => η f.1)) (σ v) := by
  classical
  simp only [regularCorrelatedChargeState, Finset.sum_apply,
    stateCoeff_groupBondTensor_eq_graphBondNetwork, graphBondNetwork]
  simp_rw [prod_character_site]
  simp only [regularEdgeTailLeg, one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, mul_assoc, regularTwistedSite]

/-- A uniform action on the literal charge columns passes through the actual
closed contraction while the remote reference remains summed. Source: SCP10,
lines 2505–2535 and 2560–2581; auxiliary linear contraction identity. -/
theorem regionLocalTerm_mulVec_regularCorrelatedChargeState
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (u : Edge Γ → G) (e₀ e₁ : Edge Γ)
    (h₀ : e₀.1.1 ∈ R) (h₁ : e₁.1.1 ∉ R) (k : G)
    (W : Matrix ({v : V // v ∈ R} → Fin d) ({v : V // v ∈ R} → Fin d) ℂ)
    (hcols : ∀ (χ : G → ℂ) (p q : G) (θ : RB (Γ := Γ) R → G),
      W *ᵥ regularWeightedOpenRegionWeight a R u
          (fun η => χ (p * q⁻¹ * η ⟨e₀, Or.inl h₀⟩)) θ =
        regularWeightedOpenRegionWeight a R u
          (fun η => χ (p * q⁻¹ * k⁻¹ * η ⟨e₀, Or.inl h₀⟩)) θ)
    (χ : G → ℂ) (p : G) :
    regionLocalTerm R W *ᵥ regularCorrelatedChargeState a u e₀ e₁ χ p 1 =
      regularCorrelatedChargeState a u e₀ e₁ χ p k⁻¹ := by
  classical
  unfold regularCorrelatedChargeState
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro q _
  let A := regularEdgeCharacterSite
    (regularEdgeCharacterSite (regularTwistedSite a u) e₀
      (fun t => χ (p * q⁻¹ * 1 * t)) 1)
    e₁ (fun t => if t = q then 1 else 0) 1
  let B := regularEdgeCharacterSite
    (regularEdgeCharacterSite (regularTwistedSite a u) e₀
      (fun t => χ (p * q⁻¹ * k⁻¹ * t)) 1)
    e₁ (fun t => if t = q then 1 else 0) 1
  change regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor A) =
    stateCoeff (groupBondTensor B)
  apply regionLocalTerm_mulVec_stateCoeff_of_openColumns R A B W
  · intro μ
    let θ : RB (Γ := Γ) R → G := fun f => (Fintype.equivFin G).symm (μ f)
    have hμ : (fun f => Fintype.equivFin G (θ f)) = μ := by
      funext f
      exact (Fintype.equivFin G).apply_symm_apply (μ f)
    have hin (c : G → ℂ) :
        openRegionWeight (groupBondTensor
          (regularEdgeCharacterSite
            (regularEdgeCharacterSite (regularTwistedSite a u) e₀ c 1)
            e₁ (fun t => if t = q then 1 else 0) 1)) R μ =
        openRegionWeight (groupBondTensor
          (regularEdgeCharacterSite (regularTwistedSite a u) e₀ c 1)) R μ := by
      apply openRegionWeight_groupBondTensor_congr_on
      intro v hv
      funext α s
      have hne : v ≠ e₁.1.1 := fun h => h₁ (h ▸ hv)
      simp only [regularEdgeCharacterSite, hne, ↓reduceDIte]
    have hA := hin (fun t => χ (p * q⁻¹ * 1 * t))
    have hB := hin (fun t => χ (p * q⁻¹ * k⁻¹ * t))
    change W *ᵥ openRegionWeight (groupBondTensor A) R μ =
      openRegionWeight (groupBondTensor B) R μ
    rw [hA,hB,← hμ]
    rw [openRegionWeight_regularEdgeCharacterSite_eq_weighted a R u e₀ h₀,
      openRegionWeight_regularEdgeCharacterSite_eq_weighted a R u e₀ h₀]
    simpa only [one_mul, mul_one] using hcols χ p q θ
  · intro v hv
    funext α s
    have hne : v ≠ e₀.1.1 := fun h => hv (h.symm ▸ h₀)
    simp only [A,B,regularEdgeCharacterSite,hne,↓reduceDIte]

end TNLean.PEPS
