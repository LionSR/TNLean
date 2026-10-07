/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCorrelatedChargeGlobalTransport
import TNLean.PEPS.RegularPhysicalChargePairCreation
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove
import TNLean.PEPS.RegularTwistedStateNonzero

/-!
# Preparing a literal correlated charge pair in the closed contraction

The two retained bond labels are resolved inside the actual open contraction.
Uniform preparation of these columns consequently prepares their closed coherent
contraction. The operation acts only on the chosen region and preserves its
norm. Source: SCP10, arXiv:1001.3807, lines 2505–2558.

**Scope restriction (finite-region preparation):** The preparation acts on a
supplied finite region. It does not identify the prescribed flux-string
background, a complete geometric charge–flux braid, or the subsequent reunion
measurement of lines 2560–2615. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- Resolving the partner label in the actual regional tensor gives the literal
correlated column, not two independent character weights.
Source: SCP10, `eq:anyons:chargeon-pair-state`, lines 2505–2535. -/
theorem sum_openRegionWeight_regularCorrelatedChargePair
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (u : Edge Γ → G) (e₀ e₁ : RI (Γ := Γ) R)
    (χ : G → ℂ) (p : G) (θ : RB (Γ := Γ) R → G) :
    (∑ q : G, openRegionWeight (groupBondTensor
      (regularEdgeCharacterSite
        (regularEdgeCharacterSite (regularTwistedSite a u) e₀.1
          (fun t => χ (p * q⁻¹ * t)) 1)
        e₁.1 (fun t => if t = q then 1 else 0) 1)) R
      (fun f => Fintype.equivFin G (θ f))) =
    fun s => regularChargePairOpenRegionMatrix (regularTwistedSite a u)
      R e₀ e₁ χ p s θ := by
  classical
  funext σ
  simp only [Finset.sum_apply]
  simp_rw [openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork]
  unfold graphOpenRegionNetwork regularChargePairOpenRegionMatrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  split_ifs with hb
  · have hp (e : RI (Γ := Γ) R) (b) (f : G → ℂ) :
        (∏ w : {v : V // v ∈ R}, regularEdgeCharacterSite b e.1 f 1 w.1
          (fun j => η ⟨j.1, isRegionIncidentEdge_of_regionVertex R w j⟩) (σ w)) =
        f (η ⟨e.1, Or.inl e.2.1⟩) *
          ∏ w : {v : V // v ∈ R}, b w.1
            (fun j => η ⟨j.1, isRegionIncidentEdge_of_regionVertex R w j⟩) (σ w) := by
      have hf : ∀ w : {v : V // v ∈ R},
          regularEdgeCharacterSite b e.1 f 1 w.1
            (fun j => η ⟨j.1, isRegionIncidentEdge_of_regionVertex R w j⟩) (σ w) =
          (if w = ⟨e.1.1.1, e.2.1⟩ then f (η ⟨e.1, Or.inl e.2.1⟩) else 1) *
            b w.1 (fun j => η ⟨j.1, isRegionIncidentEdge_of_regionVertex R w j⟩)
              (σ w) := by
        intro w
        unfold regularEdgeCharacterSite
        by_cases h : w.1 = e.1.1.1
        · have hw : w = ⟨e.1.1.1, e.2.1⟩ := Subtype.ext h
          subst w
          simp only [↓reduceDIte, ↓reduceIte, one_mul]
        · have hw : w ≠ ⟨e.1.1.1, e.2.1⟩ := fun hw => h (congrArg Subtype.val hw)
          simp only [h, hw, ↓reduceDIte, ↓reduceIte, one_mul]
      simp_rw [hf]
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    simp_rw [hp e₁, hp e₀]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, regularTwistedSite]
  · simp only [Finset.sum_const_zero]

/-- A local preparation uniform in the boundary prepares the literal closed pair
by a unitary on the same original spins. Source: SCP10, lines 2505–2558.
The tree and the distinct internal bonds specify this auxiliary finite region. -/
theorem exists_unitary_regularClosedChargePairPreparation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R})
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (e₀ e₁ : RI (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (χ : G → ℂ) (hχ : χ ∈ regularChargeLabels (G := G)) (p : G) :
    ∃ W : Matrix ({v : V // v ∈ R} → Fin d) ({v : V // v ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup _ ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup _ ℂ ∧
      regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor a) =
        regularCorrelatedChargeState a (fun _ => 1) e₀.1 e₁.1 χ p 1 := by
  classical
  obtain ⟨W, hW, hcols⟩ := exists_unitary_regularPhysicalChargePairCreation
    a ha R T hT htree o e₀ e₁ hne χ hχ p
  refine ⟨W, hW, regionLocalTerm_mem_unitaryGroup R W hW, ?_⟩
  have hu : regularTwistedSite a (fun _ => (1 : G)) = a := by
    funext v η s
    change a v (regularTwistedLabels (fun _ => 1) v η) s = a v η s
    congr 1
    funext f
    simp only [regularTwistedLabels, one_mul, ite_self]
  rw [regularCorrelatedChargeState]
  symm
  rw [← Finset.sum_congr rfl (fun q _ => (one_smul ℂ _))]
  symm
  apply regionLocalTerm_mulVec_stateCoeff_sum_of_openColumns R a
    (fun q => regularEdgeCharacterSite
      (regularEdgeCharacterSite (regularTwistedSite a (fun _ => 1)) e₀.1
        (fun t => χ (p * q⁻¹ * 1 * t)) 1)
      e₁.1 (fun t => if t = q then 1 else 0) 1) (fun _ => 1) W
  · intro μ
    let θ : RB (Γ := Γ) R → G := fun f => (Fintype.equivFin G).symm (μ f)
    have hμ : (fun f => Fintype.equivFin G (θ f)) = μ := by
      funext f
      exact (Fintype.equivFin G).apply_symm_apply (μ f)
    simp only [one_smul]
    have hc (q : G) : (fun t => χ (p * q⁻¹ * 1 * t)) =
        (fun t => χ (p * q⁻¹ * t)) := by
      funext t
      rw [mul_one]
    have hopen (q : G) :
        openRegionWeight (groupBondTensor
          (regularEdgeCharacterSite
            (regularEdgeCharacterSite (regularTwistedSite a (fun _ => 1)) e₀.1
              (fun t => χ (p * q⁻¹ * 1 * t)) 1)
            e₁.1 (fun t => if t = q then 1 else 0) 1)) R μ =
        openRegionWeight (groupBondTensor
          (regularEdgeCharacterSite
            (regularEdgeCharacterSite (regularTwistedSite a (fun _ => 1)) e₀.1
              (fun t => χ (p * q⁻¹ * t)) 1)
            e₁.1 (fun t => if t = q then 1 else 0) 1)) R μ :=
      congrArg (fun c : G → ℂ => openRegionWeight (groupBondTensor
        (regularEdgeCharacterSite
          (regularEdgeCharacterSite (regularTwistedSite a (fun _ => 1)) e₀.1 c 1)
          e₁.1 (fun t => if t = q then 1 else 0) 1)) R μ) (hc q)
    simp_rw [hopen]
    rw [← hμ, sum_openRegionWeight_regularCorrelatedChargePair, hu]
    rw [← regularChargePairOpenRegionMatrix_one_eq_openRegionWeight a
      (fun v => (ha v).toIsGInjective) R e₀ e₁ θ]
    exact hcols θ
  · intro q v hv
    funext η s
    have h₀ : v ≠ e₀.1.1.1 := fun h => hv (h.symm ▸ e₀.2.1)
    have h₁ : v ≠ e₁.1.1.1 := fun h => hv (h.symm ▸ e₁.2.1)
    simp only [hu, regularEdgeCharacterSite, h₀, h₁, ↓reduceDIte]

/-- Actual closed charge-pair preparation preserves the vacuum norm and is
nonzero. Both facts follow from the derived original-spin unitary, rather than
from a supplied normalization formula. Source: SCP10, lines 2505–2558. -/
theorem regularClosedChargePairPreparation_normSq_ne_zero
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R})
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (e₀ e₁ : RI (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (χ : G → ℂ) (hχ : χ ∈ regularChargeLabels (G := G)) (p : G) :
    let ψ := regularCorrelatedChargeState a (fun _ => 1) e₀.1 e₁.1 χ p 1
    (star ψ ⬝ᵥ ψ = star (stateCoeff (groupBondTensor a)) ⬝ᵥ
      stateCoeff (groupBondTensor a)) ∧ ψ ≠ 0 := by
  classical
  obtain ⟨W, _, hW, hact⟩ := exists_unitary_regularClosedChargePairPreparation
    a ha R T hT htree o e₀ e₁ hne χ hχ p
  have hgram : (regionLocalTerm R W)ᴴ * regionLocalTerm R W = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hW
  constructor
  · rw [← hact, Matrix.star_dotProduct_mulVec, Matrix.mulVec_mulVec,
      hgram, Matrix.one_mulVec]
  · intro hz
    have hback := congrArg (fun ψ => (regionLocalTerm R W)ᴴ *ᵥ ψ) hact
    rw [Matrix.mulVec_mulVec, hgram, Matrix.one_mulVec, hz, Matrix.mulVec_zero] at hback
    have hu : regularTwistedSite a (fun _ => (1 : G)) = a := by
      funext v η s
      change a v (regularTwistedLabels (fun _ => 1) v η) s = a v η s
      congr 1
      funext f
      simp only [regularTwistedLabels, one_mul, ite_self]
    apply stateCoeff_regularTwistedSite_ne_zero_of_isGInjective a
      (fun v => (ha v).toIsGInjective) (fun _ => 1)
    simpa only [hu] using hback

end TNLean.PEPS
