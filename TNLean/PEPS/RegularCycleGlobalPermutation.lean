/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoCycleConjugation
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove

/-!
# Global contraction identities for accessible cycle permutations

A fixed physical unitary implementing a conjugation-equivariant cycle permutation
extends by the complementary identity. Arbitrary common exterior and crossing
bond operators remain present: an identity vertex gauge gives the same boundary
transport on both sides, and the actual cut sum gives the global state identity.

Source: SCP10, arXiv:1001.3807, accessible-coordinate construction,
lines 1765–1920, and `eq:anyons:fluxon-braiding-lazy`, lines 2360–2395.

**Scope restriction (accessible cycle permutations):** These are actual local
and global contraction identities on a chosen finite tree-coordinate block.
The controlled conjugation specialization does not yet identify a prescribed
native string crossing or an anyon braid. It asserts no energy or ground-space
conclusion; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]

/-- One identity-extended unitary implements the cycle permutation in actual
global states for every cycle assignment and arbitrary common exterior and
crossing operators. Source: SCP10, lines 1765–1920 and 2360–2395. -/
theorem exists_unitary_regularCycleGlobalPermutation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      (∀ (ω : RC (Γ := Γ) R T → G)
        (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T ω))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T (φ ω)))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularTreeCycleAssignment R T ω) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularTreeCycleAssignment R T (φ ω)) u))) := by
  classical
  obtain ⟨W, hW, hperm⟩ :=
    exists_unitary_regularCyclePhysicalPermutation R T a ha hT htree o φ hφ
  have hinv : ∀ g v η s, a v (fun e => g * η e) s = a v η s := by
    intro g v η s
    exact (ha v).toIsGInjective.regularSiteMap_translation g η s
  refine ⟨W, hW, regionLocalTerm_mem_unitaryGroup R W hW, hperm, ?_⟩
  intro ω u
  apply regionLocalTerm_mulVec_stateCoeff_of_openColumns
  · intro μ
    let θ := fun f => (Fintype.equivFin G).symm (μ f)
    have h := hperm ω (regularRegionBoundaryTransport R (fun _ => 1) u θ)
    rw [← openRegionWeight_regularTreeCycleBondExtension R T a hinv ω u θ,
      ← openRegionWeight_regularTreeCycleBondExtension R T a hinv (φ ω) u θ] at h
    simpa only [θ, Equiv.apply_symm_apply] using h
  · exact regularTwistedSite_regularRegionBondExtension_eq_outside R a _ _ u

/-- One fixed global physical unitary conjugates the selected cycle by the
retained controlling cycle, for all inserted labels and common exterior data.
Source: SCP10, `eq:anyons:fluxon-braiding-lazy`, lines 2360–2388. -/
theorem exists_unitary_regularTwoCycleGlobalConjugation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      ∀ (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularTreeCycleAssignment R T ω) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularTreeCycleAssignment R T
            (regularTwoCycleConjugation e₀ e₁ hne ω)) u))) := by
  obtain ⟨W, hW, hglobal, _, hact⟩ := exists_unitary_regularCycleGlobalPermutation
    R T a ha hT htree o (regularTwoCycleConjugation e₀ e₁ hne)
    (regularTwoCycleConjugation_conjugation e₀ e₁ hne)
  exact ⟨W, hW, hglobal, hact⟩

end TNLean.PEPS
