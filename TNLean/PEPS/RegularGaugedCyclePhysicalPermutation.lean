/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCyclePermutation
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove

/-!
# Physical cycle operations with a common tree background

A single original-spin unitary implements a conjugation-equivariant cycle
permutation even when the internal tree operators are nontrivial. Both sides
are reconstructed from the same vertex gauge. All exterior and crossing
operators are retained literally, and the same boundary transport therefore
normalizes their actual open-region coefficients.

Source: SCP10, arXiv:1001.3807, accessible virtual systems, lines 1765–1920,
and the physical movement and virtual braiding arguments, lines 2270–2301
and 2361–2415. This auxiliary chosen-tree statement does not identify a
prescribed four-endpoint string braid or compare different crossing
presentations. No coefficient, Gram or parent-Hamiltonian hypothesis is used.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]

/-- Reconstruct the internal operators from one vertex gauge and cycle labels.
Source: SCP10, reversible accessible coordinates, lines 1765–1920. -/
def regularGaugedTreeCycleAssignment (k : RV R → G) (ω : RC (Γ := Γ) R T → G) :
    Edge Γ → G := fun e =>
  if h : e.1.1 ∈ R ∧ e.1.2 ∈ R then
    k ⟨e.1.2, h.2⟩ * regularTreeCycleAssignment R T ω e * (k ⟨e.1.1, h.1⟩)⁻¹
  else 1

/-- A shared gauge normalizes every internal operator while retaining the
literal common crossing assignment in the boundary transport.
Source: SCP10, actual regular contraction, lines 1765–1920. -/
theorem openRegionWeight_regularGaugedTreeCycleBondExtension {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (hinv : ∀ x v η s, a v (fun e => x * η e) s = a v η s)
    (k : RV R → G) (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    openRegionWeight (groupBondTensor (regularTwistedSite a
      (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k ω) u))) R
      (fun f => Fintype.equivFin G (θ f)) =
    openRegionWeight (groupBondTensor (regularTwistedSite a
      (regularTreeCycleAssignment R T ω))) R
      (fun f => Fintype.equivFin G (regularRegionBoundaryTransport R k u θ f)) := by
  have hops : regularRegionGaugeEdgeOperators R k
      (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k ω) u) =
      regularTreeCycleAssignment R T ω := by
    funext e
    by_cases h : e.1.1 ∈ R ∧ e.1.2 ∈ R
    · simp only [regularRegionGaugeEdgeOperators,
        regularRegionGaugeResidual, regularRegionBondExtension, ite_eq_left h,
        regularGaugedTreeCycleAssignment, dite_eq_left h]
      group
    · simp only [regularRegionGaugeEdgeOperators, dite_eq_right h]
      by_cases ht : e.1.1 ∈ R
      · have hh : e.1.2 ∉ R := fun hh => h ⟨ht, hh⟩
        simp only [regularTreeCycleAssignment, dite_eq_left ht, dite_eq_right hh]
      · simp only [regularTreeCycleAssignment, dite_eq_right ht]
  have hb : regularRegionBoundaryTransport R k
      (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k ω) u) =
      regularRegionBoundaryTransport R k u := by
    apply Equiv.ext
    intro η
    funext e
    have hn : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
      rcases e.2 with h | h
      · exact fun he => h.2 he.2
      · exact fun he => h.1 he.1
    simp only [regularRegionBoundaryTransport, Equiv.piCongrRight_apply, Pi.map_apply,
      Equiv.mulLeft, regularRegionBondExtension, ite_eq_right hn]
  funext σ
  rw [openRegionWeight_regularRegionGauge a hinv R k, hops, hb]

/-- One original-spin unitary acts before every shared gauge, cycle assignment,
boundary configuration and common exterior or crossing operator. Source: SCP10,
accessible physical operations, lines 1765–1920 and 2270–2301. -/
theorem exists_unitary_regularGaugedCyclePhysicalPermutation {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      (∀ (k : RV R → G) (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G)
        (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k ω) u))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k (φ ω)) u))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (k : RV R → G) (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k ω) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k (φ ω)) u))) := by
  classical
  obtain ⟨W, hW, hperm⟩ :=
    exists_unitary_regularCyclePhysicalPermutation R T a ha hT htree o φ hφ
  have hinv : ∀ x v η s, a v (fun e => x * η e) s = a v η s :=
    fun x v η s => (ha v).toIsGInjective.regularSiteMap_translation x η s
  have hcols (k : RV R → G) (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G)
      (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
      W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
        (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k ω) u))) R
        (fun f => Fintype.equivFin G (θ f)) =
      openRegionWeight (groupBondTensor (regularTwistedSite a
        (regularRegionBondExtension R (regularGaugedTreeCycleAssignment R T k (φ ω)) u))) R
        (fun f => Fintype.equivFin G (θ f)) := by
    rw [openRegionWeight_regularGaugedTreeCycleBondExtension R T a hinv,
      openRegionWeight_regularGaugedTreeCycleBondExtension R T a hinv]
    exact hperm ω (regularRegionBoundaryTransport R k u θ)
  refine ⟨W, hW, regionLocalTerm_mem_unitaryGroup R W hW, hcols, ?_⟩
  intro k ω u
  apply regionLocalTerm_mulVec_stateCoeff_of_openColumns
  · intro μ
    let θ := fun f => (Fintype.equivFin G).symm (μ f)
    simpa only [θ, Equiv.apply_symm_apply] using hcols k ω u θ
  · exact regularTwistedSite_regularRegionBondExtension_eq_outside R a _ _ u

end TNLean.PEPS
