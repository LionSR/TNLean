/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCoherentGlobalTransport
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove
import TNLean.PEPS.RegularCyclePhysicalFluxCreation

/-!
# Coherent flux creation in an actual globally contracted state

The local original-spin creation unitary extends by the complementary identity.
All exterior and crossing bond operators may be arbitrary and common to every
summand. An identity vertex gauge derives their common boundary transport, and
finite-sum linearity through the actual cut gives the normalized conjugacy-class
sum of actual global insertions. The unitary depends on the requested
conjugacy class and is chosen before every exterior and crossing assignment.

Source: SCP10, arXiv:1001.3807, Theorem 6.17, lines 2304–2340, and the actual
cut contraction, lines 1935–1957. The centralizer multiplicities are retained;
the normalization is the one derived from the actual local creation vectors.

**Scope restriction (chosen finite cycle block):** A spanning tree and one
internal non-tree bond are supplied in a finite simple graph, and the original
sites are G-isometric for the regular virtual action. This is a global coherent
contraction consequence of the local operation, without an energy or
parent-Hamiltonian membership assertion. Concrete pair geometry and the
unrestricted source scope are recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
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

private theorem global_creation_of_columns
    (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (hinv : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (e : RC (Γ := Γ) R T) (g : G) (γ : ℂ)
    (W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ)
    (hcreate : ∀ θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G,
      W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
        (regularTreeCycleAssignment R T (fun _ => 1)))) R
        (fun f => Fintype.equivFin G (θ f)) =
      γ • ∑ z : G, openRegionWeight (groupBondTensor (regularTwistedSite a
        (regularTreeCycleAssignment R T (fun f => if f = e then z * g * z⁻¹ else 1)))) R
        (fun f => Fintype.equivFin G (θ f))) (u : Edge Γ → G) :
    regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
      (regularRegionBondExtension R (regularTreeCycleAssignment R T (fun _ => 1)) u))) =
    γ • ∑ z : G, stateCoeff (groupBondTensor (regularTwistedSite a
      (regularRegionBondExtension R (regularTreeCycleAssignment R T
        (fun f => if f = e then z * g * z⁻¹ else 1)) u))) := by
  rw [Finset.smul_sum]
  apply regionLocalTerm_mulVec_stateCoeff_sum_of_openColumns R
    (regularTwistedSite a (regularRegionBondExtension R
      (regularTreeCycleAssignment R T (fun _ => 1)) u))
    (fun z : G => regularTwistedSite a (regularRegionBondExtension R
      (regularTreeCycleAssignment R T (fun f => if f = e then z * g * z⁻¹ else 1)) u))
    (fun _ => γ) W
  · intro μ
    let θ := fun f => (Fintype.equivFin G).symm (μ f)
    have hμ : μ = fun f => Fintype.equivFin G (θ f) := by
      funext f
      exact (Fintype.equivFin G).apply_symm_apply (μ f) |>.symm
    rw [hμ]
    simp_rw [openRegionWeight_regularTreeCycleBondExtension R T a hinv]
    simpa only [Finset.smul_sum] using
      hcreate (regularRegionBoundaryTransport R (fun _ => 1) u θ)
  · intro z v hv
    exact regularTwistedSite_regularRegionBondExtension_eq_outside R a _ _ u v hv

/-- One identity-extended original-spin unitary creates the normalized coherent
conjugacy-class insertion for every common exterior and crossing bond assignment.
Its local action and the global finite cut identity are derived. Source: SCP10,
Theorem 6.17, lines 2304–2340, in the stated chosen finite cycle block. -/
theorem exists_unitary_regularCycleGlobalFluxCreation_bondOperators
    (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (g : G) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      ∀ u : Edge Γ → G,
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularTreeCycleAssignment R T (fun _ => 1)) u))) =
        (Real.sqrt ((Fintype.card G : ℝ) *
          Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ •
          ∑ z : G, stateCoeff (groupBondTensor (regularTwistedSite a
            (regularRegionBondExtension R (regularTreeCycleAssignment R T
              (fun f => if f = e then z * g * z⁻¹ else 1)) u))) := by
  obtain ⟨W, hW, hcreate⟩ :=
    exists_unitary_regularCyclePhysicalFluxCreation R T a ha hT htree o e g
  have hinv : ∀ x v η s, a v (fun f => x * η f) s = a v η s := by
    intro x v η s
    exact (ha v).toIsGInjective.regularSiteMap_translation x η s
  exact ⟨W, hW, regionLocalTerm_mem_unitaryGroup R W hW,
    global_creation_of_columns R T a hinv e g _ W hcreate⟩
end TNLean.PEPS
