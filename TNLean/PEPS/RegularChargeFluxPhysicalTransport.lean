/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeFluxCoordinateTransport
import TNLean.PEPS.RegularWeightedOpenContraction
/-!
# Original-spin transport of a literal character-weighted bond insertion

One unitary on the original physical region implements the controlled
reference-cycle operation. It is selected before the character, the charge
parameter, all actual bond operators and every open boundary configuration. Its action
is proved on the actual incident-label contraction with a diagonal bond
weight, rather than inferred from a span of group-valued insertions.

Source: SCP10, arXiv:1001.3807, charge–flux braiding, lines 2569–2581,
using accessible coordinates, lines 1765–1920.
**Scope restriction (chosen finite block):** A spanning tree and selected
internal charge and non-tree flux bonds are supplied. This local operation is
an auxiliary physical realization of the parameter change, not the complete
geometric charge–flux braid; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}
/-- One original-spin unitary changes the literal diagonal charge parameter by
right multiplication with the inverse transported residual, uniformly in every
actual bond assignment and weighted column.
Source: SCP10, lines 2569–2581; chosen finite-block specialization. -/
theorem exists_unitary_regularChargeFluxPhysicalTransport {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RI (Γ := Γ) R) (b : RC (Γ := Γ) R T) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ (u : Edge Γ → G) (χ : G → ℂ) (p : G)
        (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G),
        W *ᵥ regularWeightedOpenRegionWeight a R u
          (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩)) θ =
        regularWeightedOpenRegionWeight a R u
          (fun η => χ (regularChargeFluxParameter R T hT htree o e b u p *
            η ⟨e.1, Or.inl e.2.1⟩)) θ := by
  classical
  let Q := Matrix.permMatrixHom (R := ℂ)
    (regularChargeFluxPhysicalPermutation (G := G) R T hT htree o e b)
  have hQ : Q ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
    (regularChargeFluxPhysicalPermutation (G := G) R T hT htree o e b)⁻¹
      |>.permMatrix_mem_unitaryGroup
  obtain ⟨W,hW,hWA⟩ := exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute
    a ha R Q hQ
    (regularChargeFluxPhysicalPermutation_commute_localProjector R T hT htree o e b).eq
  refine ⟨W,hW,?_⟩
  intro u χ p θ
  have hcan := regularProjectorWeightedTwistedRegionMatrix_chargeFlux_mulVec
    R T hT htree o e b u χ p θ
  rw [← regionPhysicalMap_regularProjectorWeightedTwistedRegionMatrix a
      (fun v => (ha v).toIsGInjective),
    ← regionPhysicalMap_regularProjectorWeightedTwistedRegionMatrix a
      (fun v => (ha v).toIsGInjective)]
  change W *ᵥ (_ *ᵥ _) = _ *ᵥ _
  rw [Matrix.mulVec_mulVec, hWA, ← Matrix.mulVec_mulVec, hcan]
end TNLean.PEPS
