/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGaugedCyclePhysicalPermutation
import TNLean.PEPS.RegularInternalGaugeTransport

/-!
# Physical cycle operations on an arbitrary actual bond assignment

The actual operators on a region determine their root-normalized tree gauge
and cycle residuals. Reconstructing those derived coordinates recovers every
original internal coefficient. A fixed physical cycle operation therefore acts
on arbitrary actual inputs, without a supplied common-background representation.
The transformed assignment retains every exterior and crossing operator.

Source: SCP10, arXiv:1001.3807, accessible coordinates, lines 1765–1920, and
Theorem 6.16, lines 2271–2305.

**Scope restriction (regular action and chosen finite region):** The physical
statement retains a chosen tree and a conjugation-equivariant cycle permutation.
Interpreting it as native occupied-to-vacant plaquette movement requires the
corresponding actual holonomy calculation; it does not establish the complete
four-endpoint braid. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [LinearOrder V]
variable {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]
variable (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
variable (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})

/-- The normalized gauge and residuals derived from an actual assignment recover
its internal ordered coefficients. Source: SCP10, lines 1765–1920. -/
theorem regularGaugedTreeCycleAssignment_treeGauge_of_internal (u : Edge Γ → G)
    (e : Edge Γ) (he : e.1.1 ∈ R ∧ e.1.2 ∈ R) :
    regularGaugedTreeCycleAssignment R T (regularRegionTreeGauge R T hT htree o u).1
      (regularRegionTreeCycleResidual R T hT htree o u) e = u e := by
  classical
  simp only [regularGaugedTreeCycleAssignment, dite_eq_left he,
    regularTreeCycleAssignment, dite_eq_left he.1, dite_eq_left he.2]
  by_cases hn : ¬ T.Adj ⟨e.1.1, he.1⟩ ⟨e.1.2, he.2⟩
  · simp only [dite_eq_left hn, regularRegionTreeCycleResidual,
      regularRegionGaugeResidual]
    group
  · simp only [dite_eq_right hn, mul_one]
    exact regularRegionTreeGauge_gradient R T hT htree o u ⟨e, he⟩ (not_not.mp hn)

/-- Retaining the literal exterior recovers the whole original bond assignment.
Source: SCP10, the reversible coordinate construction, lines 1765–1920. -/
theorem regularRegionBondExtension_treeGauge (u : Edge Γ → G) :
    regularRegionBondExtension R
      (regularGaugedTreeCycleAssignment R T (regularRegionTreeGauge R T hT htree o u).1
        (regularRegionTreeCycleResidual R T hT htree o u)) u = u :=
  regularRegionBondExtension_eq_of_internal R _ u
    (regularGaugedTreeCycleAssignment_treeGauge_of_internal R T hT htree o u)

/-- Change the derived cycle residuals and reconstruct with the original tree
background, preserving every exterior operator. Source: SCP10, lines 1765–1920
and Theorem 6.16, lines 2271–2305. -/
def regularActualCyclePermutation (φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G))
    (u : Edge Γ → G) : Edge Γ → G :=
  regularRegionBondExtension R
    (regularGaugedTreeCycleAssignment R T (regularRegionTreeGauge R T hT htree o u).1
      (φ (regularRegionTreeCycleResidual R T hT htree o u))) u

variable [Fintype V] [DecidableRel Γ.Adj]

/-- A fixed original-spin unitary acts on every actual bond assignment using
only its derived tree gauge and cycle residuals. Source: SCP10, accessible
operations and Theorem 6.16, lines 1765–1920 and 2271–2305. -/
theorem exists_unitary_regularActualCyclePhysicalPermutation {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹) :
    ∃ W : Matrix ({v : V // v ∈ R} → Fin d) ({v : V // v ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({v : V // v ∈ R} → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      (∀ (u : Edge Γ → G) (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularActualCyclePermutation R T hT htree o φ u))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ u : Edge Γ → G,
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a u)) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (regularActualCyclePermutation R T hT htree o φ u))) := by
  obtain ⟨W, hW, hglobal, hlocal, hact⟩ :=
    exists_unitary_regularGaugedCyclePhysicalPermutation R T a ha hT htree o φ hφ
  refine ⟨W, hW, hglobal, ?_, ?_⟩
  · intro u θ
    have H := hlocal (regularRegionTreeGauge R T hT htree o u).1
      (regularRegionTreeCycleResidual R T hT htree o u) u θ
    rw [regularRegionBondExtension_treeGauge R T hT htree o u] at H
    exact H
  · intro u
    have H := hact (regularRegionTreeGauge R T hT htree o u).1
      (regularRegionTreeCycleResidual R T hT htree o u) u
    rw [regularRegionBondExtension_treeGauge R T hT htree o u] at H
    exact H

end TNLean.PEPS
