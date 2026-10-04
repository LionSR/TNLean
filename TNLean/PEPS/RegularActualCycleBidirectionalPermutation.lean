/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularActualCyclePhysicalPermutation

/-!
# Actual cycle operations and their physical inverses

The same original-spin unitary acts on the cycle coordinates derived from
every actual input. Its adjoint implements the inverse cycle permutation,
with the original tree background and all exterior operators retained.
Source: SCP10, arXiv:1001.3807, lines 1765–1920 and Theorem 6.16,
lines 2271–2305. This is an auxiliary chosen-tree statement, not the
complete prescribed braid or a parent-Hamiltonian assertion.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G]
variable (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
variable (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})

/-- Reconstruct the forward or inverse permutation from the actual input's
own normalized coordinates. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def regularActualCycleDirectionalPermutation
    (φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G))
    (reverse : Bool) (u : Edge Γ → G) : Edge Γ → G :=
  regularActualCyclePermutation R T hT htree o (if reverse then φ.symm else φ) u

/-- One physical unitary and its adjoint implement both directions on every
actual input, before all input and boundary data. Source: SCP10,
Theorem 6.16, lines 2271–2305. -/
theorem exists_unitary_regularActualCycleBidirectionalPermutation {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹) :
    ∃ W : Matrix ({v : V // v ∈ R} → Fin d) ({v : V // v ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({v : V // v ∈ R} → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      (∀ (reverse : Bool) (u : Edge Γ → G)
          (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        (if reverse then W.conjTranspose else W) *ᵥ
          openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
            (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularActualCycleDirectionalPermutation R T hT htree o φ reverse u))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (reverse : Bool) (u : Edge Γ → G),
        (if reverse then (regionLocalTerm R W).conjTranspose else regionLocalTerm R W) *ᵥ
          stateCoeff (groupBondTensor (regularTwistedSite a u)) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (regularActualCycleDirectionalPermutation R T hT htree o φ reverse u))) := by
  obtain ⟨W, hW, hglobal, hlocal, hact⟩ :=
    exists_unitary_regularGaugedCyclePhysicalPermutation R T a ha hT htree o φ hφ
  have hWgram : W.conjTranspose * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  have hUgram : (regionLocalTerm R W).conjTranspose * regionLocalTerm R W = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hglobal
  refine ⟨W, hW, hglobal, ?_, ?_⟩
  · intro reverse u θ
    cases reverse
    · have H := hlocal (regularRegionTreeGauge R T hT htree o u).1
        (regularRegionTreeCycleResidual R T hT htree o u) u θ
      rw [regularRegionBondExtension_treeGauge R T hT htree o u] at H
      exact H
    · have H := hlocal (regularRegionTreeGauge R T hT htree o u).1
        (φ.symm (regularRegionTreeCycleResidual R T hT htree o u)) u θ
      rw [Equiv.apply_symm_apply, regularRegionBondExtension_treeGauge R T hT htree o u] at H
      change W.conjTranspose *ᵥ _ = _
      rw [← H, Matrix.mulVec_mulVec, hWgram, Matrix.one_mulVec]
      rfl
  · intro reverse u
    cases reverse
    · have H := hact (regularRegionTreeGauge R T hT htree o u).1
        (regularRegionTreeCycleResidual R T hT htree o u) u
      rw [regularRegionBondExtension_treeGauge R T hT htree o u] at H
      exact H
    · have H := hact (regularRegionTreeGauge R T hT htree o u).1
        (φ.symm (regularRegionTreeCycleResidual R T hT htree o u)) u
      rw [Equiv.apply_symm_apply, regularRegionBondExtension_treeGauge R T hT htree o u] at H
      change (regionLocalTerm R W).conjTranspose *ᵥ _ = _
      rw [← H, Matrix.mulVec_mulVec, hUgram, Matrix.one_mulVec]
      rfl

end TNLean.PEPS
