/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphDependentCutCoordinates
import TNLean.PEPS.DependentLiftedCutIntersection

/-!
# Existing regional parent constraints give genuine dependent cut witnesses

For an actual finite-graph PEPS parent, every regional kernel constraint gives
one arbitrary joint boundary on the exposed virtual incidences and the omitted
physical coordinates. When the regions cover the vertices, the independent
local reconstruction theorem turns these witnesses into full-network cut
witnesses for the original tensors.

The parent and its open-region kernel are the existing graph definitions.
No supplied cut membership, spanning statement, or reconstruction assumption
is used. Bond dimensions and site tensors are unrestricted, apart from
nonzero bond dimensions. The existing parent framework uses one physical
alphabet and a simple graph; those scope restrictions remain explicit here.

Source: SCP10, arXiv:1001.3807, the regional parent conditions in Theorem 5.4.
This is the coordinate passage preceding rectangle growth, not the subsequent
microscopic-parent to four-seam intersection theorem.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS
open DependentBondNetwork

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The omitted physical coordinates in the cut convention are exactly the
complementary coordinates in the existing graph parent convention. -/
def outsidePhysicalToComplement (R : Finset V)
    (τ : OutsidePhysicalConfig R (fun _ : V ↦ Fin d)) :
    RegionPhysicalConfig (d := d) (Finset.univ \ R) :=
  fun v ↦ τ ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

/-- Closing every extra exposed endpoint realizes an ordinary regional
boundary, with arbitrary correlations with the omitted physical coordinates. -/
def graphRegionalCutBoundary (A : Tensor Γ d) (R : Finset V)
    (x : RegionPhysicalConfig (d := d) (Finset.univ \ R) → RegionBoundaryConfig A R → ℂ)
    (p : CutConfig (regionExteriorCut R) (graphBondAlphabet A) ×
      OutsidePhysicalConfig R (fun _ : V ↦ Fin d)) : ℂ :=
  x (outsidePhysicalToComplement R p.2) (regionCutBoundaryLabel A R p.1) *
    cutIdentityWeight (graphBondAlphabet A) (regionExteriorCut R) p.1

/-- The explicit boundary contracts to the actual open-region map, times
only the previously established exterior multiplicity. -/
theorem liftedCutMap_graphRegionalCutBoundary (A : Tensor Γ d) (R : Finset V)
    (x : RegionPhysicalConfig (d := d) (Finset.univ \ R) → RegionBoundaryConfig A R → ℂ)
    (σ : V → Fin d) :
    liftedCutMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A)
      R (regionExteriorCut R) (graphRegionalCutBoundary A R x) σ =
      (regionExteriorMultiplicity A R : ℂ) *
        openRegionMap A R (x (fun v ↦ σ v.1)) (fun v ↦ σ v.1) := by
  classical
  change (∑ β : EndpointConfig (graphBondAlphabet A),
    (x (outsidePhysicalToComplement R (outsidePhysicalRestriction R σ))
        (regionCutBoundaryLabel A R (cutRestriction _ _ β)) *
      cutIdentityWeight (graphBondAlphabet A) (regionExteriorCut R) (cutRestriction _ _ β) *
      cutInteriorWeight (graphBondAlphabet A) (regionExteriorCut R) β) *
        ∏ v ∈ R, graphDependentTensor A v (endpointSiteEquiv _ _ _ β v) (σ v)) = _
  rw [sum_cutIdentityWeight_mul (graphBondAlphabet A) (regionExteriorCut R)
    (fun θ ↦ x (outsidePhysicalToComplement R (outsidePhysicalRestriction R σ))
      (regionCutBoundaryLabel A R θ))
    (fun β ↦ ∏ v ∈ R, graphDependentTensor A v (endpointSiteEquiv _ _ _ β v) (σ v))]
  simp only [regionCutBoundaryLabel_diagonal, graphDependentTensor_diagonal]
  have hprod (η : VirtualConfig A) :
      (∏ v ∈ R, A.component v (fun e ↦ η e.1) (σ v)) =
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun e ↦ η e.1) (σ w.1) :=
    Finset.prod_subtype R (fun _ ↦ Iff.rfl) _
  simp_rw [hprod]
  exact sum_regionBoundaryLabel_mul_eq_openRegionMap A R _ _

/-- Actual regional slices supply a literal joint boundary witness. The
positive bond hypothesis only cancels the explicit exterior multiplicity. -/
theorem mem_liftedCutSpace_of_region_slices (A : Tensor Γ d) (R : Finset V)
    (hA : ∀ e, A.bondDim e ≠ 0) {ψ : (V → Fin d) → ℂ}
    (hψ : ∀ τ : RegionPhysicalConfig (d := d) (Finset.univ \ R),
      regionSliceMap R τ ψ ∈ regionGroundSpace A R) :
    ψ ∈ liftedCutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (graphDependentTensor A) R (regionExteriorCut R) := by
  classical
  choose x hx using hψ
  have hscaled : (regionExteriorMultiplicity A R : ℂ) • ψ ∈
      liftedCutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (graphDependentTensor A) R (regionExteriorCut R) := by
    refine ⟨graphRegionalCutBoundary A R x, ?_⟩
    funext σ
    rw [liftedCutMap_graphRegionalCutBoundary]
    have heq : assembleRegionσ R (fun v ↦ σ v.1) (fun v ↦ σ v.1) = σ := by
      funext v
      simp [assembleRegionσ]
    have hxσ := congrFun (hx (fun v ↦ σ v.1)) (fun v ↦ σ v.1)
    change openRegionMap A R (x (fun v ↦ σ v.1)) (fun v ↦ σ v.1) =
      ψ (assembleRegionσ R (fun v ↦ σ v.1) (fun v ↦ σ v.1)) at hxσ
    rw [hxσ, heq]
    rfl
  have hn : (regionExteriorMultiplicity A R : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (regionExteriorMultiplicity_ne_zero A R hA)
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
    Submodule.smul_mem _ (regionExteriorMultiplicity A R : ℂ)⁻¹ hscaled

/-- The existing physical parent space gives all its actual lifted regional
ranges, on the original all-site physical space. -/
theorem regionParentGroundSpace_le_iInf_liftedCutSpace (A : Tensor Γ d)
    (hA : ∀ e, A.bondDim e ≠ 0) {ι : Type*} (R : ι → Finset V) :
    regionParentGroundSpace A R ≤
      ⨅ i, liftedCutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (graphDependentTensor A) (R i) (regionExteriorCut (R i)) := by
  intro ψ hψ
  apply (Submodule.mem_iInf _).mpr
  intro i
  apply mem_liftedCutSpace_of_region_slices A (R i) hA
  intro τ
  exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hψ i) τ

/-- Vertex-covering actual parent constraints give genuine full cut ranges
for the original tensors, without injectivity or an assumed reconstruction. -/
theorem regionParentGroundSpace_le_iInf_cutSpace (A : Tensor Γ d)
    (hA : ∀ e, A.bondDim e ≠ 0) {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ R i) :
    regionParentGroundSpace A R ≤
      ⨅ i, cutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (graphDependentTensor A) (regionExteriorCut (R i)) := by
  rw [← iInf_liftedCutSpace_eq_iInf_cutSpace graphEdgeTail graphEdgeHead
    (graphBondAlphabet A) (graphDependentTensor A) R (fun i ↦ regionExteriorCut (R i))
    (fun i p ↦ mem_regionExteriorCut_of_outside (R i) p) (fun v ↦ Or.inl (hcover v))]
  exact regionParentGroundSpace_le_iInf_liftedCutSpace A hA R

/-- Every vector killed by the actual positive parent Hamiltonian has one
joint boundary witness for each regional cut, using the original site tensors. -/
theorem exists_cutBoundary_of_mem_regionParentKernel (A : Tensor Γ d)
    (hA : ∀ e, A.bondDim e ≠ 0) {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction A (R i) (H i))
    {ψ : (V → Fin d) → ℂ}
    (hψ : ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian R H)).ker) (i : ι) :
    ∃ M : CutConfig (regionExteriorCut (R i)) (graphBondAlphabet A) → ℂ,
      ∀ σ, cutCoeff graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (graphDependentTensor A) (regionExteriorCut (R i)) M σ = ψ σ := by
  rw [ker_regionParentHamiltonian A R H hH] at hψ
  exact (mem_cutSpace_iff _ _ _ _ _ _).mp ((Submodule.mem_iInf _).mp
    (regionParentGroundSpace_le_iInf_cutSpace A hA R hcover hψ) i)

end TNLean.PEPS
