/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentDependentCut
import TNLean.PEPS.DependentCutCoefficientSupport
import TNLean.PEPS.ParentHamiltonian.ThreeBlockPhysicalExtension

/-!
# Coherent bond coefficients of actual graph parent ground vectors

A common family of local G-injective inverses reconstructs every vector in the
existing physical parent space. When the regions cover the edges, its canonical
coordinates have a coherent representation-matrix expansion. Each nonzero
coefficient is a vertex coboundary on every region separately. These statements
are consequences of actual parent membership, with no coefficient support or
cut-space premise on the physical vector.

Every bond may carry an independent semi-regular representation and every site
may have an independent G-injective tensor. The finite-simple-graph parent
framework retains its common physical alphabet.
Source: SCP10, arXiv:1001.3807, Theorems 5.4 and 5.5.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS
open DependentBondNetwork

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

omit [Fintype V] [Fintype G] in
/-- Semi-regularity supplies the positive bond dimensions needed by the
coordinate passage from the existing parent framework. -/
theorem bondDim_ne_zero_of_isSemiRegular (A : Tensor Γ d)
    (U : (e : Edge Γ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e))) :
    ∀ e, A.bondDim e ≠ 0 := by
  intro e
  have hn := ThreeBlockDependent.nonempty_of_isSemiRegular (U e) (hU e)
  exact Nat.ne_zero_of_lt (Fin.pos_iff_nonempty.mpr hn)

/-- Independent local inverses, actual cut membership, and recovery are all
obtained from the existing physical parent ground-space condition. -/
theorem exists_regionParent_commonInverse (A : Tensor Γ d)
    (U : (e : Edge Γ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v))
    {ι : Type*} (i₀ : ι) (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    ∃ F : (v : V) → Matrix (LocalConfig graphEdgeTail graphEdgeHead (graphBondAlphabet A) v)
      (Fin d) ℂ,
      ∀ ψ ∈ regionParentGroundSpace A R,
        (∀ i, dependentPhysicalProductFamilyMap F ψ ∈
          cutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
            (DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
            (regionExteriorCut (R i))) ∧
        dependentPhysicalProductFamilyMap
          (fun v ↦ LinearMap.toMatrix' (localSiteMap graphEdgeTail graphEdgeHead
            (graphBondAlphabet A) (graphDependentTensor A) v))
          (dependentPhysicalProductFamilyMap F ψ) = ψ := by
  obtain ⟨F, _, hF⟩ := exists_liftedCutSpace_common_localInverse
    graphEdgeTail graphEdgeHead (graphBondAlphabet A) i₀
    (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
    (graphDependentTensor A) hA R (fun i ↦ regionExteriorCut (R i))
    (fun i p ↦ mem_regionExteriorCut_of_outside (R i) p) (fun v ↦ Or.inl (hcover v))
  refine ⟨F, fun ψ hψ ↦ ?_⟩
  obtain ⟨hcuts, hrec⟩ := hF ψ
    (regionParentGroundSpace_le_iInf_liftedCutSpace A
      (bondDim_ne_zero_of_isSemiRegular A U hU) R hψ)
  exact ⟨fun i ↦ (Submodule.mem_iInf _).mp hcuts i, hrec⟩

/-- Every actual parent vector has reconstructing canonical coordinates,
a coherent trace-dual expansion, and regional pure-gauge support. -/
theorem exists_regionParent_bondCoefficients (A : Tensor Γ d)
    (U : (e : Edge Γ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v))
    {ι : Type*} (i₀ : ι) (R : ι → Finset V)
    (hvertex : ∀ v, ∃ i, v ∈ R i)
    (hedge : ∀ e : Edge Γ, ∃ i, e.1.1 ∈ R i ∧ e.1.2 ∈ R i)
    {ψ : (V → Fin d) → ℂ} (hψ : ψ ∈ regionParentGroundSpace A R) :
    ∃ ξ : ((v : V) → LocalConfig graphEdgeTail graphEdgeHead (graphBondAlphabet A) v) → ℂ,
      (∀ i, ξ ∈ cutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
          (regionExteriorCut (R i))) ∧
      dependentPhysicalProductFamilyMap
        (fun v ↦ LinearMap.toMatrix' (localSiteMap graphEdgeTail graphEdgeHead
          (graphBondAlphabet A) (graphDependentTensor A) v)) ξ = ψ ∧
      ξ = ∑ p : Edge Γ → G,
        bondCoefficientExtraction graphEdgeTail graphEdgeHead (graphBondAlphabet A) U p ξ •
          representationBondProduct graphEdgeTail graphEdgeHead (graphBondAlphabet A) U p ∧
      (∀ p : Edge Γ → G,
        bondCoefficientExtraction graphEdgeTail graphEdgeHead (graphBondAlphabet A) U p ξ ≠ 0 →
        ∀ i, ∃ q : V → G, ∀ e : Edge Γ, e.1.1 ∈ R i → e.1.2 ∈ R i →
          p e = q e.1.2 * (q e.1.1)⁻¹) := by
  obtain ⟨F, hF⟩ := exists_regionParent_commonInverse A U hU hA i₀ R hvertex
  obtain ⟨hcuts, hrec⟩ := hF ψ hψ
  let ξ := dependentPhysicalProductFamilyMap F ψ
  refine ⟨ξ, hcuts, hrec, ?_, ?_⟩
  · apply eq_sum_extracted_bondProducts_of_mem_cutSpaces
      graphEdgeTail graphEdgeHead (graphBondAlphabet A) U hU
      (fun i ↦ regionExteriorCut (R i)) _ hcuts
    intro e
    obtain ⟨i, hi⟩ := hedge e
    exact ⟨i, by simp [regionExteriorCut, hi.1, hi.2]⟩
  · intro p hp i
    obtain ⟨q, hq⟩ := exists_vertexLabels_of_bondCoefficientExtraction_ne_zero
      graphEdgeTail graphEdgeHead (graphBondAlphabet A) U hU
      (regionExteriorCut (R i)) p (hcuts i) hp
    refine ⟨q, fun e ht hh ↦ hq e ?_⟩
    simp [regionExteriorCut, ht, hh]

end TNLean.PEPS
