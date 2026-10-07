/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockPhysicalExtension
import TNLean.PEPS.ParentHamiltonian.ThreeBlockOpenBoundaryContraction
import TNLean.PEPS.ParentHamiltonian.ThreeBlockOpenBoundaryRegional
import TNLean.PEPS.DependentLiftedCutIntersection

/-!
# The three-block G-injective intersection with open exterior legs

The two regional ranges leave the omitted core physical factor arbitrary.
Their intersection is the literal three-tensor contraction against one arbitrary
joint tensor on eight exterior virtual legs. Only the three core physical
factors occur in the conclusion. Each bond and each physical site has its own
finite alphabet, and each matched bond representation may be semi-regular.

Source: SCP10, arXiv:1001.3807, Theorem 5.4, `thm:2d:intersection`,
lines 1373–1420 and `figs3/grow-N`, `figs3/grow-M`, `figs3/grow-intersect`.
-/

universe u
noncomputable section
namespace TNLean.PEPS.ThreeBlockDependent
open DependentBondNetwork

/-- The two physical tensors on the left of the source intersection. -/
def leftVertices : Finset Vertex := {0, 1}

/-- The two physical tensors on the right of the source intersection. -/
def rightVertices : Finset Vertex := {1, 2}

variable {G : Type*} [Group G] [Finite G]
variable (D : Bond → Type u) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Core → Type u} [∀ v, Finite (Phys v)]

/-- The source intersection on exactly three independent physical factors,
with arbitrary correlated exterior virtual data and arbitrary G-injective
core tensors. The right-hand map has exactly eight virtual boundary indices.
Source: SCP10, Theorem 5.4; the two endpoint tensors may also differ. -/
theorem coreLiftedCutSpace_inf_eq_openBoundarySpace
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : Core) → LocalConfig D v.1 → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (incidentRepresentation tail head D U v.1)
      (Matrix.mulVecLin (fun s η ↦ A v η s))) :
    coreLiftedCutSpace D (extendedTensor D A) leftVertices (by decide) leftCut ⊓
        coreLiftedCutSpace D (extendedTensor D A) rightVertices (by decide) rightCut =
      openBoundarySpace D (extendedTensor D A) := by
  classical
  let (v : Core) := Fintype.ofFinite (Phys v)
  have hD := nonempty_bonds_of_isSemiRegular D U hU
  let τ : OutsidePhysicalConfig coreVertices (ExtendedPhys D Phys) := fun v ↦
    (exteriorOutputEquiv D Phys v.1 v.2).symm (fun p ↦ Classical.choice (hD p.1.1))
  let ξ₀ : ExteriorEndpointConfig D := fun p ↦ Classical.choice (hD p.1.1)
  have hleft : ∀ p : Endpoint Bond,
      endpointVertex tail head p ∉ leftVertices → p.1 ∈ leftCut := by decide
  have hright : ∀ p : Endpoint Bond,
      endpointVertex tail head p ∉ rightVertices → p.1 ∈ rightCut := by decide
  have hcore : ∀ p : Endpoint Bond,
      endpointVertex tail head p ∉ coreVertices → p.1 ∈ exteriorBonds := by decide
  have hcover v : v ∈ leftVertices ∨ v ∈ rightVertices ∨
      (localSiteMap tail head D (extendedTensor D A) v).range = ⊤ := by
    by_cases hl : v ∈ leftVertices
    · exact Or.inl hl
    by_cases hr : v ∈ rightVertices
    · exact Or.inr (Or.inl hr)
    have hv : v ∉ coreVertices := by
      have hu : leftVertices ∪ rightVertices = coreVertices := by decide
      simpa only [← hu, Finset.mem_union, not_or] using And.intro hl hr
    exact Or.inr (Or.inr (localSiteMap_extendedTensor_exterior_range D A v hv))
  have hcoverCore v : v ∈ coreVertices ∨
      (localSiteMap tail head D (extendedTensor D A) v).range = ⊤ := by
    by_cases hv : v ∈ coreVertices
    · exact Or.inl hv
    · exact Or.inr (localSiteMap_extendedTensor_exterior_range D A v hv)
  rw [← comap_liftedCutSpace_eq_coreLiftedCutSpace D (extendedTensor D A)
      leftVertices (by decide) leftCut τ,
    ← comap_liftedCutSpace_eq_coreLiftedCutSpace D (extendedTensor D A)
      rightVertices (by decide) rightCut τ,
    ← Submodule.comap_inf,
    liftedCutSpace_inf_eq_cutSpace_inf tail head D (extendedTensor D A)
      leftVertices rightVertices leftCut rightCut hleft hright hcover,
    cutSpace_left_inf_right D U (extendedTensor D A) (isGInjective_extendedTensor D U A hA),
    ← liftedCutSpace_eq_cutSpace_of_cover_or_surjective tail head D (extendedTensor D A)
      coreVertices exteriorBonds hcore hcoverCore,
    comap_liftedCutSpace_eq_coreLiftedCutSpace D (extendedTensor D A)
      coreVertices (Finset.Subset.refl _) exteriorBonds τ,
    coreLiftedCutSpace_eq_openBoundarySpace D (extendedTensor D A) ξ₀]

/-- The intersection of the two actual six-virtual-leg regional ranges is the
actual eight-virtual-leg range, on exactly three physical factors. Boundary
tensors may correlate all their virtual indices with the omitted physical
factor. Source: SCP10, Theorem 5.4, without a common dimension assumption. -/
theorem regionalBoundarySpace_inf_eq_openBoundarySpace
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : Core) → LocalConfig D v.1 → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (incidentRepresentation tail head D U v.1)
      (Matrix.mulVecLin (fun s η ↦ A v η s))) :
    regionalBoundarySpace D (extendedTensor D A) leftVertices (by decide) leftCut (by decide) ⊓
        regionalBoundarySpace D (extendedTensor D A)
          rightVertices (by decide) rightCut (by decide) =
      openBoundarySpace D (extendedTensor D A) := by
  classical
  have hD := nonempty_bonds_of_isSemiRegular D U hU
  let ξL : OutsideRegionEndpointConfig D leftVertices := fun p ↦ Classical.choice (hD p.1.1)
  let ξR : OutsideRegionEndpointConfig D rightVertices := fun p ↦ Classical.choice (hD p.1.1)
  rw [← coreLiftedCutSpace_eq_regionalBoundarySpace D (extendedTensor D A)
      leftVertices (by decide) leftCut (by decide) ξL,
    ← coreLiftedCutSpace_eq_regionalBoundarySpace D (extendedTensor D A)
      rightVertices (by decide) rightCut (by decide) ξR]
  exact coreLiftedCutSpace_inf_eq_openBoundarySpace D U hU A hA

end TNLean.PEPS.ThreeBlockDependent
