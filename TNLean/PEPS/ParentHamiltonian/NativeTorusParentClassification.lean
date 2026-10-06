/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.NativeTorusParentSpanning
import TNLean.PEPS.ParentHamiltonian.NativeTorusClosureMembership
import TNLean.PEPS.NativeTorusClosureDimension

/-!
# Exact native nonuniform plaquette-parent classification

The kernel of every genuine positive microscopic plaquette parent equals the
span of its actual commuting closure vectors. Every original edge retains
its own semi-regular representation and every site its own G-injective tensor.
The dimension is precisely the number of simultaneous conjugacy classes of
commuting pairs. No cut, span, flatness, or independence premise is supplied.

Source: SCP10, arXiv:1001.3807, Theorems 5.7 and 5.9. This is the finite native
simple-graph formulation with both torus periods at least three. Independent
physical alphabets are handled by faithful coordinate padding in the subsequent
nonuniform classification, rather than by replacing the parent definition.
-/

noncomputable section
namespace TNLean.PEPS
open DependentBondNetwork

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G] [Finite G] {d : ℕ}

/-- The actual plaquette parent space is exactly the native commuting-closure
span for independent bonds and unrelated G-injective sites. Source: SCP10, Theorem 5.7. -/
theorem torusPlaquetteParentGroundSpace_eq_nativeCommutingClosureSpan
    (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v)) :
    regionParentGroundSpace A torusPlaquetteRegion =
      NativeTorus.commutingClosureSpan (graphBondAlphabet A) U (graphDependentTensor A) := by
  exact le_antisymm (torusPlaquetteParentGroundSpace_le_nativeCommutingClosureSpan A U hU hA)
    (nativeCommutingClosureSpan_le_torusPlaquetteParentGroundSpace A U
      (fun v ↦ (hA v).invariant))

/-- Every positive microscopic plaquette parent with the prescribed local kernels
has exactly the actual native commuting-closure span as its full ambient kernel.
Source: SCP10, Theorem 5.7, for the native simple-graph torus. -/
theorem ker_torusPlaquetteParentHamiltonian_eq_nativeCommutingClosureSpan
    (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v))
    (H : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hH : ∀ v, IsRegionParentInteraction A (torusPlaquetteRegion v) (H v)) :
    (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker =
      NativeTorus.commutingClosureSpan (graphBondAlphabet A) U (graphDependentTensor A) := by
  rw [ker_regionParentHamiltonian A torusPlaquetteRegion H hH,
    torusPlaquetteParentGroundSpace_eq_nativeCommutingClosureSpan A U hU hA]

/-- The full physical kernel has one dimension per commuting pair class, with
independent semi-regular bond representations and no independence hypothesis.
Source: SCP10, Theorem 5.9, for native simple tori of periods at least three. -/
theorem finrank_ker_torusPlaquetteParentHamiltonian
    (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v))
    (H : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hH : ∀ v, IsRegionParentInteraction A (torusPlaquetteRegion v) (H v)) :
    Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker =
      Nat.card (CommutingPairConjugacyClass G) := by
  rw [ker_torusPlaquetteParentHamiltonian_eq_nativeCommutingClosureSpan A U hU hA H hH]
  exact NativeTorus.finrank_commutingClosureSpan (graphBondAlphabet A) U hU
    (graphDependentTensor A) hA

end TNLean.PEPS
