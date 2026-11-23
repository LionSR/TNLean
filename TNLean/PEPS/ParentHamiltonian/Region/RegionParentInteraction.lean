/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.Region.RegionConfigSplit
import TNLean.PEPS.Tensor.Region.RegionGroundSpace
import QICLean.Analysis.Projection.MatrixStarProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Hermitian
import QICLean.ManyBody.Sites.Placement
import QICLean.ManyBody.Dynamics.InteractionOperations
import QICLean.ManyBody.Hamiltonian.FrustrationFree
import QICLean.Algebra.Matrix.MatrixAux

/-!
# Regional parent interactions of finite PEPS

A parent interaction on a region is any positive semidefinite operator whose
kernel is the span of the open-region tensors; the canonical one is the
orthogonal projector onto the complement of that span. Placed on the whole
graph, it acts as the identity on the complementary physical indices. The
kernel of the parent Hamiltonian of a finite family of these interactions is
their common kernel, and the closed PEPS vector belongs to that kernel.

Source: Cirac, Pérez-García, Schuch, and Verstraete, arXiv:2011.12127,
Section IV.C.1, local source lines 2003–2011.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators Kronecker ComplexOrder Matrix MatrixOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- A positive local interaction with exactly the prescribed PEPS kernel.
The interaction need not be a projector. Source: arXiv:2011.12127,
Section IV.C.1, lines 2003–2011. -/
def IsRegionParentInteraction (A : Tensor Γ d) (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) : Prop :=
  h.PosSemidef ∧ (Matrix.mulVecLin h).ker = regionGroundSpace A R

/-- The regional PEPS ground space with the standard physical inner product.
Source: arXiv:2011.12127, local physical space, lines 2003–2011. -/
noncomputable def regionGroundSpaceES (A : Tensor Γ d) (R : Finset V) :
    Submodule ℂ (EuclideanSpace ℂ (RegionPhysicalConfig (d := d) R)) :=
  (regionGroundSpace A R).map
    (WithLp.linearEquiv 2 ℂ (RegionPhysicalConfig (d := d) R → ℂ)).symm.toLinearMap

/-- The canonical parent interaction is the orthogonal projector onto the
orthogonal complement of the regional ground space.
Source: arXiv:2011.12127, positive interactions with the prescribed kernel,
lines 2003–2011. -/
noncomputable def canonicalRegionParentInteraction (A : Tensor Γ d) (R : Finset V) :
    Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ :=
  Matrix.toEuclideanLin.symm (regionGroundSpaceES A R)ᗮ.starProjection.toLinearMap

/-- The canonical parent interaction is positive semidefinite.
Source: arXiv:2011.12127, lines 2003–2011. -/
theorem canonicalRegionParentInteraction_posSemidef (A : Tensor Γ d) (R : Finset V) :
    (canonicalRegionParentInteraction A R).PosSemidef := by
  classical
  exact Matrix.nonneg_iff_posSemidef.mp
    ((regionGroundSpaceES A R)ᗮ.isStarProjection_starProjectionMatrix).nonneg

/-- The kernel of the canonical regional projector is exactly the local
PEPS ground space. Source: arXiv:2011.12127, lines 2003–2011. -/
theorem ker_canonicalRegionParentInteraction (A : Tensor Γ d) (R : Finset V) :
    (Matrix.mulVecLin (canonicalRegionParentInteraction A R)).ker = regionGroundSpace A R := by
  classical
  ext ψ
  have hact : WithLp.toLp 2 (canonicalRegionParentInteraction A R *ᵥ ψ) =
      (regionGroundSpaceES A R)ᗮ.starProjection (WithLp.toLp 2 ψ) := by
    change Matrix.toEuclideanLin (canonicalRegionParentInteraction A R)
      (WithLp.toLp 2 ψ) = _
    rw [canonicalRegionParentInteraction, LinearEquiv.apply_symm_apply]
    rfl
  change canonicalRegionParentInteraction A R *ᵥ ψ = 0 ↔ _
  rw [← WithLp.toLp_eq_zero (p := 2), hact,
    Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  simp [regionGroundSpaceES]

/-- The canonical orthogonal projector is a parent interaction in the general
positive-operator definition. Source: arXiv:2011.12127, lines 2003–2011. -/
theorem isRegionParentInteraction_canonical (A : Tensor Γ d) (R : Finset V) :
    IsRegionParentInteraction A R (canonicalRegionParentInteraction A R) :=
  ⟨canonicalRegionParentInteraction_posSemidef A R, ker_canonicalRegionParentInteraction A R⟩

/-- A global vector is killed by a regional parent interaction precisely when
every complementary slice belongs to the local PEPS ground space.
Source: arXiv:2011.12127, local parent kernels, lines 2003–2011. -/
theorem place_mulVec_eq_zero_iff (A : Tensor Γ d) (R : Finset V)
    {h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) (ψ : (V → Fin d) → ℂ) :
    ManyBody.place (X := fun _ ↦ Fin _) R h *ᵥ ψ = 0 ↔
      ∀ τ : RegionPhysicalConfig (d := d) (Finset.univ \ R),
        (fun σ => ψ (assembleRegionσ R σ τ)) ∈ regionGroundSpace A R := by
  constructor
  · intro hzero τ
    rw [← hh.2]
    apply LinearMap.mem_ker.mpr
    funext σ
    exact (place_mulVec_assemble R h ψ σ τ).symm.trans (congrFun hzero _)
  · intro hslice
    funext η
    obtain ⟨⟨σ, τ⟩, rfl⟩ := (regionConfigEquiv (d := d) R).symm.surjective η
    change (ManyBody.place (X := fun _ ↦ Fin _) R h *ᵥ ψ) (assembleRegionσ R σ τ) = 0
    rw [place_mulVec_assemble]
    have hmem := hslice τ
    rw [← hh.2] at hmem
    exact congrFun (LinearMap.mem_ker.mp hmem) σ

/-! ## Finite families of interactions -/

variable {ι : Type*} [Fintype ι]

/-- The space satisfying all regional PEPS boundary conditions.
Different terms may have different regions. Source: arXiv:2011.12127,
general-graph and multiple-region construction, lines 2003–2011. -/
noncomputable def regionParentGroundSpace (A : Tensor Γ d) (R : ι → Finset V) :
    Submodule ℂ ((V → Fin d) → ℂ) :=
  ⨅ i, ⨅ τ, (regionGroundSpace A (R i)).comap (regionSliceMap (R i) τ)

/-- The full ground space is the intersection of the regional PEPS conditions.
This characterization is independent of the choice of positive interactions
with those kernels. Source: arXiv:2011.12127, lines 2003–2011. -/
theorem ker_hamiltonian_ofPlace (A : Tensor Γ d) (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i)) :
    (Matrix.mulVecLin (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian).ker =
      regionParentGroundSpace A R := by
  ext ψ
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply,
    ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
      (Φ := ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h)
      fun i ↦ ManyBody.posSemidef_place (X := fun _ ↦ Fin _) (hh i).1,
    ManyBody.Interaction.ofPlace_term,
    place_mulVec_eq_zero_iff A _ (hh _), regionParentGroundSpace,
    Submodule.mem_iInf, Submodule.mem_comap, regionSliceMap, LinearMap.coe_mk,
    AddHom.coe_mk]

omit [Fintype ι] in
/-- The represented PEPS satisfies every parent ground-space condition.
Source: arXiv:2011.12127, frustration freeness, lines 2008–2011. -/
theorem stateCoeff_mem_regionParentGroundSpace (A : Tensor Γ d) (R : ι → Finset V) :
    stateCoeff A ∈ regionParentGroundSpace A R := by
  simp only [regionParentGroundSpace, Submodule.mem_iInf, Submodule.mem_comap]
  exact fun i τ => stateCoeff_slice_mem_regionGroundSpace A (R i) τ

omit [Fintype ι] in
/-- **The closed PEPS vector lies in the zero space of every family of regional parent
interactions**: every placed parent interaction annihilates it.
Source: arXiv:2011.12127, frustration freeness, lines 2008–2011. -/
theorem toLp_stateCoeff_mem_zeroSpace_ofPlace (A : Tensor Γ d) (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i)) :
    WithLp.toLp 2 (stateCoeff A) ∈
      (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).zeroSpace := by
  rw [ManyBody.Interaction.mem_zeroSpace_iff]
  intro i
  rw [ManyBody.Interaction.ofPlace_term]
  exact (place_mulVec_eq_zero_iff A (R i) (hh i) _).mpr
    (stateCoeff_slice_mem_regionGroundSpace A (R i))

end TNLean.PEPS
