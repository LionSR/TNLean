/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionGroundSpace
import QICLean.Algebra.MatrixStarProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Hermitian
import QICLean.ManyBody.Sites.Placement
import QICLean.ManyBody.Dynamics.InteractionOperations
import QICLean.ManyBody.Hamiltonian.FrustrationFree
import QICLean.Algebra.MatrixAux

/-!
# Parent Hamiltonians on finite PEPS graphs

A parent interaction on a region is any positive semidefinite operator whose
kernel is the span of the open-region tensors. It acts as the identity on the
complementary physical indices. The kernel of a finite sum of these interactions
is their common kernel, and the closed PEPS vector belongs to that kernel.

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

/-- Splitting a physical configuration into its region and complement.
Source: arXiv:2011.12127, local-versus-complement factorization, lines 2003–2011. -/
def regionConfigEquiv (R : Finset V) :
    (V → Fin d) ≃ RegionPhysicalConfig (d := d) R ×
      RegionPhysicalConfig (d := d) (Finset.univ \ R) where
  toFun σ := (fun v => σ v.1, fun v => σ v.1)
  invFun p := assembleRegionσ R p.1 p.2
  left_inv σ := by
    funext v
    simp [assembleRegionσ]
  right_inv p := by
    apply Prod.ext <;> funext v
    · exact assembleRegionσ_mem R p.1 p.2 v
    · exact assembleRegionσ_notMem R p.1 p.2 v

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

/-- The placement of a regional operator, extended by the identity on its complement, in the
coordinates of the region and of `univ \ R`.
Source: arXiv:2011.12127, parent Hamiltonian construction, lines 2003–2011. -/
theorem place_eq_regionConfigEquiv (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) :
    ManyBody.place (X := fun _ ↦ Fin d) R h =
      (h ⊗ₖ (1 : Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R))
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ)).submatrix
          (regionConfigEquiv R) (regionConfigEquiv R) := by
  ext σ τ
  simp only [ManyBody.place_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, regionConfigEquiv, Equiv.coe_fn_mk, funext_iff, Subtype.forall,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  split_ifs <;> simp_all

/-- On a fixed complementary configuration the global interaction is exactly
the original regional interaction. Source: arXiv:2011.12127, lines 2003–2011. -/
theorem place_mulVec_assemble (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) (ψ : (V → Fin d) → ℂ)
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (ManyBody.place (X := fun _ ↦ Fin _) R h *ᵥ ψ) (assembleRegionσ R σ τ) =
      (h *ᵥ (fun ν => ψ (assembleRegionσ R ν τ))) σ := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (regionConfigEquiv (d := d) R).symm,
    Fintype.sum_prod_type]
  simp [place_eq_regionConfigEquiv, Matrix.submatrix_apply,
    regionConfigEquiv, Matrix.one_apply]

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

/-- The closed PEPS vector is annihilated by every parent interaction.
Source: arXiv:2011.12127, frustration freeness, lines 2008–2011. -/
theorem place_stateCoeff_eq_zero (A : Tensor Γ d) (R : Finset V)
    {h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) :
    ManyBody.place (X := fun _ ↦ Fin _) R h *ᵥ stateCoeff A = 0 :=
  (place_mulVec_eq_zero_iff A R hh _).mpr
    (stateCoeff_slice_mem_regionGroundSpace A R)

/-! ## Finite families of interactions -/

/-- A physical slice with the complementary configuration fixed.
Source: arXiv:2011.12127, local ground-space conditions, lines 2003–2011. -/
def regionSliceMap (R : Finset V)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    ((V → Fin d) → ℂ) →ₗ[ℂ] (RegionPhysicalConfig (d := d) R → ℂ) where
  toFun ψ σ := ψ (assembleRegionσ R σ τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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
theorem ker_regionParentHamiltonian (A : Tensor Γ d) (R : ι → Finset V)
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

/-- Every term and therefore their sum annihilates the closed PEPS vector.
Source: arXiv:2011.12127, frustration freeness, lines 2008–2011. -/
theorem regionParentHamiltonian_stateCoeff_eq_zero (A : Tensor Γ d) (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i)) :
    (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian *ᵥ stateCoeff A = 0 := by
  exact (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
    (Φ := ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h)
    fun i ↦ ManyBody.posSemidef_place (X := fun _ ↦ Fin _) (hh i).1).mpr
    (fun i => place_stateCoeff_eq_zero A (R i) (hh i))

end TNLean.PEPS
