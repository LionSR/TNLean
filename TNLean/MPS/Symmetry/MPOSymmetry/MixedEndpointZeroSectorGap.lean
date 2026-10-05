/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison

/-!
# The zero second-sector comparator and its intrinsic open gap

When the second bond summand has dimension zero, the actual mixed tensor
is the original endpoint tensor, the zero-parameter inserted weight is the
identity, and the extended local interaction is the ordinary two-site
parent interaction. Every physical configuration is active. The already
constructed active-coordinate isometry is therefore onto and transports
the actual active Hamiltonian unitarily to the ordinary open parent.

The ordinary injective-parent uniform gap consequently gives a uniform gap
for this concrete member of the same active mixed family. No supplied gap,
projector comparison, or kernel hypothesis is used. The zero-dimensional
first sector is handled directly as the zero Hilbert space.

Source: arXiv:2203.12563, Section 5, lines 1690–1692; the ordinary open-gap
input is the one-site-injective two-site parent theorem developed from
Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1.
-/

open scoped Matrix InnerProductSpace BigOperators

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ N : ℕ}

/-- The unique tensor on the empty second bond and physical sector.
Source context: arXiv:2203.12563, Section 5, the degenerate direct-sum comparator. -/
def emptyEndpointTensor : MPSTensor (0 * 0) 0 := fun p => Fin.elim0 p

private theorem finSumFinEquiv_symm_zeroSector (i : Fin D₀) :
    (finSumFinEquiv : Fin D₀ ⊕ Fin 0 ≃ Fin (D₀ + 0)).symm i = Sum.inl i := by
  exact finSumFinEquiv_symm_apply_castAdd (n := 0) i

/-- With no second sector, the actual unweighted mixed tensor is `A₀`.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
@[simp]
theorem mixedEndpointBase_emptyEndpointTensor
    (A₀ : MPSTensor (D₀ * D₀) D₀) : mixedEndpointBase A₀ emptyEndpointTensor = A₀ := by
  ext p i j
  simp [mixedEndpointBase, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_zeroSector, mixedEndpointLetter, Matrix.fromBlocks]
  exact congrArg (fun q : Fin (D₀ * D₀) => A₀ q i j)
    (finProdFinEquiv.apply_symm_apply p)

/-- Every zero-parameter bond weight is one when the second sector is empty.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
@[simp]
theorem bondInterpolationWeight_zeroSector (i : Fin D₀) :
    bondInterpolationWeight D₀ 0 0 i = 1 := by
  simp [bondInterpolationWeight, finSumFinEquiv_symm_zeroSector]

/-- The actual endpoint insertion is the identity in the zero second-sector
family. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem bondInterpolationMatrix_zeroSector :
    bondInterpolationMatrix D₀ 0 0 = (1 : Matrix (Fin D₀) (Fin D₀) ℂ) := by
  ext i j
  simp [bondInterpolationMatrix, Matrix.diagonal_apply, Matrix.one_apply]

/-- The actual extended local interaction in this comparator is exactly the
ordinary `A₀` parent interaction. No injectivity is needed for the equality.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointParentInteraction_zeroSector_eq_parentInteractionES
    (A₀ : MPSTensor (D₀ * D₀) D₀) :
    (mixedEndpointParentInteraction A₀ emptyEndpointTensor 0).toLinearMap =
      parentInteractionES A₀ 2 := by
  have hsupport :
      (insertedTwoSiteMap (mixedEndpointBase A₀ emptyEndpointTensor)
        (bondInterpolationMatrix D₀ 0 0)).range = groundSpaceES A₀ 2 := by
    rw [mixedEndpointBase_emptyEndpointTensor, bondInterpolationMatrix_zeroSector]
    simpa only [Matrix.mul_one] using
      range_insertedTwoSiteMap_eq_groundSpaceES A₀ (1 : Matrix (Fin D₀) (Fin D₀) ℂ) isUnit_one
  have hproj := congrArg
    (fun S : Submodule ℂ (EuclideanSpace ℂ (Cfg (D₀ * D₀) 2)) => S.starProjection)
    hsupport
  rw [mixedEndpointParentInteraction, hproj]
  simp only [parentInteractionES, Submodule.starProjection_orthogonal']

/-- The full actual nonwrapping sum is the ordinary open parent Hamiltonian
at every volume. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem openInteractionHamiltonianES_zeroSector_eq_openParentHamiltonianES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (M : ℕ) :
    openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ emptyEndpointTensor 0).toLinearMap M =
      openParentHamiltonianES A₀ 2 M := by
  rw [mixedEndpointParentInteraction_zeroSector_eq_parentInteractionES]
  simp only [openInteractionHamiltonianES, openParentHamiltonianES,
    periodicLocalInteractionES_parentInteractionES A₀ (by norm_num : 0 < 2)]

/-- Every physical configuration is active in the zero second-sector family.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenInnerActive_zeroSector
    (σ : Cfg ((D₀ + 0) * (D₀ + 0)) N) :
    MixedEndpointOpenInnerActive (D₁ := 0) σ := by
  simp [MixedEndpointOpenInnerActive]

/-- The actual active projection is the identity when the second sector is
empty. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem mixedEndpointOpenActiveProjection_zeroSector (D₀ N : ℕ) :
    mixedEndpointOpenActiveProjection D₀ 0 N = LinearMap.id := by
  ext v σ
  rw [mixedEndpointOpenActiveProjection_apply]
  simp [mixedEndpointOpenInnerActive_zeroSector]

/-- The active-coordinate isometry has no omitted physical subspace in the
zero second-sector case. Its adjoint supplies an explicit preimage.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveLinearIsometry_zeroSector_surjective (D₀ N : ℕ) :
    Function.Surjective (mixedEndpointActiveLinearIsometry D₀ 0 N) := by
  intro w
  refine ⟨(mixedEndpointActiveLinearIsometry D₀ 0 N).toLinearMap.adjoint w, ?_⟩
  change ((mixedEndpointActiveLinearIsometry D₀ 0 N).toLinearMap ∘ₗ
    (mixedEndpointActiveLinearIsometry D₀ 0 N).toLinearMap.adjoint) w = w
  rw [mixedEndpointActiveLinearIsometry_comp_adjoint,
    mixedEndpointOpenActiveProjection_zeroSector, LinearMap.id_apply]

/-- The existing active inclusion becomes a genuine Euclidean isometric
equivalence in the zero second-sector family.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointZeroSectorActiveEquiv (D₀ N : ℕ) :
    mixedEndpointActiveSpace D₀ 0 N ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg (D₀ * D₀) (N + 1 + 1)) where
  toLinearEquiv := LinearEquiv.ofLinearMap (σ₁₂ := RingHom.id ℂ) (σ₂₁ := RingHom.id ℂ)
    (re₁₂ := inferInstance) (re₂₁ := inferInstance)
    (mixedEndpointActiveLinearIsometry D₀ 0 N).toLinearMap
    (mixedEndpointActiveLinearIsometry D₀ 0 N).toLinearMap.adjoint
    (by rw [mixedEndpointActiveLinearIsometry_comp_adjoint,
      mixedEndpointOpenActiveProjection_zeroSector])
    (mixedEndpointActiveLinearIsometry_adjoint_comp)
  norm_map' v := (mixedEndpointActiveLinearIsometry D₀ 0 N).norm_map v

/-- This equivalence uses exactly the actual coordinate inclusion.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem mixedEndpointZeroSectorActiveEquiv_toLinearMap (D₀ N : ℕ) :
    (mixedEndpointZeroSectorActiveEquiv D₀ N).toLinearEquiv.toLinearMap =
      (mixedEndpointActiveLinearIsometry D₀ 0 N).toLinearMap := rfl

/-- The intrinsic ordinary open parent and this concrete active family
intertwine with no loss of norms or changes of interaction range.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveHamiltonian_zeroSector_intertwines
    (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) (v : mixedEndpointActiveSpace D₀ 0 N) :
    mixedEndpointActiveLinearIsometry D₀ 0 N
        (mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N v) =
      openParentHamiltonianES A₀ 2 (N + 1 + 1) (mixedEndpointActiveLinearIsometry D₀ 0 N v) := by
  simpa only [openInteractionHamiltonianES_zeroSector_eq_openParentHamiltonianES] using
    mixedEndpointActiveHamiltonian_intertwines A₀ emptyEndpointTensor N v

/-- Exact unitary compression identity for the zero-sector active family.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveHamiltonian_zeroSector_eq_conjugate_openParent
    (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) :
    mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N =
      (mixedEndpointZeroSectorActiveEquiv D₀ N).toLinearEquiv.toLinearMap.adjoint ∘ₗ
        openParentHamiltonianES A₀ 2 (N + 1 + 1) ∘ₗ
          (mixedEndpointZeroSectorActiveEquiv D₀ N).toLinearEquiv.toLinearMap := by
  simp only [mixedEndpointActiveHamiltonian_eq_compression,
    openInteractionHamiltonianES_zeroSector_eq_openParentHamiltonianES,
    mixedEndpointZeroSectorActiveEquiv_toLinearMap, mixedEndpointActiveCompression]

/-- The actual zero-second-sector active Hamiltonians have an intrinsic
positive gap uniformly in sufficiently long chains, derived solely from
one-site injectivity of `A₀`. No gap or kernel identification is supplied.
The zero-dimensional first sector is covered directly by the zero space.
Source: arXiv:2203.12563, Section 5, lines 1690–1692, using the ordinary
open-parent gap of Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1. -/
theorem exists_mixedEndpointActiveHamiltonian_zeroSector_uniform_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    ∃ W : ℕ, 2 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N + 1 + 1 →
        ∀ v ∈ (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N))ᗮ,
          δ * ‖v‖ ≤ ‖mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N v‖ := by
  by_cases hD₀ : D₀ = 0
  · subst D₀
    refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
    intro N _ v _
    have hv : v = 0 := by
      apply PiLp.ext
      rintro ⟨a, κ, e⟩
      exact isEmptyElim a
    simp [hv]
  · let : NeZero D₀ := ⟨hD₀⟩
    obtain ⟨W, hW, δ, hδ, hGap⟩ :=
      exists_openParentHamiltonianES_two_uniform_gap_of_isInjective A₀ hA₀
    refine ⟨W, hW, δ, hδ, ?_⟩
    intro N hWN v hv
    let U : mixedEndpointActiveSpace D₀ 0 N →ₗᵢ[ℂ]
        EuclideanSpace ℂ (Cfg (D₀ * D₀) (N + 1 + 1)) :=
      mixedEndpointActiveLinearIsometry D₀ 0 N
    have hker : LinearMap.ker (openParentHamiltonianES A₀ 2 (N + 1 + 1)) =
        groundSpaceES A₀ (N + 1 + 1) :=
      ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        (Kraus.isNBlkInjective_one_of_isInjective hA₀) (by norm_num) (by omega)
    have hUv : U v ∈ (groundSpaceES A₀ (N + 1 + 1))ᗮ := by
      rw [← hker]
      apply (Submodule.mem_orthogonal _ _).mpr
      intro w hw
      obtain ⟨u, rfl⟩ := mixedEndpointActiveLinearIsometry_zeroSector_surjective D₀ N w
      have hu : u ∈ LinearMap.ker (mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N) := by
        rw [ker_mixedEndpointActiveHamiltonian,
          openInteractionHamiltonianES_zeroSector_eq_openParentHamiltonianES]
        exact hw
      simpa only [U, LinearIsometry.inner_map_map] using
        (Submodule.mem_orthogonal _ _).mp hv u hu
    have h := hGap (N + 1 + 1) hWN (U v) hUv
    rw [← mixedEndpointActiveHamiltonian_zeroSector_intertwines A₀ N v] at h
    simpa only [U, LinearIsometry.norm_map] using h

end

end MPOSymmetry
end MPSTensor
