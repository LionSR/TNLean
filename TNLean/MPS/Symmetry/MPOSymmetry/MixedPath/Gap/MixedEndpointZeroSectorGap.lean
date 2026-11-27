/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointActiveHamiltonian
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison
import QICLean.Spectral.Gap.IsometricConjugationGap

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

open scoped Matrix InnerProductSpace BigOperators ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

open ManyBody.Interaction (chainTranslates)

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
  simp only [mixedEndpointBase, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_zeroSector, mixedEndpointLetter, Matrix.fromBlocks_apply₁₁]
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
theorem mixedEndpointParentInteraction_zeroSector_eq_toMatrix'_parentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) :
    mixedEndpointParentInteraction A₀ emptyEndpointTensor 0 =
      LinearMap.toMatrix' (parentInteraction A₀ 2) := by
  apply Matrix.toEuclideanLin.injective
  have hsupport :
      (insertedTwoSiteMap (mixedEndpointBase A₀ emptyEndpointTensor)
        (bondInterpolationMatrix D₀ 0 0)).range = ((groundSpace A₀ 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
    rw [mixedEndpointBase_emptyEndpointTensor, bondInterpolationMatrix_zeroSector]
    simpa only [Matrix.mul_one] using
      range_insertedTwoSiteMap_eq_map_groundSpace A₀ (1 : Matrix (Fin D₀) (Fin D₀) ℂ) isUnit_one
  have hproj := congrArg
    (fun S : Submodule ℂ (EuclideanSpace ℂ (Cfg (D₀ * D₀) 2)) => S.starProjection)
    hsupport
  rw [toEuclideanLin_mixedEndpointParentInteraction, hproj,
    toEuclideanLin_toMatrix'_parentInteraction]
  simp only [Submodule.starProjection_orthogonal']

/-- The full actual nonwrapping sum is the ordinary open parent Hamiltonian
at every volume. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem hamiltonian_chainTranslates_zeroSector_eq_hamiltonian_parentChainInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (M : ℕ) :
    (chainTranslates 2 M
        (mixedEndpointParentInteraction A₀ emptyEndpointTensor 0)).hamiltonian =
      (parentChainInteraction A₀ 2 M).hamiltonian := by
  rw [mixedEndpointParentInteraction_zeroSector_eq_toMatrix'_parentInteraction]

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
      Matrix.toEuclideanLin (parentChainInteraction A₀ 2 (N + 1 + 1)).hamiltonian
          (mixedEndpointActiveLinearIsometry D₀ 0 N v) := by
  simpa only
    [hamiltonian_chainTranslates_zeroSector_eq_hamiltonian_parentChainInteraction] using
    mixedEndpointActiveHamiltonian_intertwines A₀ emptyEndpointTensor N v

/-- Exact unitary compression identity for the zero-sector active family.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveHamiltonian_zeroSector_eq_conjugate_openParent
    (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) :
    mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N =
      (mixedEndpointZeroSectorActiveEquiv D₀ N).toLinearEquiv.toLinearMap.adjoint ∘ₗ
        Matrix.toEuclideanLin (parentChainInteraction A₀ 2 (N + 1 + 1)).hamiltonian ∘ₗ
          (mixedEndpointZeroSectorActiveEquiv D₀ N).toLinearEquiv.toLinearMap := by
  simp only [mixedEndpointActiveHamiltonian_eq_compression,
    hamiltonian_chainTranslates_zeroSector_eq_hamiltonian_parentChainInteraction,
    mixedEndpointZeroSectorActiveEquiv_toLinearMap, mixedEndpointActiveCompression]

/-- The actual zero-second-sector active Hamiltonians have an intrinsic
positive gap uniformly in sufficiently long chains, derived solely from
one-site injectivity of `A₀`: every eigenvalue is `0` or at least the gap.
No gap or kernel identification is supplied. The isometric equivalence with
the ordinary open parent carries its eigenvalues over unchanged. The
zero-dimensional first sector is covered directly by the zero space.
Source: arXiv:2203.12563, Section 5, lines 1690–1692, using the ordinary
open-parent gap of Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1. -/
theorem exists_mixedEndpointActiveHamiltonian_zeroSector_uniform_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    ∃ W : ℕ, 2 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N + 1 + 1 → ∀ μ : ℂ, Module.End.HasEigenvalue
          (mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  by_cases hD₀ : D₀ = 0
  · subst D₀
    refine ⟨2, by norm_num, 1, by norm_num, fun N _ μ hμ ↦ ?_⟩
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine absurd ?_ hv.2
    apply PiLp.ext
    rintro ⟨a, κ, e⟩
    exact isEmptyElim a
  · let : NeZero D₀ := ⟨hD₀⟩
    obtain ⟨W, hW, δ, hδ, hGap⟩ :=
      exists_hamiltonian_parentChainInteraction_two_uniform_gap_of_isInjective A₀ hA₀
    refine ⟨W, hW, δ, hδ, fun N hWN μ hμ ↦ hGap (N + 1 + 1) hWN μ ?_⟩
    let U := mixedEndpointZeroSectorActiveEquiv D₀ N
    have hconj : U.toLinearEquiv.conj
        (mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N) =
        Matrix.toEuclideanLin (parentChainInteraction A₀ 2 (N + 1 + 1)).hamiltonian := by
      refine LinearMap.ext fun w ↦ ?_
      obtain ⟨v, rfl⟩ := U.surjective w
      change U (mixedEndpointActiveHamiltonian A₀ emptyEndpointTensor N (U.symm (U v))) = _
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact mixedEndpointActiveHamiltonian_zeroSector_intertwines A₀ N v
    exact (U.hasEigenvalue_iff_of_conj _ _ hconj μ).mp hμ

end

end MPOSymmetry
end MPSTensor
