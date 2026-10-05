/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSectors

/-!
# Reducing physical sectors of the extended support

The actual physical sector maps are self-adjoint. Their derived invariance
of the mixed tensor's extended support therefore implies commutation with
its orthogonal projector. Source: arXiv:2203.12563, Section 5,
lines 1690–1692, the endpoint parent interaction.
-/

open scoped Matrix InnerProductSpace

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

private theorem diagonal_bondWeight_isSymmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Fin (D₀ + D₁)) :
    (Matrix.toEuclideanLin (Matrix.diagonal fun i =>
      bondInterpolationWeight D₀ D₁ 0 (f i))).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  change star (fun i => bondInterpolationWeight D₀ D₁ 0 (f i)) = _
  funext i
  simp only [Pi.star_apply]
  unfold bondInterpolationWeight
  split <;> simp

/-- The physical row-sector map is self-adjoint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointRowSector_isSymmetric (site : Fin 2) :
    (mixedEndpointRowSector D₀ D₁ site).IsSymmetric := by
  unfold mixedEndpointRowSector
  exact diagonal_bondWeight_isSymmetric (D₀ := D₀) (D₁ := D₁)
    (ι := Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
    (fun σ => (finProdFinEquiv.symm (σ site)).1)

/-- The physical column-sector map is self-adjoint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointColumnSector_isSymmetric (site : Fin 2) :
    (mixedEndpointColumnSector D₀ D₁ site).IsSymmetric := by
  unfold mixedEndpointColumnSector
  exact diagonal_bondWeight_isSymmetric (D₀ := D₀) (D₁ := D₁)
    (ι := Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
    (fun σ => (finProdFinEquiv.symm (σ site)).2)

private theorem commute_starProjection_of_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (Q : E →ₗ[ℂ] E) (hQ : Q.IsSymmetric) (hS : S.map Q ≤ S) :
    Commute Q S.starProjection.toLinearMap := by
  have hmem (v : E) (hv : v ∈ S) : Q v ∈ S := hS ⟨v, hv, rfl⟩
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  change Q (S.starProjection v) = S.starProjection (Q v)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := S)
  · exact hmem _ (S.starProjection_apply_mem v)
  · intro w hw
    rw [← map_sub, hQ]
    exact Submodule.starProjection_inner_eq_zero (K := S) v (Q w) (hmem w hw)

/-- The first row sector reduces the orthogonal projector onto the actual
extended support. This follows from the explicit boundary transport,
without assuming projector commutation.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointRowSector_commute_extendedSupport_starProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (W : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    Commute (mixedEndpointRowSector D₀ D₁ 0)
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W).range.starProjection.toLinearMap :=
  commute_starProjection_of_invariant _ _ (mixedEndpointRowSector_isSymmetric 0)
    (range_insertedTwoSiteMap_invariant_rowSector A₀ A₁ W)

/-- The second column sector reduces the orthogonal projector onto the
actual extended support. This follows from explicit boundary transport.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointColumnSector_commute_extendedSupport_starProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (W : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    Commute (mixedEndpointColumnSector D₀ D₁ 1)
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W).range.starProjection.toLinearMap :=
  commute_starProjection_of_invariant _ _ (mixedEndpointColumnSector_isSymmetric 1)
    (range_insertedTwoSiteMap_invariant_columnSector A₀ A₁ W)

end MPOSymmetry
end MPSTensor
