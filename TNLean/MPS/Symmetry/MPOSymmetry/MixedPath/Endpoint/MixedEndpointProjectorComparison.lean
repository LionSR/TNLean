/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Endpoint.MixedEndpointSectors
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Endpoint.MixedEndpointReducingSectors

/-!
# Endpoint interaction comparisons from the physical sectors

For the actual mixed endpoint tensor, the canonical first-endpoint support
projector is the product of the extended-support projector with its two
outer physical sector projections. This gives the local comparison needed
for the periodic endpoint Hamiltonian. The two missing outer sectors are
controlled by the inner sectors of the adjacent extended interactions.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

private theorem symmetricProjection_one_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) :
    (1 - P).IsSymmetricProjection :=
  ⟨hP.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hP.isSymmetric⟩

/-- Every physical row-sector selector is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointRowSector_isSymmetricProjection (site : Fin 2) :
    (mixedEndpointRowSector D₀ D₁ site).IsSymmetricProjection := by
  refine ⟨?_, mixedEndpointRowSector_isSymmetric site⟩
  ext v σ
  simp only [Module.End.mul_apply, mixedEndpointRowSector_apply]
  unfold bondInterpolationWeight
  split <;> simp

/-- Every physical column-sector selector is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointColumnSector_isSymmetricProjection (site : Fin 2) :
    (mixedEndpointColumnSector D₀ D₁ site).IsSymmetricProjection := by
  refine ⟨?_, mixedEndpointColumnSector_isSymmetric site⟩
  ext v σ
  simp only [Module.End.mul_apply, mixedEndpointColumnSector_apply]
  unfold bondInterpolationWeight
  split <;> simp

/-- Physical row and column sectors commute, including at different sites.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointRowSector_commute_columnSector (i j : Fin 2) :
    Commute (mixedEndpointRowSector D₀ D₁ i) (mixedEndpointColumnSector D₀ D₁ j) := by
  apply (commute_iff_eq _ _).mpr
  ext v σ
  simp only [Module.End.mul_apply, mixedEndpointRowSector_apply,
    mixedEndpointColumnSector_apply]
  exact mul_left_comm _ _ _

/-- The first endpoint's canonical support projector is the product of its
actual extended-support projector and the two outer sector projections.
No commutation or support identity is assumed: both were derived from
boundary matrix transport. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointLeftTensor_starProjection_eq_outerCorner
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    ((groundSpace (mixedEndpointLeftTensor A₀ D₁) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection.toLinearMap =
      mixedEndpointRowSector D₀ D₁ 0 * mixedEndpointColumnSector D₀ D₁ 1 *
        (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
          (bondInterpolationMatrix D₀ D₁ 0)).range.starProjection.toLinearMap := by
  let S := (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
    (bondInterpolationMatrix D₀ D₁ 0)).range
  let R := mixedEndpointRowSector D₀ D₁ 0
  let C := mixedEndpointColumnSector D₀ D₁ 1
  have hRC := mixedEndpointRowSector_commute_columnSector (D₀ := D₀) (D₁ := D₁) 0 1
  have hRP := mixedEndpointRowSector_commute_extendedSupport_starProjection A₀ A₁
    (bondInterpolationMatrix D₀ D₁ 0)
  have hCP := mixedEndpointColumnSector_commute_extendedSupport_starProjection A₀ A₁
    (bondInterpolationMatrix D₀ D₁ 0)
  have hprod : (R * C * S.starProjection.toLinearMap).IsSymmetricProjection :=
    LinearMap.IsSymmetricProjection.mul_of_commute
      (LinearMap.IsSymmetricProjection.mul_of_commute
        (mixedEndpointRowSector_isSymmetricProjection 0)
        (mixedEndpointColumnSector_isSymmetricProjection 1) hRC)
      (Submodule.isSymmetricProjection_starProjection S) (hRP.mul_left hCP)
  symm
  apply hprod.ext (Submodule.isSymmetricProjection_starProjection _)
  rw [Submodule.range_starProjection]
  rw [← mixedEndpoint_extendedSupport_outerCorner_eq_map_groundSpace A₀ A₁]
  change LinearMap.range (R * C * S.starProjection.toLinearMap) = S.map (R.comp C)
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨S.starProjection v, S.starProjection_apply_mem v, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨v, ?_⟩
    change R (C (S.starProjection v)) = R (C v)
    rw [S.starProjection_eq_self_iff.mpr hv]

/-- The operator of the extended local interaction is an orthogonal projection at every
parameter, including both endpoints. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem isSymmetricProjection_toEuclideanLin_mixedEndpointParentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (γ : ℝ) :
    (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ γ)).IsSymmetricProjection := by
  rw [toEuclideanLin_mixedEndpointParentInteraction]
  exact symmetricProjection_one_sub (Submodule.isSymmetricProjection_starProjection _)

/-- The extended local interaction is positive at every parameter, including
both endpoints. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem posSemidef_mixedEndpointParentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (γ : ℝ) :
    (mixedEndpointParentInteraction A₀ A₁ γ).PosSemidef :=
  Matrix.isPositive_toEuclideanLin_iff.mp
    (isSymmetricProjection_toEuclideanLin_mixedEndpointParentInteraction A₀ A₁ γ).isPositive

/-- The extended first-endpoint term is bounded above by the canonical
embedded first-endpoint term. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointParentInteraction_zero_le_parentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 0) ≤
      Matrix.toEuclideanLin
        (LinearMap.toMatrix' (parentInteraction (mixedEndpointLeftTensor A₀ D₁) 2)) := by
  have hle : ((groundSpace (mixedEndpointLeftTensor A₀ D₁) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection.toLinearMap ≤
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0)).range.starProjection.toLinearMap := by
    apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
      (Submodule.isSymmetricProjection_starProjection _) |>.mpr
    simpa only [Submodule.range_starProjection] using
      map_groundSpace_mixedEndpointLeftTensor_le_extendedSupport A₀ A₁
  simpa only [toEuclideanLin_mixedEndpointParentInteraction,
    toEuclideanLin_toMatrix'_parentInteraction,
    Submodule.starProjection_orthogonal', ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one] using sub_le_sub_left hle 1

/-- The canonical embedded endpoint interaction is at most the extended
interaction plus its two outer sector penalties. These penalties are supplied
by the neighboring extended terms on a ring.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem parentInteraction_mixedEndpointLeftTensor_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Matrix.toEuclideanLin
      (LinearMap.toMatrix' (parentInteraction (mixedEndpointLeftTensor A₀ D₁) 2)) ≤
      Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 0) +
        (1 - mixedEndpointRowSector D₀ D₁ 0) +
        (1 - mixedEndpointColumnSector D₀ D₁ 1) := by
  let S := (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
    (bondInterpolationMatrix D₀ D₁ 0)).range
  have hP : S.starProjection.toLinearMap.IsSymmetricProjection :=
    Submodule.isSymmetricProjection_starProjection S
  have hupper := LinearMap.IsSymmetricProjection.one_sub_mul_mul_le hP
    (mixedEndpointRowSector_isSymmetricProjection (D₀ := D₀) (D₁ := D₁) 0)
    (mixedEndpointColumnSector_isSymmetricProjection (D₀ := D₀) (D₁ := D₁) 1)
    (mixedEndpointRowSector_commute_columnSector (D₀ := D₀) (D₁ := D₁) 0 1)
    (mixedEndpointRowSector_commute_extendedSupport_starProjection A₀ A₁
      (bondInterpolationMatrix D₀ D₁ 0))
    (mixedEndpointColumnSector_commute_extendedSupport_starProjection A₀ A₁
      (bondInterpolationMatrix D₀ D₁ 0))
  simpa only [toEuclideanLin_toMatrix'_parentInteraction,
    Submodule.starProjection_orthogonal',
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one,
    mixedEndpointLeftTensor_starProjection_eq_outerCorner A₀ A₁,
    toEuclideanLin_mixedEndpointParentInteraction] using hupper

private theorem extendedSupport_starProjection_le_sector
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (Q : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2))
    (hQ : Q.IsSymmetricProjection)
    (hfix : ∀ v, Q (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
      (bondInterpolationMatrix D₀ D₁ 0) v) =
        insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0) v) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
      (bondInterpolationMatrix D₀ D₁ 0)).range.starProjection.toLinearMap ≤ Q := by
  apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range hQ |>.mpr
  rw [Submodule.range_starProjection]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, hfix v⟩

/-- The first-column sector penalty is bounded by the extended endpoint
interaction because the extended support lies in that sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_one_sub_columnSector_zero_le_parentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    1 - mixedEndpointColumnSector D₀ D₁ 0 ≤
      Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 0) := by
  rw [toEuclideanLin_mixedEndpointParentInteraction]
  exact sub_le_sub_left (extendedSupport_starProjection_le_sector A₀ A₁ _
    (mixedEndpointColumnSector_isSymmetricProjection 0)
    (mixedEndpointColumnSector_zero_insertedTwoSiteMap A₀ A₁)) 1

/-- The second-row sector penalty is bounded by the extended endpoint
interaction because the extended support lies in that sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_one_sub_rowSector_one_le_parentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    1 - mixedEndpointRowSector D₀ D₁ 1 ≤
      Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 0) := by
  rw [toEuclideanLin_mixedEndpointParentInteraction]
  exact sub_le_sub_left (extendedSupport_starProjection_le_sector A₀ A₁ _
    (mixedEndpointRowSector_isSymmetricProjection 1)
    (mixedEndpointRowSector_one_insertedTwoSiteMap A₀ A₁)) 1

end MPOSymmetry
end MPSTensor
