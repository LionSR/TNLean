/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointCornerSupport
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointReducingSectors

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

private theorem symmetricProjection_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection)
    (hQ : Q.IsSymmetricProjection) (hPQ : Commute P Q) :
    (P * Q).IsSymmetricProjection :=
  ⟨hP.isIdempotentElem.mul_of_commute hPQ hQ.isIdempotentElem,
    hP.isSymmetric.mul_of_commute hQ.isSymmetric hPQ⟩

private theorem symmetricProjection_one_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) :
    (1 - P).IsSymmetricProjection :=
  ⟨hP.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hP.isSymmetric⟩

private theorem one_sub_mul_le_add_one_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection)
    (hQ : Q.IsSymmetricProjection) (hPQ : Commute P Q) :
    1 - P * Q ≤ (1 - P) + (1 - Q) := by
  have hcomm : Commute (1 - P) (1 - Q) :=
    (Commute.one_left (1 - Q)).sub_left ((Commute.one_right P).sub_right hPQ)
  have hpos := (symmetricProjection_mul (symmetricProjection_one_sub hP)
    (symmetricProjection_one_sub hQ) hcomm).isPositive
  rw [LinearMap.le_def]
  convert hpos using 1
  noncomm_ring

private theorem one_sub_mul_mul_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P R C : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection)
    (hR : R.IsSymmetricProjection) (hC : C.IsSymmetricProjection)
    (hRC : Commute R C) (hRP : Commute R P) (hCP : Commute C P) :
    1 - R * C * P ≤ (1 - P) + (1 - R) + (1 - C) := by
  have h₁ := one_sub_mul_le_add_one_sub
    (symmetricProjection_mul hR hC hRC) hP (hRP.mul_left hCP)
  have h₂ := one_sub_mul_le_add_one_sub (P := R) (Q := C) hR hC hRC
  change ((1 - R * C) + (1 - P) - (1 - R * C * P)).IsPositive at h₁
  change ((1 - R) + (1 - C) - (1 - R * C)).IsPositive at h₂
  rw [LinearMap.le_def]
  convert h₁.add h₂ using 1
  abel

/-- Every physical row-sector selector is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointRowSector_isSymmetricProjection (site : Fin 2) :
    (mixedEndpointRowSector D₀ D₁ site).IsSymmetricProjection := by
  refine ⟨?_, mixedEndpointRowSector_isSymmetric site⟩
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  simp only [Module.End.mul_apply, mixedEndpointRowSector_apply]
  unfold bondInterpolationWeight
  split <;> simp

/-- Every physical column-sector selector is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointColumnSector_isSymmetricProjection (site : Fin 2) :
    (mixedEndpointColumnSector D₀ D₁ site).IsSymmetricProjection := by
  refine ⟨?_, mixedEndpointColumnSector_isSymmetric site⟩
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  simp only [Module.End.mul_apply, mixedEndpointColumnSector_apply]
  unfold bondInterpolationWeight
  split <;> simp

/-- Physical row and column sectors commute, including at different sites.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointRowSector_commute_columnSector (i j : Fin 2) :
    Commute (mixedEndpointRowSector D₀ D₁ i) (mixedEndpointColumnSector D₀ D₁ j) := by
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  simp only [Module.End.mul_apply, mixedEndpointRowSector_apply,
    mixedEndpointColumnSector_apply]
  exact mul_left_comm _ _ _

/-- The first endpoint's canonical support projector is the product of its
actual extended-support projector and the two outer sector projections.
No commutation or support identity is assumed: both were derived from
boundary matrix transport. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointLeftTensor_starProjection_eq_outerCorner
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (groundSpaceES (mixedEndpointLeftTensor A₀ D₁) 2).starProjection.toLinearMap =
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
    symmetricProjection_mul
      (symmetricProjection_mul (mixedEndpointRowSector_isSymmetricProjection 0)
        (mixedEndpointColumnSector_isSymmetricProjection 1) hRC)
      (Submodule.isSymmetricProjection_starProjection S) (hRP.mul_left hCP)
  symm
  apply hprod.ext (Submodule.isSymmetricProjection_starProjection _)
  rw [Submodule.range_starProjection]
  rw [← mixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES A₀ A₁]
  change LinearMap.range (R * C * S.starProjection.toLinearMap) = S.map (R.comp C)
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨S.starProjection v, S.starProjection_apply_mem v, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨v, ?_⟩
    change R (C (S.starProjection v)) = R (C v)
    rw [S.starProjection_eq_self_iff.mpr hv]

/-- The extended local interaction is positive at every parameter, including
both endpoints. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointParentInteraction_isPositive
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (γ : ℝ) :
    (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap.IsPositive :=
  (symmetricProjection_one_sub (Submodule.isSymmetricProjection_starProjection _)).isPositive

/-- The extended first-endpoint term is bounded above by the canonical
embedded first-endpoint term. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointParentInteraction_zero_le_parentInteractionES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap ≤
      parentInteractionES (mixedEndpointLeftTensor A₀ D₁) 2 := by
  have hle : (groundSpaceES (mixedEndpointLeftTensor A₀ D₁) 2).starProjection.toLinearMap ≤
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0)).range.starProjection.toLinearMap := by
    apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
      (Submodule.isSymmetricProjection_starProjection _) |>.mpr
    simpa only [Submodule.range_starProjection] using
      groundSpaceES_mixedEndpointLeftTensor_le_extendedSupport A₀ A₁
  simpa only [mixedEndpointParentInteraction, parentInteractionES,
    Submodule.starProjection_orthogonal', ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one] using sub_le_sub_left hle 1

/-- The canonical embedded endpoint interaction is at most the extended
interaction plus its two outer sector penalties. These penalties are supplied
by the neighboring extended terms on a ring.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem parentInteractionES_mixedEndpointLeftTensor_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    parentInteractionES (mixedEndpointLeftTensor A₀ D₁) 2 ≤
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap +
        (1 - mixedEndpointRowSector D₀ D₁ 0) +
        (1 - mixedEndpointColumnSector D₀ D₁ 1) := by
  let S := (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
    (bondInterpolationMatrix D₀ D₁ 0)).range
  have hP : S.starProjection.toLinearMap.IsSymmetricProjection :=
    Submodule.isSymmetricProjection_starProjection S
  have hupper := one_sub_mul_mul_le hP
    (mixedEndpointRowSector_isSymmetricProjection (D₀ := D₀) (D₁ := D₁) 0)
    (mixedEndpointColumnSector_isSymmetricProjection (D₀ := D₀) (D₁ := D₁) 1)
    (mixedEndpointRowSector_commute_columnSector (D₀ := D₀) (D₁ := D₁) 0 1)
    (mixedEndpointRowSector_commute_extendedSupport_starProjection A₀ A₁
      (bondInterpolationMatrix D₀ D₁ 0))
    (mixedEndpointColumnSector_commute_extendedSupport_starProjection A₀ A₁
      (bondInterpolationMatrix D₀ D₁ 0))
  simpa only [parentInteractionES, Submodule.starProjection_orthogonal',
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one,
    mixedEndpointLeftTensor_starProjection_eq_outerCorner A₀ A₁,
    mixedEndpointParentInteraction] using hupper

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
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  sub_le_sub_left (extendedSupport_starProjection_le_sector A₀ A₁ _
    (mixedEndpointColumnSector_isSymmetricProjection 0)
    (mixedEndpointColumnSector_zero_insertedTwoSiteMap A₀ A₁)) 1

/-- The second-row sector penalty is bounded by the extended endpoint
interaction because the extended support lies in that sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_one_sub_rowSector_one_le_parentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    1 - mixedEndpointRowSector D₀ D₁ 1 ≤
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  sub_le_sub_left (extendedSupport_starProjection_le_sector A₀ A₁ _
    (mixedEndpointRowSector_isSymmetricProjection 1)
    (mixedEndpointRowSector_one_insertedTwoSiteMap A₀ A₁)) 1

end MPOSymmetry
end MPSTensor
