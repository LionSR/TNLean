/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SupportedParentProjection

/-!
# Parent compression to a reducing coordinate space

If an isometry's range projection reduces a parent interaction, its
compression is the orthogonal projection with kernel equal to the
adjoint image of the original support. The original support may have
components outside the isometric range.

This supplies the physical phase restriction in GLM23,
arXiv:2203.12563v3, Section 5, lines 1695–1777.
-/

namespace LinearIsometry

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

/-- Restriction to a reducing isometric range preserves an orthogonal
projection, without containing its entire range. -/
theorem isSymmetricProjection_compression_of_commute
    (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F) (hH : H.IsSymmetricProjection)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint) H) :
    (U.compression H).IsSymmetricProjection := by
  constructor
  · rw [isIdempotentElem_iff]
    ext v
    apply U.injective
    change U (U.compression H (U.compression H v)) = U (U.compression H v)
    rw [U.apply_compression_of_commute H hComm,
      U.apply_compression_of_commute H hComm,
      U.apply_compression_of_commute H hComm]
    exact LinearMap.congr_fun hH.isIdempotentElem.eq (U v)
  · exact hH.isSymmetric.adjoint_conj U.toLinearMap

/-- The compressed parent kernel is the adjoint image of the support
when the coordinate range reduces the parent interaction. -/
theorem ker_compression_one_sub_starProjection_of_commute
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint)
      (1 - S.starProjection.toLinearMap)) :
    LinearMap.ker (U.compression (1 - S.starProjection.toLinearMap)) =
      S.map U.toLinearMap.adjoint := by
  rw [U.ker_compression_eq_map_adjoint_of_commute _ hComm]
  congr 1
  rw [← ContinuousLinearMap.toLinearMap_one, ← ContinuousLinearMap.toLinearMap_sub,
    ← Submodule.starProjection_orthogonal', Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

/-- Compression of a reducing parent interaction is the canonical
orthogonal-complement projection of the derived compressed support. -/
theorem compression_one_sub_starProjection_of_commute
    (U : E →ₗᵢ[ℂ] F) (S : Submodule ℂ F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint)
      (1 - S.starProjection.toLinearMap)) :
    U.compression (1 - S.starProjection.toLinearMap) =
      1 - (S.map U.toLinearMap.adjoint).starProjection.toLinearMap := by
  have hS := Submodule.isSymmetricProjection_starProjection S
  have hH : (1 - S.starProjection.toLinearMap).IsSymmetricProjection :=
    ⟨hS.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hS.isSymmetric⟩
  have hK := U.isSymmetricProjection_compression_of_commute _ hH hComm
  have hrange : LinearMap.range (U.compression (1 - S.starProjection.toLinearMap)) =
      (S.map U.toLinearMap.adjoint)ᗮ := by
    rw [← U.ker_compression_one_sub_starProjection_of_commute S hComm,
      ← hK.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  obtain ⟨_, h⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hK
  simpa only [hrange, Submodule.starProjection_orthogonal',
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one] using h

/-- Two successive rectangular compressions equal compression by their
composite isometry. -/
theorem compression_comp (V : F →ₗᵢ[ℂ] G) (U : E →ₗᵢ[ℂ] F) (H : G →ₗ[ℂ] G) :
    (V.comp U).compression H = U.compression (V.compression H) := by
  simp only [compression, LinearIsometry.comp, LinearMap.adjoint_comp,
    LinearMap.comp_assoc]

end LinearIsometry
