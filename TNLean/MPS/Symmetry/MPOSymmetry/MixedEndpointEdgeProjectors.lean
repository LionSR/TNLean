/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEdgeBoundaryTransport
import TNLean.MPS.ParentHamiltonian.Martingale.BoundedProjectionDeformation

/-!
# Canonical deformations of the actual active-edge constraints

The derived first- and last-edge support identities are transported to
Euclidean coefficient spaces. Their physical normalizations are explicit
linear equivalences, with the forward endpoint coordinate matrix as inverse.
Consequently the canonical deformed constraints are exactly the orthogonal
complement projections of the common one-sided core supports.

The orientation is important: if `F` sends the actual support to the core
support, then the deformation of the actual constraint uses `F.symm`,
because a canonical deformation pulls back its old kernel. The reverse
identification uses `F` and is included as well.

The interior constraint is the ordinary `A₀` two-site parent interaction.
There is no gap assumption or assertion of a global Hamiltonian equality.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix InnerProductSpace

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ : ℕ}

/-- The identity first-edge physical matrix gives the identity map.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem firstEdgePhysicalMap_one :
    firstEdgePhysicalMap (D₁ := D₁)
      (1 : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext x
  rcases x with ⟨p, q⟩
  change firstBoundaryCoordinateMap 1 (fun r => ψ (r, q)) p = ψ (p, q)
  simp only [firstBoundaryCoordinateMap_one, LinearMap.id_apply]

/-- The identity last-edge physical matrix gives the identity map.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem lastEdgePhysicalMap_one :
    lastEdgePhysicalMap (D₁ := D₁)
      (1 : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext x
  rcases x with ⟨q, p⟩
  change lastBoundaryCoordinateMap 1 (fun r => ψ (q, r)) p = ψ (q, p)
  simp only [lastBoundaryCoordinateMap_one, LinearMap.id_apply]

/-- First-edge physical maps compose by the local matrix product.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstEdgePhysicalMap_mul
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    firstEdgePhysicalMap (D₁ := D₁) (F * G) =
      (firstEdgePhysicalMap F).comp (firstEdgePhysicalMap G) := by
  apply LinearMap.ext
  intro ψ
  funext x
  rcases x with ⟨p, q⟩
  change firstBoundaryCoordinateMap (F * G) (fun r => ψ (r, q)) p =
    firstBoundaryCoordinateMap F (firstBoundaryCoordinateMap G (fun r => ψ (r, q))) p
  simp only [firstBoundaryCoordinateMap_mul, LinearMap.comp_apply]

/-- Last-edge physical maps compose by the local matrix product.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem lastEdgePhysicalMap_mul
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    lastEdgePhysicalMap (D₁ := D₁) (F * G) =
      (lastEdgePhysicalMap F).comp (lastEdgePhysicalMap G) := by
  apply LinearMap.ext
  intro ψ
  funext x
  rcases x with ⟨q, p⟩
  change lastBoundaryCoordinateMap (F * G) (fun r => ψ (q, r)) p =
    lastBoundaryCoordinateMap F (lastBoundaryCoordinateMap G (fun r => ψ (q, r))) p
  simp only [lastBoundaryCoordinateMap_mul, LinearMap.comp_apply]

/-- An explicit invertible first-edge physical change.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstEdgePhysicalEquiv
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) :
    (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) ≃ₗ[ℂ]
      (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) :=
  LinearEquiv.ofLinearMap (firstEdgePhysicalMap F) (firstEdgePhysicalMap G)
    (by rw [← firstEdgePhysicalMap_mul, hFG, firstEdgePhysicalMap_one])
    (by rw [← firstEdgePhysicalMap_mul, hGF, firstEdgePhysicalMap_one])

/-- An explicit invertible last-edge physical change.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastEdgePhysicalEquiv
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) :
    (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) ≃ₗ[ℂ]
      (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) :=
  LinearEquiv.ofLinearMap (lastEdgePhysicalMap F) (lastEdgePhysicalMap G)
    (by rw [← lastEdgePhysicalMap_mul, hFG, lastEdgePhysicalMap_one])
    (by rw [← lastEdgePhysicalMap_mul, hGF, lastEdgePhysicalMap_one])

/-- Normalize the first edge by the inverse endpoint physical matrix.
Its inverse is the forward endpoint physical matrix.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstEdgeNormalizationEquiv
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) ≃ₗ[ℂ]
      (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) :=
  let F := squarePhysicalCoordinates A₀
  have hdet : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_squarePhysicalCoordinates A₀ hA₀)
  firstEdgePhysicalEquiv F⁻¹ F (Matrix.nonsing_inv_mul _ hdet) (Matrix.mul_nonsing_inv _ hdet)

/-- Normalize the last edge, again with explicit inverse given by the
forward endpoint physical matrix.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastEdgeNormalizationEquiv
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) ≃ₗ[ℂ]
      (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) :=
  let F := squarePhysicalCoordinates A₀
  have hdet : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_squarePhysicalCoordinates A₀ hA₀)
  lastEdgePhysicalEquiv F⁻¹ F (Matrix.nonsing_inv_mul _ hdet) (Matrix.mul_nonsing_inv _ hdet)

/-- The actual first-edge normalization in Euclidean coefficient coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstEdgeNormalizationEquivES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) ≃ₗ[ℂ]
      EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :=
  let U := WithLp.linearEquiv 2 ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ)
  U.trans ((firstEdgeNormalizationEquiv A₀ hA₀).trans U.symm)

/-- The actual last-edge normalization in Euclidean coefficient coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastEdgeNormalizationEquivES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) ≃ₗ[ℂ]
      EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :=
  let U := WithLp.linearEquiv 2 ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ)
  U.trans ((lastEdgeNormalizationEquiv A₀ hA₀).trans U.symm)

/-- The actual first-edge support in Euclidean coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointFirstEdgeSupportES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Submodule ℂ (EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀)) :=
  (mixedEndpointFirstEdgeBoundaryMap A₀ A₁).range.map
    (WithLp.linearEquiv 2 ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ)).symm.toLinearMap

/-- The actual last-edge support in Euclidean coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointLastEdgeSupportES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Submodule ℂ (EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀)) :=
  (mixedEndpointLastEdgeBoundaryMap A₀ A₁).range.map
    (WithLp.linearEquiv 2 ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ)).symm.toLinearMap

/-- The first common-core edge support with arbitrary exterior spectators.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointFirstEdgeCoreSupportES (A₀ : MPSTensor (D₀ * D₀) D₀)
    (ι : Type*) [Fintype ι] :
    Submodule ℂ (EuclideanSpace ℂ (endpointFirstEdgeCfg ι D₀)) :=
  (endpointFirstEdgeCoreMap A₀ ι).range.map
    (WithLp.linearEquiv 2 ℂ (endpointFirstEdgeCfg ι D₀ → ℂ)).symm.toLinearMap

/-- The last common-core edge support with arbitrary exterior spectators.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointLastEdgeCoreSupportES (A₀ : MPSTensor (D₀ * D₀) D₀)
    (ι : Type*) [Fintype ι] :
    Submodule ℂ (EuclideanSpace ℂ (endpointLastEdgeCfg ι D₀)) :=
  (endpointLastEdgeCoreMap A₀ ι).range.map
    (WithLp.linearEquiv 2 ℂ (endpointLastEdgeCfg ι D₀ → ℂ)).symm.toLinearMap

private theorem map_conjugateEquiv_of_map_eq
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (U : E ≃ₗ[ℂ] F) (e : F ≃ₗ[ℂ] F) (S T : Submodule ℂ F)
    (h : S.map e.toLinearMap = T) :
    (S.map U.symm.toLinearMap).map (U.trans (e.trans U.symm)).toLinearMap =
      T.map U.symm.toLinearMap := by
  ext v
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e x, ?_, ?_⟩
    · rw [← h]
      exact ⟨x, hx, rfl⟩
    · simp
  · rintro ⟨y, hy, rfl⟩
    rw [← h] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨U.symm x, ⟨x, hx, rfl⟩, ?_⟩
    simp

/-- The first-edge Euclidean normalization carries the actual support
exactly onto the common-core support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_firstEdgeNormalizationEquivES_actualSupport
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (mixedEndpointFirstEdgeSupportES A₀ A₁).map
      (firstEdgeNormalizationEquivES (D₁ := D₁) A₀ hA₀).toLinearMap =
      endpointFirstEdgeCoreSupportES A₀ (Fin D₀ ⊕ Fin D₁) := by
  apply map_conjugateEquiv_of_map_eq
    (WithLp.linearEquiv 2 ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ))
    (firstEdgeNormalizationEquiv A₀ hA₀)
  exact map_range_firstEdgePhysicalMap_actual_eq_core A₀ A₁ hA₀

/-- The last-edge Euclidean normalization has the corresponding exact
support image. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_lastEdgeNormalizationEquivES_actualSupport
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (mixedEndpointLastEdgeSupportES A₀ A₁).map
      (lastEdgeNormalizationEquivES (D₁ := D₁) A₀ hA₀).toLinearMap =
      endpointLastEdgeCoreSupportES A₀ (Fin D₀ ⊕ Fin D₁) := by
  apply map_conjugateEquiv_of_map_eq
    (WithLp.linearEquiv 2 ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ))
    (lastEdgeNormalizationEquiv A₀ hA₀)
  exact map_range_lastEdgePhysicalMap_actual_eq_core A₀ A₁ hA₀

/-- The actual canonical first-edge constraint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointFirstEdgeConstraintES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :=
  (mixedEndpointFirstEdgeSupportES A₀ A₁)ᗮ.starProjection.toLinearMap

/-- The actual canonical last-edge constraint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointLastEdgeConstraintES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :=
  (mixedEndpointLastEdgeSupportES A₀ A₁)ᗮ.starProjection.toLinearMap

/-- The canonical first common-core constraint, including arbitrary
exterior spectators. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointFirstEdgeCoreConstraintES (A₀ : MPSTensor (D₀ * D₀) D₀)
    (ι : Type*) [Fintype ι] :
    EuclideanSpace ℂ (endpointFirstEdgeCfg ι D₀) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointFirstEdgeCfg ι D₀) :=
  (endpointFirstEdgeCoreSupportES A₀ ι)ᗮ.starProjection.toLinearMap

/-- The canonical last common-core constraint, including arbitrary
exterior spectators. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointLastEdgeCoreConstraintES (A₀ : MPSTensor (D₀ * D₀) D₀)
    (ι : Type*) [Fintype ι] :
    EuclideanSpace ℂ (endpointLastEdgeCfg ι D₀) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointLastEdgeCfg ι D₀) :=
  (endpointLastEdgeCoreSupportES A₀ ι)ᗮ.starProjection.toLinearMap


/-- The actual first-edge canonical constraint is a symmetric projection.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointFirstEdgeConstraintES_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (mixedEndpointFirstEdgeConstraintES A₀ A₁).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection _

/-- The actual last-edge canonical constraint is a symmetric projection.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointLastEdgeConstraintES_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (mixedEndpointLastEdgeConstraintES A₀ A₁).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection _

/-- The first-edge constraint's kernel is its derived cropped support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem ker_mixedEndpointFirstEdgeConstraintES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    LinearMap.ker (mixedEndpointFirstEdgeConstraintES A₀ A₁) =
      mixedEndpointFirstEdgeSupportES A₀ A₁ := by
  simp only [mixedEndpointFirstEdgeConstraintES, Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

/-- The last-edge constraint's kernel is its derived cropped support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem ker_mixedEndpointLastEdgeConstraintES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    LinearMap.ker (mixedEndpointLastEdgeConstraintES A₀ A₁) =
      mixedEndpointLastEdgeSupportES A₀ A₁ := by
  simp only [mixedEndpointLastEdgeConstraintES, Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

/-- Every first common-core constraint is a symmetric projection, including
its exterior spectators. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem endpointFirstEdgeCoreConstraintES_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (ι : Type*) [Fintype ι] :
    (endpointFirstEdgeCoreConstraintES A₀ ι).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection _

/-- Every last common-core constraint is a symmetric projection, including
its exterior spectators. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem endpointLastEdgeCoreConstraintES_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (ι : Type*) [Fintype ι] :
    (endpointLastEdgeCoreConstraintES A₀ ι).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection _

private theorem deformed_complementProjections_of_map_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (e : E ≃ₗ[ℂ] F) (S : Submodule ℂ E) (T : Submodule ℂ F)
    (h : S.map e.toLinearMap = T) :
    e.symm.deformedConstraintProjection Sᗮ.starProjection.toLinearMap =
        Tᗮ.starProjection.toLinearMap ∧
      e.deformedConstraintProjection Tᗮ.starProjection.toLinearMap =
        Sᗮ.starProjection.toLinearMap := by
  have hBackward : S.comap e.symm.toLinearMap = T := by
    rw [← h]
    ext v
    constructor
    · intro hv
      exact ⟨e.symm v, hv, e.apply_symm_apply v⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  have hForward : T.comap e.toLinearMap = S := by
    rw [← h]
    ext v
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwv : w = v := e.injective heq
      change w ∈ S at hw
      change v ∈ S
      exact hwv ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  constructor
  · simp only [LinearEquiv.deformedConstraintProjection, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal, hBackward]
  · simp only [LinearEquiv.deformedConstraintProjection, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal, hForward]

/-- Deforming the actual first-edge constraint by the inverse normalization
is exactly the common-core constraint. This orientation follows from the
pulled-back-kernel definition of canonical deformation.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstEdgeNormalization_symm_deformed_actualConstraint_eq_core
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (firstEdgeNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.deformedConstraintProjection
        (mixedEndpointFirstEdgeConstraintES A₀ A₁) =
      endpointFirstEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁) :=
  (deformed_complementProjections_of_map_eq _ _ _
    (map_firstEdgeNormalizationEquivES_actualSupport A₀ A₁ hA₀)).1

/-- The corresponding inverse-normalization identity for the last edge.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem lastEdgeNormalization_symm_deformed_actualConstraint_eq_core
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (lastEdgeNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.deformedConstraintProjection
        (mixedEndpointLastEdgeConstraintES A₀ A₁) =
      endpointLastEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁) :=
  (deformed_complementProjections_of_map_eq _ _ _
    (map_lastEdgeNormalizationEquivES_actualSupport A₀ A₁ hA₀)).1

/-- In the direction used to transfer a core gap back to the actual first
edge, the forward normalization canonically deforms the core constraint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstEdgeNormalization_deformed_coreConstraint_eq_actual
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (firstEdgeNormalizationEquivES (D₁ := D₁) A₀ hA₀).deformedConstraintProjection
        (endpointFirstEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)) =
      mixedEndpointFirstEdgeConstraintES A₀ A₁ :=
  (deformed_complementProjections_of_map_eq _ _ _
    (map_firstEdgeNormalizationEquivES_actualSupport A₀ A₁ hA₀)).2

/-- The forward-normalization counterpart for the last edge.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem lastEdgeNormalization_deformed_coreConstraint_eq_actual
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (lastEdgeNormalizationEquivES (D₁ := D₁) A₀ hA₀).deformedConstraintProjection
        (endpointLastEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)) =
      mixedEndpointLastEdgeConstraintES A₀ A₁ :=
  (deformed_complementProjections_of_map_eq _ _ _
    (map_lastEdgeNormalizationEquivES_actualSupport A₀ A₁ hA₀)).2

/-- The actual interior support in Euclidean coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointInteriorEdgeSupportES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg (D₀ * D₀) 2)) :=
  (mixedEndpointInteriorEdgeBoundaryMap A₀ A₁).range.map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace (D₀ * D₀) 2)).symm.toLinearMap

/-- The actual interior support is the ordinary two-site endpoint support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointInteriorEdgeSupportES_eq_groundSpaceES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    mixedEndpointInteriorEdgeSupportES A₀ A₁ = groundSpaceES A₀ 2 := by
  unfold mixedEndpointInteriorEdgeSupportES groundSpaceES
  rw [range_mixedEndpointInteriorEdgeBoundaryMap]

/-- The actual interior canonical constraint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointInteriorEdgeConstraintES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    EuclideanSpace ℂ (Cfg (D₀ * D₀) 2) →ₗ[ℂ] EuclideanSpace ℂ (Cfg (D₀ * D₀) 2) :=
  (mixedEndpointInteriorEdgeSupportES A₀ A₁)ᗮ.starProjection.toLinearMap

/-- The actual interior constraint is exactly the ordinary `A₀` parent
interaction, independently of injectivity and the second endpoint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointInteriorEdgeConstraintES_eq_parentInteractionES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    mixedEndpointInteriorEdgeConstraintES A₀ A₁ = parentInteractionES A₀ 2 := by
  exact congrArg
    (fun S : Submodule ℂ (EuclideanSpace ℂ (Cfg (D₀ * D₀) 2)) =>
      Sᗮ.starProjection.toLinearMap)
    (mixedEndpointInteriorEdgeSupportES_eq_groundSpaceES A₀ A₁)

end

end MPOSymmetry
end MPSTensor
