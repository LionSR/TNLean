/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal accessible charge subspaces

For a fixed character, take the span of all actual two-site charge vectors,
including every internal state and every pair of unknown vertex translations.
Distinct irreducible characters give orthogonal subspaces. Independent vertex
translations preserve each subspace, so its orthogonal detector is compatible
with the unknown translations.

Source: SCP10, arXiv:1001.3807, charge detection, lines 2470–2486.
These are auxiliary accessible-coordinate statements. No measurement on the
original physical spins is asserted here.
-/

open scoped BigOperators
noncomputable section
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G]

/-- The actual charge matrix regarded as a Hilbert-space vector.
Source: SCP10, charge detection, lines 2470–2486. -/
def regularChargeVector (χ : G → ℂ) (p x y : G) : EuclideanSpace ℂ (G × G) :=
  WithLp.toLp 2 fun rs => regularChargeMatrix χ p x y rs.1 rs.2

/-- The charge subspace includes every internal state and unknown vertex translation.
Source: SCP10, charge detection, lines 2470–2486. -/
def regularChargeSubspace (χ : G → ℂ) : Submodule ℂ (EuclideanSpace ℂ (G × G)) :=
  Submodule.span ℂ {v | ∃ p x y, v = regularChargeVector χ p x y}

omit [Fintype G] in
/-- Every actual charge vector belongs to the corresponding accessible charge subspace.
Source: SCP10, charge detection, lines 2470–2486. -/
theorem regularChargeVector_mem_subspace (χ : G → ℂ) (p x y : G) :
    regularChargeVector χ p x y ∈ regularChargeSubspace χ :=
  Submodule.subset_span ⟨p, x, y, rfl⟩

/-- Hilbert-space overlap is exactly the overlap of the actual charge matrices.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeVector_inner (χ ψ : G → ℂ) (p x y q x' y' : G) :
    inner ℂ (regularChargeVector χ p x y) (regularChargeVector ψ q x' y') =
      ∑ r, ∑ s, star (regularChargeMatrix χ p x y r s) *
        regularChargeMatrix ψ q x' y' r s := by
  simp only [PiLp.inner_apply, regularChargeVector, RCLike.inner_apply',
    Fintype.sum_prod_type]
  rfl

/-- Independent vertex translations permute the two accessible registers.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
def regularChargeTranslation (z w : G) :
    EuclideanSpace ℂ (G × G) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (G × G) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr (Equiv.mulLeft z) (Equiv.mulLeft w))

/-- The register permutation acts on the literal charge vectors by translating x and y.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
theorem regularChargeTranslation_vector (χ : G → ℂ) (p x y z w : G) :
    regularChargeTranslation z w (regularChargeVector χ p x y) =
      regularChargeVector χ p (z * x) (w * y) := by
  ext rs
  simp only [regularChargeTranslation, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, regularChargeVector, PiLp.toLp_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.mulLeft_symm]
  exact (regularChargeMatrix_translate_apply χ p x y z w rs.1 rs.2).symm

/-- Independent vertex translations preserve each accessible charge subspace.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
theorem regularChargeSubspace_map_translation (χ : G → ℂ) (z w : G) :
    (regularChargeSubspace χ).map (regularChargeTranslation z w).toLinearEquiv.toLinearMap =
      regularChargeSubspace χ := by
  change (Submodule.span ℂ {v | ∃ p x y, v = regularChargeVector χ p x y}).map _ = _
  rw [Submodule.map_span]
  unfold regularChargeSubspace
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨p, x, y, rfl⟩, rfl⟩
    exact ⟨p, z * x, w * y, regularChargeTranslation_vector χ p x y z w⟩
  · rintro ⟨p, x, y, rfl⟩
    refine ⟨regularChargeVector χ p (z⁻¹ * x) (w⁻¹ * y),
      ⟨p, z⁻¹ * x, w⁻¹ * y, rfl⟩, ?_⟩
    change regularChargeTranslation z w _ = _
    rw [regularChargeTranslation_vector]
    simp only [mul_inv_cancel_left]

/-- Orthogonal projection onto the full accessible subspace of a charge label.
Source: SCP10, charge detection, lines 2474–2486. -/
def regularChargeDetector (χ : G → ℂ) :
    EuclideanSpace ℂ (G × G) →L[ℂ] EuclideanSpace ℂ (G × G) :=
  (regularChargeSubspace χ).starProjection

/-- The charge detector is an orthogonal projection on the complete accessible space.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetector_isSymmetricProjection (χ : G → ℂ) :
    (regularChargeDetector χ).toLinearMap.IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection (regularChargeSubspace χ)

/-- Every actual vector with the selected charge label has detector eigenvalue one.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetector_vector (χ : G → ℂ) (p x y : G) :
    regularChargeDetector χ (regularChargeVector χ p x y) =
      regularChargeVector χ p x y :=
  Submodule.starProjection_eq_self_iff.mpr (regularChargeVector_mem_subspace χ p x y)

/-- The actual charge detector commutes with every independent vertex translation.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
theorem regularChargeDetector_commute_translation (χ : G → ℂ) (z w : G)
    (v : EuclideanSpace ℂ (G × G)) :
    regularChargeTranslation z w (regularChargeDetector χ v) =
      regularChargeDetector χ (regularChargeTranslation z w v) := by
  have h := (regularChargeTranslation z w).toLinearIsometry.map_starProjection
    (regularChargeSubspace χ) v
  change regularChargeTranslation z w ((regularChargeSubspace χ).starProjection v) =
    ((regularChargeSubspace χ).map
      (regularChargeTranslation z w).toLinearEquiv.toLinearMap).starProjection
        (regularChargeTranslation z w v) at h
  simpa only [regularChargeDetector, regularChargeSubspace_map_translation] using h

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Distinct irreducible charge labels give orthogonal accessible charge subspaces.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeSubspace_isOrtho
    (σ : Representation ℂ G E) (τ : Representation ℂ G F)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (hne : σ.character ≠ τ.character) :
    (regularChargeSubspace σ.character).IsOrtho
      (regularChargeSubspace τ.character) := by
  apply Submodule.isOrtho_span.mpr
  rintro _ ⟨p, x, y, rfl⟩ _ ⟨q, x', y', rfl⟩
  rw [regularChargeVector_inner]
  exact regularChargeMatrix_orthogonal σ τ hσ hne p x y q x' y'

/-- Every inequivalent irreducible charge has detector eigenvalue zero,
for every internal state and unknown vertex translation.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetector_other_vector
    (σ : Representation ℂ G E) (τ : Representation ℂ G F)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (hne : σ.character ≠ τ.character) (p x y : G) :
    regularChargeDetector σ.character (regularChargeVector τ.character p x y) = 0 := by
  change (regularChargeSubspace σ.character).starProjection _ = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact (regularChargeSubspace_isOrtho σ τ hσ hne).symm
    (regularChargeVector_mem_subspace τ.character p x y)

end TNLean.PEPS
