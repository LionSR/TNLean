/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointEdgeNormalization
import TNLean.MPS.ParentHamiltonian.Martingale.BoundedProjectionDeformation

/-!
# Canonical projection constraints under joint boundary normalization

The inverse positive boundary factors define invertible changes in the
compressed Euclidean coordinates. The actual support identities give
both orientations of the resulting canonical projection deformation.
Orthogonal constraints are formed from the transported kernels; no
similarity-conjugation identity is used.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777. That passage
defines the degenerate-case path and asserts, without proof, that its
Hamiltonian stays well behaved along the whole path (line 1777). The
boundary columns, their polar factors and the compression below are not in
the source; they are this library's proof of that assertion.
-/

open scoped Matrix Kronecker ComplexOrder

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

private def matrixEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F G : Matrix ι ι ℂ) (hFG : F * G = 1) (hGF : G * F = 1) :
    (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
  LinearEquiv.ofLinearMap F.mulVecLin G.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, hFG]; ext v i; simp)
    (by rw [← Matrix.mulVecLin_mul, hGF]; ext v i; simp)

private theorem polarPos_inverse_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι κ ℂ) (hM : Function.Injective M.mulVec) :
    (Matrix.polarPos M)⁻¹ * Matrix.polarPos M = 1 ∧
      Matrix.polarPos M * (Matrix.polarPos M)⁻¹ = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.posDef_polarPos_of_injective M hM).isUnit
  exact ⟨Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet⟩

/-- The inverse joint first polar weight, with identity on the adjacent
physical site, as a linear equivalence of Euclidean coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgeNormalizationEquivES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    EuclideanSpace ℂ (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀) ≃ₗ[ℂ]
      EuclideanSpace ℂ (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀) := by
  let P := Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁)
  have hP := polarPos_inverse_pair _ (jointMixedFirstBoundaryColumns_injective A₀ A₁ h₀ h₁)
  let e := matrixEquiv (P⁻¹ ⊗ₖ (1 : Matrix (Fin d₀) (Fin d₀) ℂ)) (P ⊗ₖ 1)
    (by rw [← Matrix.mul_kronecker_mul, hP.1, Matrix.one_mul, Matrix.one_kronecker_one])
    (by rw [← Matrix.mul_kronecker_mul, hP.2, Matrix.one_mul, Matrix.one_kronecker_one])
  let U := WithLp.linearEquiv 2 ℂ (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀ → ℂ)
  exact U.trans (e.trans U.symm)

/-- The inverse joint last polar weight, with identity on the adjacent
physical site, as a linear equivalence of Euclidean coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgeNormalizationEquivES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    EuclideanSpace ℂ (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁) ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁) := by
  let P := Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁)
  have hP := polarPos_inverse_pair _ (jointMixedLastBoundaryColumns_injective A₀ A₁ h₀ h₁)
  let e := matrixEquiv ((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ P⁻¹) (1 ⊗ₖ P)
    (by rw [← Matrix.mul_kronecker_mul, hP.1, Matrix.one_mul, Matrix.one_kronecker_one])
    (by rw [← Matrix.mul_kronecker_mul, hP.2, Matrix.one_mul, Matrix.one_kronecker_one])
  let U := WithLp.linearEquiv 2 ℂ (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁ → ℂ)
  exact U.trans (e.trans U.symm)

/-- The actual compressed first-edge support in its Euclidean space.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgeCompressedSupportES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Submodule ℂ (EuclideanSpace ℂ (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀)) :=
  (jointMixedFirstEdgeCompressedMap A₀ A₁).range.map
    (WithLp.linearEquiv 2 ℂ (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀ → ℂ)).symm.toLinearMap

/-- The actual compressed last-edge support in its Euclidean space.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgeCompressedSupportES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁)) :=
  (jointMixedLastEdgeCompressedMap A₀ A₁).range.map
    (WithLp.linearEquiv 2 ℂ (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁ → ℂ)).symm.toLinearMap

/-- The common first-edge core support for arbitrary exterior dimensions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointEndpointFirstEdgeCoreSupportES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x)) (E : Fin r → ℕ) :
    Submodule ℂ (EuclideanSpace ℂ
      (((x : Fin r) × (Fin (E x) × Fin (D₀ x))) × Fin d₀)) :=
  (jointEndpointFirstEdgeCoreMap A₀ E).range.map
    (WithLp.linearEquiv 2 ℂ
      (((x : Fin r) × (Fin (E x) × Fin (D₀ x))) × Fin d₀ → ℂ)).symm.toLinearMap

/-- The reflected common core support for arbitrary exterior dimensions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointEndpointLastEdgeCoreSupportES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x)) (E : Fin r → ℕ) :
    Submodule ℂ (EuclideanSpace ℂ
      (Fin d₀ × ((x : Fin r) × (Fin (D₀ x) × Fin (E x))))) :=
  (jointEndpointLastEdgeCoreMap A₀ E).range.map
    (WithLp.linearEquiv 2 ℂ
      (Fin d₀ × ((x : Fin r) × (Fin (D₀ x) × Fin (E x))) → ℂ)).symm.toLinearMap

private theorem map_conjugateEquiv_of_map_eq
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (U : E ≃ₗ[ℂ] F) (e : F ≃ₗ[ℂ] F) (S T : Submodule ℂ F)
    (h : S.map e.toLinearMap = T) :
    (S.map U.symm.toLinearMap).map (U.trans (e.trans U.symm)).toLinearMap =
      T.map U.symm.toLinearMap := by
  rw [← Submodule.map_comp]
  have heq : (U.trans (e.trans U.symm)).toLinearMap.comp U.symm.toLinearMap =
      U.symm.toLinearMap.comp e.toLinearMap := by ext; simp
  rw [heq, Submodule.map_comp, h]

/-- The Euclidean first-boundary normalization carries the compressed
actual support exactly onto the unchanged-tensor core support.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedFirstEdgeNormalization_support
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedFirstEdgeCompressedSupportES A₀ A₁).map
        (jointMixedFirstEdgeNormalizationEquivES A₀ A₁ h₀ h₁).toLinearMap =
      jointEndpointFirstEdgeCoreSupportES A₀ (fun x => D₀ x + D₁ x) := by
  apply map_conjugateEquiv_of_map_eq
  exact map_jointMixedFirstEdgeCompressed_range_eq_core A₀ A₁ h₀ h₁

/-- The Euclidean last-boundary normalization has the reflected exact
support image. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedLastEdgeNormalization_support
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedLastEdgeCompressedSupportES A₀ A₁).map
        (jointMixedLastEdgeNormalizationEquivES A₀ A₁ h₀ h₁).toLinearMap =
      jointEndpointLastEdgeCoreSupportES A₀ (fun x => D₀ x + D₁ x) := by
  apply map_conjugateEquiv_of_map_eq
  exact map_jointMixedLastEdgeCompressed_range_eq_core A₀ A₁ h₀ h₁

private theorem deformed_complementProjections_of_map_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (e : E ≃ₗ[ℂ] F) (S : Submodule ℂ E) (T : Submodule ℂ F)
    (h : S.map e.toLinearMap = T) :
    e.symm.deformedConstraintProjection Sᗮ.starProjection.toLinearMap =
        Tᗮ.starProjection.toLinearMap ∧
      e.deformedConstraintProjection Tᗮ.starProjection.toLinearMap =
        Sᗮ.starProjection.toLinearMap := by
  constructor
  · simp only [LinearEquiv.deformedConstraintProjection, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.symm_symm, h]
  · have hsymm := (Submodule.map_symm_eq_iff e).mpr h
    simp only [LinearEquiv.deformedConstraintProjection, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal, Submodule.comap_equiv_eq_map_symm, hsymm]

/-- Both orientations of the actual first-edge canonical deformation.
Normalizing the support deforms its old constraint by the inverse map.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdgeNormalization_deformed_constraints
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    let e := jointMixedFirstEdgeNormalizationEquivES A₀ A₁ h₀ h₁
    let S := jointMixedFirstEdgeCompressedSupportES A₀ A₁
    let T := jointEndpointFirstEdgeCoreSupportES A₀ (fun x => D₀ x + D₁ x)
    e.symm.deformedConstraintProjection Sᗮ.starProjection.toLinearMap =
        Tᗮ.starProjection.toLinearMap ∧
      e.deformedConstraintProjection Tᗮ.starProjection.toLinearMap =
        Sᗮ.starProjection.toLinearMap :=
  deformed_complementProjections_of_map_eq _ _ _
    (map_jointMixedFirstEdgeNormalization_support A₀ A₁ h₀ h₁)

/-- Both orientations of the reflected last-edge canonical deformation.
These are orthogonal projections determined by kernels, without a
similarity-conjugation assertion.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdgeNormalization_deformed_constraints
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    let e := jointMixedLastEdgeNormalizationEquivES A₀ A₁ h₀ h₁
    let S := jointMixedLastEdgeCompressedSupportES A₀ A₁
    let T := jointEndpointLastEdgeCoreSupportES A₀ (fun x => D₀ x + D₁ x)
    e.symm.deformedConstraintProjection Sᗮ.starProjection.toLinearMap =
        Tᗮ.starProjection.toLinearMap ∧
      e.deformedConstraintProjection Tᗮ.starProjection.toLinearMap =
        Sᗮ.starProjection.toLinearMap :=
  deformed_complementProjections_of_map_eq _ _ _
    (map_jointMixedLastEdgeNormalization_support A₀ A₁ h₀ h₁)

end

end MPSTensor.MPOSymmetry
