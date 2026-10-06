/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointCornerSupport
import TNLean.MPS.ParentHamiltonian.Martingale.ReducingProjectionGap

/-!
# Reducing phase projections of the actual joint endpoint

The physical phase selectors are orthogonal projections. Their boundary
actions make the joint extended support invariant, hence reducing. Its
canonical first-endpoint projector is exactly its extended projector
multiplied by the two outer zero-phase projections.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

private theorem binaryDiagonal_isSymmetricProjection
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) :
    (Matrix.toEuclideanLin (Matrix.diagonal f)).IsSymmetricProjection := by
  constructor
  · ext v i
    simp only [Module.End.mul_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal]
    rcases hf i with h | h <;> simp [h]
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext i
    simp only [Pi.star_apply]
    rcases hf i with h | h <;> simp [h]

/-- A row-phase selector is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_isSymmetricProjection (site : Fin N) :
    (jointMixedRowSector d₀ d₁ D₀ D₁ site).IsSymmetricProjection :=
  binaryDiagonal_isSymmetricProjection _ fun σ => jointMixedRowWeight_eq_zero_or_one (σ site)

/-- A column-phase selector is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedColumnSector_isSymmetricProjection (site : Fin N) :
    (jointMixedColumnSector d₀ d₁ D₀ D₁ site).IsSymmetricProjection :=
  binaryDiagonal_isSymmetricProjection _ fun σ => jointMixedColumnWeight_eq_zero_or_one (σ site)

/-- Row and column selectors commute, also at different sites.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_commute_columnSector (i j : Fin N) :
    Commute (jointMixedRowSector d₀ d₁ D₀ D₁ i)
      (jointMixedColumnSector d₀ d₁ D₀ D₁ j) := by
  apply (commute_iff_eq _ _).mpr
  ext v σ
  simp only [Module.End.mul_apply, jointMixedRowSector_apply, jointMixedColumnSector_apply]
  exact mul_left_comm _ _ _

/-- The first row selector preserves the full joint extended support.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem range_blockInsertedBoundaryMap_jointMixed_invariant_rowSector
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (W : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2).range.map
      (jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)) ≤
        (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2).range := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
  rw [jointMixedRowSector_blockInsertedBoundaryMap]
  exact ⟨_, rfl⟩

/-- The last column selector preserves the full joint extended support.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem range_blockInsertedBoundaryMap_jointMixed_invariant_columnSector
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (W : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2).range.map
      (jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)) ≤
        (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2).range := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
  rw [jointMixedColumnSector_blockInsertedBoundaryMap]
  exact ⟨_, rfl⟩

/-- Every local row phase reduces the actual zero-parameter joint support.
The inner phase is fixed; the outer phase acts on the virtual boundary.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_commute_extendedSupport_starProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (site : Fin 2) :
    Commute (jointMixedRowSector d₀ d₁ D₀ D₁ site)
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap := by
  apply Submodule.commute_starProjection_of_invariant _ _
    (jointMixedRowSector_isSymmetricProjection site).isSymmetric
  fin_cases site
  · exact range_blockInsertedBoundaryMap_jointMixed_invariant_rowSector A₀ A₁ _
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
    rw [jointMixedRowSector_one_blockInsertedBoundaryMap]
    exact ⟨_, rfl⟩

/-- Every local column phase reduces the actual zero-parameter joint support.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedColumnSector_commute_extendedSupport_starProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (site : Fin 2) :
    Commute (jointMixedColumnSector d₀ d₁ D₀ D₁ site)
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap := by
  apply Submodule.commute_starProjection_of_invariant _ _
    (jointMixedColumnSector_isSymmetricProjection site).isSymmetric
  fin_cases site
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
    rw [jointMixedColumnSector_zero_blockInsertedBoundaryMap]
    exact ⟨_, rfl⟩
  · exact range_blockInsertedBoundaryMap_jointMixed_invariant_columnSector A₀ A₁ _

/-- Every local row phase reduces the actual endpoint interaction.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_commute_parentInteraction_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (site : Fin 2) :
    Commute (jointMixedRowSector d₀ d₁ D₀ D₁ site)
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  (Commute.one_right _).sub_right
    (jointMixedRowSector_commute_extendedSupport_starProjection A₀ A₁ site)

/-- Every local column phase reduces the actual endpoint interaction.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedColumnSector_commute_parentInteraction_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (site : Fin 2) :
    Commute (jointMixedColumnSector d₀ d₁ D₀ D₁ site)
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  (Commute.one_right _).sub_right
    (jointMixedColumnSector_commute_extendedSupport_starProjection A₀ A₁ site)

/-- The full joint canonical support projector is the product of the actual
extended projector and its two outer zero-phase selectors.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpointLeftTensor_starProjection_eq_outerCorner
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (groundSpaceES (toTensorFromBlocks (μ := fun _ => 1)
      (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2).starProjection.toLinearMap =
      jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2) *
        jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2) *
          (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap := by
  let S := (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range
  let R := jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
  let C := jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
  have hR := jointMixedRowSector_isSymmetricProjection (d₀ := d₀) (d₁ := d₁)
    (D₀ := D₀) (D₁ := D₁) (0 : Fin 2)
  have hC := jointMixedColumnSector_isSymmetricProjection (d₀ := d₀) (d₁ := d₁)
    (D₀ := D₀) (D₁ := D₁) (1 : Fin 2)
  have hRC := jointMixedRowSector_commute_columnSector (d₀ := d₀) (d₁ := d₁)
    (D₀ := D₀) (D₁ := D₁) (0 : Fin 2) 1
  have hRP := jointMixedRowSector_commute_extendedSupport_starProjection A₀ A₁ 0
  have hCP := jointMixedColumnSector_commute_extendedSupport_starProjection A₀ A₁ 1
  have hprod : (R * C * S.starProjection.toLinearMap).IsSymmetricProjection :=
    (hR.mul_of_commute hC hRC).mul_of_commute
      (Submodule.isSymmetricProjection_starProjection S) (hRP.mul_left hCP)
  symm
  apply hprod.ext (Submodule.isSymmetricProjection_starProjection _)
  rw [Submodule.range_starProjection,
    ← jointMixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES A₀ A₁]
  change LinearMap.range (R * C * S.starProjection.toLinearMap) = S.map (R.comp C)
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨S.starProjection v, S.starProjection_apply_mem v, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨v, ?_⟩
    change R (C (S.starProjection v)) = R (C v)
    rw [S.starProjection_eq_self_iff.mpr hv]

/-- The actual joint interaction is positive at every parameter.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpointParentInteraction_isPositive
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ) :
    (jointMixedEndpointParentInteraction A₀ A₁ γ).toLinearMap.IsPositive := by
  let S := (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) 2).range
  exact (show (1 - S.starProjection.toLinearMap).IsSymmetricProjection from
    ⟨(Submodule.isSymmetricProjection_starProjection S).isIdempotentElem.one_sub,
      LinearMap.IsSymmetric.id.sub
        (Submodule.isSymmetricProjection_starProjection S).isSymmetric⟩).isPositive

end MPSTensor.MPOSymmetry
