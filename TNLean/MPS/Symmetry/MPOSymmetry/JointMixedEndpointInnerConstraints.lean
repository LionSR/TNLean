/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointReducingSectors
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenSectors

/-!
# Inner phase constraints of the actual joint endpoint

The first column and second row of the actual zero-parameter support have
phase zero. Their product is therefore a single orthogonal constraint
whose complement is bounded by the actual interaction, with coefficient
one. Translating the already derived row and column commutators shows
that every physical phase selector reduces the actual open Hamiltonian.

The argument keeps the shared physical alphabets and all joint block
coefficients. No block orthogonality or positive dimension is assumed.
Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The two inner phase-zero conditions on one actual endpoint bond.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedTwoSiteInnerProjection (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) :=
  jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2) *
    jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2)

/-- The two inner phase constraints form an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedTwoSiteInnerProjection_isSymmetricProjection :
    (jointMixedTwoSiteInnerProjection d₀ d₁ D₀ D₁).IsSymmetricProjection :=
  (jointMixedColumnSector_isSymmetricProjection (0 : Fin 2)).mul_of_commute
    (jointMixedRowSector_isSymmetricProjection (1 : Fin 2))
    (jointMixedRowSector_commute_columnSector (1 : Fin 2) 0).symm

/-- The actual trace support satisfies both inner constraints simultaneously.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem range_blockInsertedBoundaryMap_jointMixed_le_innerProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range ≤
        LinearMap.range (jointMixedTwoSiteInnerProjection d₀ d₁ D₀ D₁) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
  refine ⟨blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2
      (blockBoundaryEquiv.symm X), ?_⟩
  change jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2)
    (jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2) _) = _
  rw [jointMixedRowSector_one_blockInsertedBoundaryMap,
    jointMixedColumnSector_zero_blockInsertedBoundaryMap]

/-- One local interaction controls the complement of the combined inner
constraint. This coefficient-one estimate follows from support inclusion.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedTwoSiteInnerProjection_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedTwoSiteInnerProjection d₀ d₁ D₀ D₁ ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply sub_le_sub_left
  apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
    jointMixedTwoSiteInnerProjection_isSymmetricProjection |>.mpr
  simpa only [Submodule.range_starProjection] using
    range_blockInsertedBoundaryMap_jointMixed_le_innerProjection A₀ A₁

/-- Every row-phase selector reduces every translate of the actual joint
interaction, including translates on which its site is a spectator.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_commute_periodicLocalInteraction_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (i k : Fin N) :
    Commute (jointMixedRowSector d₀ d₁ D₀ D₁ k)
      (periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) :=
  periodicLocalInteractionES_commute_siteDiagonal _ hN jointMixedRowWeight
    (jointMixedRowSector_commute_parentInteraction_zero A₀ A₁) i k

/-- Every column-phase selector reduces every translate of the actual
joint interaction. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedColumnSector_commute_periodicLocalInteraction_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (i k : Fin N) :
    Commute (jointMixedColumnSector d₀ d₁ D₀ D₁ k)
      (periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) :=
  periodicLocalInteractionES_commute_siteDiagonal _ hN jointMixedColumnWeight
    (jointMixedColumnSector_commute_parentInteraction_zero A₀ A₁) i k

/-- Every row-phase selector reduces the actual nonwrapping open sum.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_commute_openInteractionHamiltonian_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (k : Fin N) :
    Commute (jointMixedRowSector d₀ d₁ D₀ D₁ k)
      (openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  apply Commute.sum_right
  intro i _
  exact jointMixedRowSector_commute_periodicLocalInteraction_zero A₀ A₁ hN i.1 k

/-- Every column-phase selector reduces the actual nonwrapping open sum.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedColumnSector_commute_openInteractionHamiltonian_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (k : Fin N) :
    Commute (jointMixedColumnSector d₀ d₁ D₀ D₁ k)
      (openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  apply Commute.sum_right
  intro i _
  exact jointMixedColumnSector_commute_periodicLocalInteraction_zero A₀ A₁ hN i.1 k

end

end MPSTensor.MPOSymmetry
