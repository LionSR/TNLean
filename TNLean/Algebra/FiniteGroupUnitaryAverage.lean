/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Invariants
import QICLean.Algebra.OrthogonalProjection

/-!
# Finite-group averages of unitary representations

The normalized average of a finite-group unitary representation is the
orthogonal projection onto its invariant subspace. This is the matrix-level
averaging fact used for the local gauge constraints in arXiv:2502.20257,
lines 459--461 and Eq. `eq:projection`.
-/

open scoped BigOperators Matrix

namespace TNLean.Algebra

variable {G : Type*} {n : ℕ} [Group G] [Fintype G]

/-- The matrix representation on column vectors associated with a unitary
matrix representation. -/
noncomputable def unitaryMatrixRepresentation
    (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) :
    Representation ℂ G (Fin n → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Matrix.unitaryGroup (Fin n) ℂ).subtype.comp ρ)

/-- The normalized finite-group average
$|G|^{-1}\sum_{g \in G}\rho(g)$ of a unitary matrix representation.

This is the local gauge projector of arXiv:2502.20257, lines 459--461. -/
noncomputable def finiteGroupUnitaryAverage
    (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g : Matrix (Fin n) (Fin n) ℂ)

/-- The normalized average of a finite-group unitary matrix representation is
an orthogonal projection.

This is the single-site projection assertion underlying arXiv:2502.20257,
lines 459--461 and Eq. `eq:projection`. Idempotence is inherited from the
standard averaging projection onto representation invariants; self-adjointness
uses unitarity and reindexes the group sum by inversion. -/
theorem finiteGroupUnitaryAverage_isOrthogonalProjection
    (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) :
    IsOrthogonalProjection (finiteGroupUnitaryAverage ρ) := by
  classical
  let _ : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let σ := unitaryMatrixRepresentation ρ
  have havg :
      LinearMap.toMatrixAlgEquiv' σ.averageMap = finiteGroupUnitaryAverage ρ := by
    simp [σ, unitaryMatrixRepresentation, Representation.averageMap,
      GroupAlgebra.average, finiteGroupUnitaryAverage]
  apply IsStarProjection.isOrthogonalProjection
  rw [isStarProjection_iff']
  constructor
  · have hidem := (Representation.isProj_averageMap (ρ := σ)).isIdempotentElem.eq
    rw [← havg]
    simpa only [map_mul] using congr_arg LinearMap.toMatrixAlgEquiv' hidem
  · change (finiteGroupUnitaryAverage ρ)ᴴ = finiteGroupUnitaryAverage ρ
    simp only [finiteGroupUnitaryAverage, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sum]
    congr 1
    · simp
    · calc
        ∑ g : G, (ρ g : Matrix (Fin n) (Fin n) ℂ)ᴴ =
            ∑ g : G, (ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) := by
              apply Finset.sum_congr rfl
              intro g _
              simp [← Matrix.star_eq_conjTranspose]
        _ = ∑ g : G, (ρ g : Matrix (Fin n) (Fin n) ℂ) := by
          simpa using Equiv.sum_comp (Equiv.inv G)
            (fun g : G ↦ (ρ g : Matrix (Fin n) (Fin n) ℂ))

end TNLean.Algebra
