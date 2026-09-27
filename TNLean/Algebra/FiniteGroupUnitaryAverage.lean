/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Invariants
import QICLean.Algebra.OrthogonalProjection

/-!
# Finite-group averages of unitary representations

The normalized average `|G|⁻¹ ∑_g ρ(g)` of a unitary representation
`ρ : G →* Matrix.unitaryGroup ι ℂ` of a finite group is the orthogonal
projection onto its invariant subspace. It is the matrix of Mathlib's
`Representation.averageMap` of the associated linear representation. This is
the matrix-level averaging fact used for the local gauge constraints in
arXiv:2502.20257, lines 457--461.
-/

open scoped BigOperators Matrix

namespace TNLean.Algebra

variable {G ι : Type*} {n : ℕ} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- The normalized average `|G|⁻¹ ∑_g ρ(g)` of a finite-group unitary matrix
representation is a star projection. This is the type-generic matrix form of
the local gauge projection in arXiv:2502.20257, lines 457--461: idempotence is
Mathlib's `Representation.isProj_averageMap`, and self-adjointness holds
because `ρ(g)ᴴ = ρ(g⁻¹)`. -/
theorem isStarProjection_inv_card_smul_sum
    (ρ : G →* Matrix.unitaryGroup ι ℂ) :
    IsStarProjection ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g : Matrix ι ι ℂ)) := by
  classical
  let _ : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let σ : Representation ℂ G (ι → ℂ) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Matrix.unitaryGroup ι ℂ).subtype.comp ρ)
  have havg : LinearMap.toMatrixAlgEquiv' σ.averageMap =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g : Matrix ι ι ℂ) := by
    simp [σ, Representation.averageMap, GroupAlgebra.average]
  rw [isStarProjection_iff']
  constructor
  · have hidem := (Representation.isProj_averageMap (ρ := σ)).isIdempotentElem.eq
    rw [← havg]
    simpa only [map_mul] using congr_arg LinearMap.toMatrixAlgEquiv' hidem
  · change ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g : Matrix ι ι ℂ))ᴴ =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g : Matrix ι ι ℂ)
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
    congr 1
    · simp only [star_inv₀, star_natCast]
    · calc
        ∑ g : G, (ρ g : Matrix ι ι ℂ)ᴴ =
            ∑ g : G, (ρ g⁻¹ : Matrix ι ι ℂ) := by
              apply Finset.sum_congr rfl
              intro g _
              simp [← Matrix.star_eq_conjTranspose]
        _ = ∑ g : G, (ρ g : Matrix ι ι ℂ) := by
          simpa using Equiv.sum_comp (Equiv.inv G)
            (fun g : G ↦ (ρ g : Matrix ι ι ℂ))

/-- The normalized average `|G|⁻¹ ∑_g ρ(g)` of a finite-group unitary matrix
representation on `Fin n` is an orthogonal projection, as asserted for the
local gauge operators in arXiv:2502.20257, lines 457--461. -/
theorem isOrthogonalProjection_inv_card_smul_sum
    (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) :
    IsOrthogonalProjection ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g : Matrix (Fin n) (Fin n) ℂ)) :=
  (isStarProjection_inv_card_smul_sum ρ).isOrthogonalProjection

end TNLean.Algebra
