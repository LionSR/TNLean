/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Matrix of the canonical parent interaction

The canonical interaction is the orthogonal projection onto the complement
of the local MPS boundary space. Its matrix in the configuration basis is
positive semidefinite and represents the same operator in the Euclidean
realization. This common choice is used when constructing positive parent
interactions and when evaluating their local commutators.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma existenceinteraction,
lines 2195--2230; PGVWC07, arXiv:quant-ph/0608197, Theorem 12.
-/

open scoped ComplexOrder
namespace MPSTensor
variable {d D : ℕ}

/-- The configuration-basis matrix of the canonical parent projection.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma existenceinteraction,
lines 2195--2230. -/
noncomputable def canonicalParentInteractionMatrix (A : MPSTensor d D) (R : ℕ) :
    Matrix (Cfg d R) (Cfg d R) ℂ :=
  (Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
    (groundSpaceES A R)ᗮ.starProjection

/-- The canonical interaction matrix represents the canonical parent operator.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma existenceinteraction,
lines 2195--2230. -/
theorem toEuclideanLin_canonicalParentInteractionMatrix (A : MPSTensor d D) (R : ℕ) :
    Matrix.toEuclideanLin (canonicalParentInteractionMatrix A R) = parentInteractionES A R := by
  change (Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)
    (canonicalParentInteractionMatrix A R)).toLinearMap = _
  rw [canonicalParentInteractionMatrix, StarAlgEquiv.apply_symm_apply]
  rfl

/-- The canonical interaction matrix is positive semidefinite.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma existenceinteraction,
lines 2195--2230. -/
theorem canonicalParentInteractionMatrix_posSemidef (A : MPSTensor d D) (R : ℕ) :
    (canonicalParentInteractionMatrix A R).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  rw [toEuclideanLin_canonicalParentInteractionMatrix]
  exact parentInteractionES_isPositive A R
end MPSTensor
