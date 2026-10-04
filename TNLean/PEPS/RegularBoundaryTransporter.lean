/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryState

/-!
# Closure intertwiners on the invariant regular boundary

A weighted sum of simultaneous group translations acts on the invariant boundary
space by the sum of its weights. In particular, a sum restricted to the
intertwiners of two closure assignments becomes a scalar on that space.

This is the boundary restriction of the actual twisted-region Gram operator in
Schuch, Cirac, and Pérez-García, arXiv:1001.3807, proof of Theorem 6.9,
`Papers/1001.3807/paper_v3.tex`, lines 1935–1990 and 2043–2072. The identities
below concern the regular boundary representation; the derivation of its
weights from the contracted region is separate.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable local instance : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- A weighted sum of simultaneous translations of all regular boundary labels.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990. -/
noncomputable def regularBoundaryWeightedTranslation (b : ℕ) (w : G → ℂ) :
    Matrix (Fin b → G) (Fin b → G) ℂ :=
  ∑ g : G, w g • LinearMap.toMatrix' (regularBoundaryRepresentation (G := G) b g)

/-- A simultaneous translation fixes the invariant-boundary projector on its range. -/
theorem toMatrix_regularBoundaryRepresentation_mul_projector (b : ℕ) (g : G) :
    LinearMap.toMatrix' (regularBoundaryRepresentation (G := G) b g) *
      regularBoundaryProjector b = regularBoundaryProjector b := by
  have h : (regularBoundaryRepresentation (G := G) b g) ∘ₗ
      (regularBoundaryRepresentation (G := G) b).averageMap =
        (regularBoundaryRepresentation (G := G) b).averageMap := by
    apply LinearMap.ext
    intro x
    exact (regularBoundaryRepresentation (G := G) b).averageMap_invariant x g
  simpa only [regularBoundaryProjector, LinearMap.toMatrix'_comp] using
    congrArg LinearMap.toMatrix' h

/-- Source: SCP10, proof of Theorem 6.9, lines 1935–1990. The weighted
translation matrix is the corresponding sum of group-basis delta kernels. -/
theorem regularBoundaryWeightedTranslation_apply (b : ℕ) (w : G → ℂ)
    (x y : Fin b → G) :
    regularBoundaryWeightedTranslation b w x y =
      ∑ g : G, if x = g • y then w g else 0 := by
  simp only [regularBoundaryWeightedTranslation, Matrix.sum_apply, Matrix.smul_apply,
    LinearMap.toMatrix'_apply, regularBoundaryRepresentation_apply, Pi.single_apply,
    smul_eq_mul]
  simp only [inv_smul_eq_iff, mul_ite, mul_one, mul_zero]

/-- Source: SCP10, proof of Theorem 6.9, lines 1935–1990. On the invariant
boundary, the weighted translation sum is the sum of its weights times the projector. -/
theorem regularBoundaryWeightedTranslation_mul_projector (b : ℕ) (w : G → ℂ) :
    regularBoundaryWeightedTranslation b w * regularBoundaryProjector b =
      (∑ g : G, w g) • regularBoundaryProjector b := by
  simp only [regularBoundaryWeightedTranslation, Matrix.sum_mul, Matrix.smul_mul,
    toMatrix_regularBoundaryRepresentation_mul_projector]
  rw [Finset.sum_smul]

/-- Source: SCP10, proof of Theorem 6.9, lines 1935–1990. Restricting a
weighted translation operator on both sides to the invariant boundary gives
one scalar, the total weight. -/
theorem regularBoundaryProjector_mul_weightedTranslation_mul_projector
    (b : ℕ) (w : G → ℂ) :
    regularBoundaryProjector b * regularBoundaryWeightedTranslation b w *
      regularBoundaryProjector b = (∑ g : G, w g) • regularBoundaryProjector b := by
  simp only [Matrix.mul_assoc, regularBoundaryWeightedTranslation_mul_projector,
    Matrix.mul_smul, regularBoundaryProjector_mul_self]

end TNLean.PEPS
