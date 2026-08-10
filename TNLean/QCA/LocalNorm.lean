/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.LocalLimit

/-!
# The operator norm on the algebraic local algebra

The operator norm of a local observable is the operator norm of any finite-region
representative. The identity-tensor inclusions preserve this norm, so the actual `DirectLimit`
quotient relation makes the definition independent of the representative.

For positive on-site dimension, this gives the algebraic local algebra its natural normed
star-algebra structure and the C-star identity. The algebraic local algebra is not asserted to be
complete, and no quasi-local C-star algebra or quantum cellular automaton is defined here.

## Main definitions

* `SpinChain.algebraicLocalOperatorNorm` — the representative operator norm.

## Main results

* `SpinChain.norm_localObservable` — the canonical inclusion of each finite region preserves norm.
* `SpinChain.localObservable_isometry` — every local observable inclusion is an isometry.
* `SpinChain.norm_star_mul_self` — the C-star identity before completion.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2285--2300.
-/

open scoped ComplexOrder

namespace SpinChain

-- These aliases keep finite-region norm synthesis within the project's pending-depth limit.
noncomputable local instance (d : ℕ) (Λ : Finset ℤ) : Norm (LocalAlgebra d Λ) :=
  CStarMatrix.instNorm

noncomputable local instance (d : ℕ) (Λ : Finset ℤ) :
    NormedAddCommGroup (LocalAlgebra d Λ) :=
  CStarMatrix.instNormedAddCommGroup

noncomputable local instance (d : ℕ) (Λ : Finset ℤ) : NormedRing (LocalAlgebra d Λ) :=
  CStarMatrix.instNormedRing

local instance (d : ℕ) (Λ : Finset ℤ) : CStarRing (LocalAlgebra d Λ) :=
  CStarMatrix.instCStarRing

/-- The operator norm of a local observable, defined from any finite-region representative.

Representative independence follows from `SpinChain.localInclusion_norm` and the defining
`DirectLimit` quotient relation: two representatives agree after inclusion into a common finite
region, where their operator norms agree.

Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
noncomputable def algebraicLocalOperatorNorm (d : ℕ) [NeZero d] :
    AlgebraicLocalAlgebra d → ℝ :=
  DirectLimit.lift (localAlgebraMap d) (fun _ A ↦ ‖A‖)
    (fun _ _ h A ↦ (localInclusion_norm h A).symm)

/-- The operator norm of a canonical finite-region representative is its matrix operator norm.

Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
@[simp]
lemma algebraicLocalOperatorNorm_localObservable (d : ℕ) [NeZero d]
    (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    algebraicLocalOperatorNorm d (localObservable d Λ A) = ‖A‖ :=
  rfl

noncomputable instance instNormAlgebraicLocalAlgebra (d : ℕ) [NeZero d] :
    Norm (AlgebraicLocalAlgebra d) where
  norm := algebraicLocalOperatorNorm d

/-- The canonical inclusion of a finite-region local algebra preserves the operator norm.

Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
@[simp]
lemma norm_localObservable (d : ℕ) [NeZero d] (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) :
    ‖localObservable d Λ A‖ = ‖A‖ :=
  rfl

private lemma algebraicLocalOperatorNorm_nonneg (d : ℕ) [NeZero d]
    (A : AlgebraicLocalAlgebra d) : 0 ≤ ‖A‖ := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      change 0 ≤ ‖A‖
      exact norm_nonneg A

private lemma algebraicLocalOperatorNorm_smul (d : ℕ) [NeZero d]
    (c : ℂ) (A : AlgebraicLocalAlgebra d) : ‖c • A‖ = ‖c‖ * ‖A‖ := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      change ‖c • A‖ = ‖c‖ * ‖A‖
      exact norm_smul c A

private lemma algebraicLocalOperatorNorm_add_le (d : ℕ) [NeZero d]
    (A B : AlgebraicLocalAlgebra d) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := by
  induction A, B using DirectLimit.induction₂ with
  | _ Λ A B =>
      rw [DirectLimit.add_def]
      change ‖A + B‖ ≤ ‖A‖ + ‖B‖
      exact norm_add_le A B

private lemma algebraicLocalOperatorNorm_eq_zero_iff (d : ℕ) [NeZero d]
    (A : AlgebraicLocalAlgebra d) : ‖A‖ = 0 ↔ A = 0 := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      change ‖A‖ = 0 ↔ localObservable d Λ A = 0
      rw [norm_eq_zero]
      constructor
      · rintro rfl
        exact map_zero (localObservable d Λ)
      · intro hA
        apply localObservable_injective d Λ
        simpa using hA

private theorem algebraicLocalNormedSpaceCore (d : ℕ) [NeZero d] :
    NormedSpace.Core ℂ (AlgebraicLocalAlgebra d) where
  norm_nonneg := algebraicLocalOperatorNorm_nonneg d
  norm_smul := algebraicLocalOperatorNorm_smul d
  norm_triangle := algebraicLocalOperatorNorm_add_le d
  norm_eq_zero_iff := algebraicLocalOperatorNorm_eq_zero_iff d

noncomputable instance instNormedAddCommGroupAlgebraicLocalAlgebra (d : ℕ) [NeZero d] :
    NormedAddCommGroup (AlgebraicLocalAlgebra d) :=
  NormedAddCommGroup.ofCore (algebraicLocalNormedSpaceCore d)

private lemma algebraicLocalOperatorNorm_mul_le (d : ℕ) [NeZero d]
    (A B : AlgebraicLocalAlgebra d) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  induction A, B using DirectLimit.induction₂ with
  | _ Λ A B =>
      rw [DirectLimit.mul_def]
      change ‖A * B‖ ≤ ‖A‖ * ‖B‖
      exact norm_mul_le A B

/-- The algebraic local algebra with its representative operator norm is a normed ring.

No completeness claim is made.
Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
noncomputable instance instNormedRingAlgebraicLocalAlgebra (d : ℕ) [NeZero d] :
    NormedRing (AlgebraicLocalAlgebra d) where
  dist_eq _ _ := rfl
  norm_mul_le := algebraicLocalOperatorNorm_mul_le d

/-- The algebraic local algebra with its representative operator norm is a normed complex
algebra.

No completeness claim is made.
Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
noncomputable instance instNormedAlgebraAlgebraicLocalAlgebra (d : ℕ) [NeZero d] :
    NormedAlgebra ℂ (AlgebraicLocalAlgebra d) where
  norm_smul_le c A := by
    induction A using DirectLimit.induction with
    | _ Λ A =>
        rw [DirectLimit.smul_def]
        change ‖c • A‖ ≤ ‖c‖ * ‖A‖
        exact (norm_smul c A).le

/-- The algebraic local algebra is a star ring. This explicit instance keeps synthesis within
the project's pending-depth limit. -/
noncomputable instance instStarRingAlgebraicLocalAlgebra (d : ℕ) :
    StarRing (AlgebraicLocalAlgebra d) where
  star_involutive A := by
    induction A using DirectLimit.induction with
    | _ Λ A => rw [DirectLimit.star_def, DirectLimit.star_def, star_star]
  star_mul A B := by
    induction A, B using DirectLimit.induction₂ with
    | _ Λ A B =>
        rw [DirectLimit.mul_def, DirectLimit.star_def, DirectLimit.star_def,
          DirectLimit.star_def, star_mul, DirectLimit.mul_def]
  star_add A B := by
    induction A, B using DirectLimit.induction₂ with
    | _ Λ A B =>
        rw [DirectLimit.add_def, DirectLimit.star_def, DirectLimit.star_def,
          DirectLimit.star_def, star_add, DirectLimit.add_def]

/-- The representative operator norm satisfies the C-star identity on the algebraic local
algebra, before completion.

Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
lemma norm_star_mul_self (d : ℕ) [NeZero d] (A : AlgebraicLocalAlgebra d) :
    ‖star A * A‖ = ‖A‖ * ‖A‖ := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      rw [DirectLimit.star_def, DirectLimit.mul_def]
      change ‖star A * A‖ = ‖A‖ * ‖A‖
      exact CStarRing.norm_star_mul_self

/-- The normed star ring underlying the algebraic local algebra satisfies the C-star axiom.
It need not be complete.

Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
instance instCStarRingAlgebraicLocalAlgebra (d : ℕ) [NeZero d] :
    CStarRing (AlgebraicLocalAlgebra d) where
  norm_mul_self_le A := (norm_star_mul_self d A).ge

/-- Every canonical map from a finite region into the local algebra is an operator-norm
isometry.

Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
lemma localObservable_isometry (d : ℕ) [NeZero d] (Λ : Finset ℤ) :
    Isometry (localObservable d Λ) := by
  rw [isometry_iff_dist_eq]
  intro A B
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(localObservable d Λ).toAlgHom.toRingHom A -
    (localObservable d Λ).toAlgHom.toRingHom B‖ = ‖A - B‖
  rw [← (localObservable d Λ).toAlgHom.toRingHom.map_sub]
  change ‖localObservable d Λ (A - B)‖ = ‖A - B‖
  exact norm_localObservable d Λ (A - B)

end SpinChain
