/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.Algebra.MatrixAux
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Irreducible.PeriodicBlocking
import TNLean.Channel.Semigroup.CPClosure

/-!
# Sector irreducibility: projection orthogonality and corner preservation

This file contains the general linear-algebra input for the
sector-irreducibility development. It proves pairwise orthogonality for
orthogonal projections summing to `1`, and it shows that an adjoint-fixed
orthogonal projection for a trace-preserving tensor yields an invariant corner
algebra.

## Main statements

* `pairwise_mul_zero_of_orthogonalProjection_sum_one` — orthogonal projections
  summing to `1` are pairwise orthogonal.
* `preservesCorner_of_adjoint_fixed_projection` — an adjoint-fixed orthogonal
  projection yields a preserved corner algebra.

## Tags

matrix product states, orthogonal projections, invariant corners
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

/-! ### Orthogonal-projection pairwise orthogonality -/

variable {D m : ℕ}

/-- If a finite family of orthogonal projections sums to the identity, then
distinct projections are orthogonal: `P i * P j = 0` for `i ≠ j`.

This is the `Pairwise` packaging of
`orthogonalProjection_mul_eq_zero_of_sum_eq_one` from
`TNLean/Channel/Irreducible/Basic.lean`. -/
theorem pairwise_mul_zero_of_orthogonalProjection_sum_one
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1) :
    Pairwise fun i j : Fin m => P i * P j = 0 := fun _ _ hij =>
  orthogonalProjection_mul_eq_zero_of_sum_eq_one P hPproj hPsum hij

/-! ### Corner preservation from adjoint fixed projections -/

variable {d : ℕ}

/-- If an orthogonal projection `P` is fixed by the adjoint transfer map
`T†(·) = ∑ᵢ Aᵢ† · Aᵢ` of a TP tensor, then `T†` preserves the corner
algebra `P · M_D(ℂ) · P`.

The proof derives `[P, Aᵢ] = 0` from
`MPSTensor.commutes_letters_of_adjoint_fixed_projection`, then threads the
idempotent relation `P² = P` through the corner sandwich. -/
theorem preservesCorner_of_adjoint_fixed_projection
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : MatrixAlg D}
    (hP : IsOrthogonalProjection P)
    (hFix : MPSTensor.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) P = P) :
    PreservesCorner P (MPSTensor.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) := by
  have hComm : ∀ i : Fin d, P * A i = A i * P :=
    MPSTensor.commutes_letters_of_adjoint_fixed_projection (A := A) hTP (hP := hP) hFix
  have hCommAdj : ∀ i : Fin d, P * (A i)ᴴ = (A i)ᴴ * P := by
    intro i
    have h := congrArg Matrix.conjTranspose (hComm i)
    simpa [Matrix.conjTranspose_mul, hP.1.eq] using h.symm
  intro X
  simp only [MPSTensor.transferMap_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_conjTranspose]
  refine Finset.sum_congr rfl ?_
  intro i _
  calc
    P * ((A i)ᴴ * (P * X * P) * A i) * P
        = (P * (A i)ᴴ) * (P * X * P) * (A i * P) := by
            simp only [Matrix.mul_assoc]
    _ = ((A i)ᴴ * P) * (P * X * P) * (P * A i) := by
          rw [hCommAdj i, ← hComm i]
    _ = (A i)ᴴ * ((P * P) * X * P) * (P * A i) := by
          simp only [Matrix.mul_assoc]
    _ = (A i)ᴴ * (P * X * P) * (P * A i) := by
          simp only [Matrix.mul_assoc, hP.2]
    _ = (A i)ᴴ * (P * X * P) * A i := by
          calc
            (A i)ᴴ * (P * X * P) * (P * A i)
                = (A i)ᴴ * ((P * X * P) * P) * A i := by
                    simp only [Matrix.mul_assoc]
            _ = (A i)ᴴ * (P * X * P) * A i := by
                    simp only [Matrix.mul_assoc, hP.2]
