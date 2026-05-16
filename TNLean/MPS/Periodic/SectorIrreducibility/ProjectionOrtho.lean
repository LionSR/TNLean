/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors
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

This is a standard fact about orthogonal decompositions of the identity. The
proof sandwiches the sum between `P i` to isolate the diagonal, then extracts
each off-diagonal term via positivity (`B B* = 0 → B = 0`). -/
theorem pairwise_mul_zero_of_orthogonalProjection_sum_one
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1) :
    Pairwise fun i j : Fin m => P i * P j = 0 := by
  intro i j hij
  have hsum_i : ∑ k : Fin m, P i * P k * P i = P i := by
    calc
      ∑ k : Fin m, P i * P k * P i
          = P i * (∑ k : Fin m, P k) * P i := by
              simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
      _ = P i * 1 * P i := by rw [hPsum]
      _ = P i := by simp [(hPproj i).2]
  have hsum_erase : ∑ k ∈ Finset.univ.erase i, P i * P k * P i = 0 := by
    rw [← Finset.sum_erase_add Finset.univ (fun k => P i * P k * P i) (Finset.mem_univ i)] at hsum_i
    have hiii : P i * P i * P i = P i := by
      simp [(hPproj i).2]
    rw [hiii] at hsum_i
    simpa using hsum_i
  let B : Fin m → MatrixAlg D := fun k => if k = i then 0 else P i * P k
  have hsum_B : ∑ k : Fin m, B k * (B k)ᴴ = 0 := by
    classical
    rw [← Finset.sum_erase_add Finset.univ (fun k => B k * (B k)ᴴ) (Finset.mem_univ i)]
    have hzero_i : B i * (B i)ᴴ = 0 := by simp [B]
    rw [hzero_i, add_zero]
    calc
      ∑ k ∈ Finset.univ.erase i, B k * (B k)ᴴ
          = ∑ k ∈ Finset.univ.erase i, P i * P k * P i := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hki : k ≠ i := by
                exact Finset.mem_erase.mp hk |>.1
              calc
                B k * (B k)ᴴ = (P i * P k) * ((P i * P k)ᴴ) := by
                  simp [B, hki]
                _ = P i * P k * P i := by
                  calc
                    (P i * P k) * ((P i * P k)ᴴ)
                        = P i * (P k * (P k * P i)) := by
                            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, (hPproj i).1.eq,
                              (hPproj k).1.eq]
                    _ = P i * ((P k * P k) * P i) := by simp [Matrix.mul_assoc]
                    _ = P i * (P k * P i) := by rw [(hPproj k).2]
                    _ = P i * P k * P i := by simp [Matrix.mul_assoc]
      _ = 0 := hsum_erase
  have hB_zero := eq_zero_of_sum_mul_conjTranspose_eq_zero B hsum_B
  have hPiPj : P i * P j = 0 := by
    by_cases hji : j = i
    · exact False.elim (hij hji.symm)
    · simpa [B, hji] using hB_zero j
  exact hPiPj

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

