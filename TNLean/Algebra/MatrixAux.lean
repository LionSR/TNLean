/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Auxiliary matrix lemmas

General-purpose matrix lemmas that are not specific to any chapter's theory.
Extracted from various files for reusability.

## Main results

- `Matrix.trace_conjTranspose_mul_self_re_eq_sum_norm_sq`: entrywise Hilbert--Schmidt
  trace identity
- `Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq`: the Hilbert--Schmidt
  trace form of the Frobenius norm
- `Matrix.eq_zero_of_sum_mul_conjTranspose_eq_zero`: a positive sum of squares
  vanishes only if every summand vanishes
- `Matrix.eq_zero_of_sum_conjTranspose_mul_self_eq_zero`: the conjugate-transpose
  variant
- `Matrix.PosSemidef.mulVec_eq_zero_left/right`: kernel containment for PSD matrix sums
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Frobenius

namespace Matrix

section FrobeniusTrace

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Entrywise form of the Hilbert--Schmidt trace identity. -/
theorem trace_conjTranspose_mul_self_re_eq_sum_norm_sq
    (A : Matrix m n ℂ) :
    (trace (Aᴴ * A)).re = ∑ j : n, ∑ i : m, ‖A i j‖ ^ 2 := by
  have hstar_mul_re : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [show star z = starRingEnd ℂ z from rfl, Complex.conj_mul',
      ← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa only [RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add] using hstar_mul_re (A i j)

/-- The real trace of `Aᴴ * A` is the square of the Frobenius norm. -/
theorem trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq
    (A : Matrix m n ℂ) :
    (trace (Aᴴ * A)).re = ‖A‖ ^ 2 := by
  rw [trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · calc
      ∑ j : n, ∑ i : m, ‖A i j‖ ^ 2 =
          ∑ j : n, ∑ i : m, ‖A i j‖ ^ (2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro i _
            exact (Real.rpow_natCast (‖A i j‖) 2).symm
      _ = ∑ i : m, ∑ j : n, ‖A i j‖ ^ (2 : ℝ) := by
            rw [Finset.sum_comm]
  · positivity

end FrobeniusTrace

section SumSquaresZero

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- If `∑ᵢ Bᵢ * Bᵢ† = 0`, then every `Bᵢ` is zero. -/
theorem eq_zero_of_sum_mul_conjTranspose_eq_zero
    (B : ι → Matrix n n ℂ)
    (h : ∑ i : ι, B i * (B i)ᴴ = 0) :
    ∀ i, B i = 0 := by
  intro i
  have htrace_nonneg :
      ∀ j : ι, 0 ≤ ((B j * (B j)ᴴ).trace).re :=
    fun j =>
      (Complex.le_def.mp (Matrix.posSemidef_self_mul_conjTranspose (B j)).trace_nonneg).1
  have htrace_sum :
      ∑ j : ι, ((B j * (B j)ᴴ).trace).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, h]
    simp
  have htrace_re : ((B i * (B i)ᴴ).trace).re = 0 :=
    congrFun (Fintype.sum_eq_zero_iff_of_nonneg (fun j => htrace_nonneg j) |>.mp
      htrace_sum) i
  have htrace_zero : (B i * (B i)ᴴ).trace = 0 :=
    Complex.ext htrace_re
      (Complex.le_def.mp (Matrix.posSemidef_self_mul_conjTranspose (B i)).trace_nonneg).2.symm
  have hmul_zero : B i * (B i)ᴴ = 0 :=
    (Matrix.posSemidef_self_mul_conjTranspose (B i)).trace_eq_zero_iff.mp htrace_zero
  exact Matrix.self_mul_conjTranspose_eq_zero.mp hmul_zero

/-- If `∑ᵢ Bᵢ† * Bᵢ = 0`, then every `Bᵢ` is zero. -/
theorem eq_zero_of_sum_conjTranspose_mul_self_eq_zero
    (B : ι → Matrix n n ℂ)
    (h : ∑ i : ι, (B i)ᴴ * B i = 0) :
    ∀ i, B i = 0 := by
  have hstar :
      ∀ i, (B i)ᴴ = 0 :=
    eq_zero_of_sum_mul_conjTranspose_eq_zero (fun i => (B i)ᴴ) (by
      simpa only [Matrix.conjTranspose_conjTranspose] using h)
  intro i
  exact Matrix.conjTranspose_eq_zero.mp (hstar i)

end SumSquaresZero

end Matrix

/-! ## Kernel intersection for PSD matrices -/

section KernelPSD

open Matrix

variable {D : ℕ}

namespace Matrix.PosSemidef

/-- For PSD matrices `A` and `B`, `ker(A + B) ⊆ ker(A)`.
Proof: `v†(A+B)v = v†Av + v†Bv = 0` with both nonneg implies `v†Av = 0`. -/
theorem mulVec_eq_zero_left
    {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : Fin D → ℂ) (hv : (A + B) *ᵥ v = 0) :
    A *ᵥ v = 0 := by
  have hqf : star v ⬝ᵥ ((A + B) *ᵥ v) = 0 := by rw [hv]; simp
  rw [add_mulVec, dotProduct_add] at hqf
  have h1_re := hA.re_dotProduct_nonneg v
  have h2_re := hB.re_dotProduct_nonneg v
  have h3_re : (star v ⬝ᵥ (A *ᵥ v)).re + (star v ⬝ᵥ (B *ᵥ v)).re = 0 := by
    have := congr_arg Complex.re hqf; simpa using this
  change 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re at h1_re
  change 0 ≤ (star v ⬝ᵥ (B *ᵥ v)).re at h2_re
  have hre : (star v ⬝ᵥ (A *ᵥ v)).re = 0 := by linarith
  exact (hA.dotProduct_mulVec_zero_iff v).mp
    (Complex.ext hre (hA.isHermitian.im_star_dotProduct_mulVec_self v))

/-- For PSD matrices `A` and `B`, `ker(A + B) ⊆ ker(B)`. -/
theorem mulVec_eq_zero_right
    {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : Fin D → ℂ) (hv : (A + B) *ᵥ v = 0) :
    B *ᵥ v = 0 := by
  exact mulVec_eq_zero_left hB hA v (by simpa [add_comm] using hv)

end Matrix.PosSemidef

end KernelPSD
