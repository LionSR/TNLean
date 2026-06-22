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
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Instances.Matrix

/-!
# Auxiliary matrix lemmas

General-purpose matrix lemmas that are not specific to any chapter's theory.
Extracted from various files for reusability.

## Main results

- `Matrix.trace_conjTranspose_mul_self_re_eq_sum_norm_sq`: entrywise Hilbert--Schmidt
  trace identity
- `Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq`: the Hilbert--Schmidt
  trace form of the Frobenius norm
- `Matrix.trace_conjTranspose_mul_self_kronecker`: Hilbert--Schmidt trace-form
  multiplicativity for Kronecker products
- `Matrix.card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one`: determinant
  AM--GM lower bound for the Hilbert--Schmidt trace form
- `Matrix.PosSemidef.trace_mul_nonneg`: the trace product of two positive
  semidefinite matrices is nonnegative
- `Matrix.eq_zero_of_sum_mul_conjTranspose_eq_zero`: a positive sum of squares
  vanishes only if every summand vanishes
- `Matrix.eq_zero_of_sum_conjTranspose_mul_self_eq_zero`: the conjugate-transpose
  variant
- `Matrix.PosSemidef.mulVec_eq_zero_left/right`: kernel containment for PSD matrix sums
-/

open scoped Matrix BigOperators ComplexOrder Kronecker Matrix.Norms.Frobenius

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

section FrobeniusKronecker

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- The Hilbert--Schmidt trace form is multiplicative under Kronecker products. -/
theorem trace_conjTranspose_mul_self_kronecker
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    trace ((A ⊗ₖ B)ᴴ * (A ⊗ₖ B)) = trace (Aᴴ * A) * trace (Bᴴ * B) := by
  rw [conjTranspose_kronecker]
  rw [← mul_kronecker_mul (A := Aᴴ) (B := A) (A' := Bᴴ) (B' := B)]
  rw [trace_kronecker]

/-- The real Hilbert--Schmidt trace form is multiplicative under Kronecker products. -/
theorem trace_conjTranspose_mul_self_re_kronecker
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    (trace ((A ⊗ₖ B)ᴴ * (A ⊗ₖ B))).re =
      (trace (Aᴴ * A)).re * (trace (Bᴴ * B)).re := by
  have hA_im : (trace (Aᴴ * A)).im = 0 :=
    (RCLike.nonneg_iff.mp (posSemidef_conjTranspose_mul_self A).trace_nonneg).2
  have hB_im : (trace (Bᴴ * B)).im = 0 :=
    (RCLike.nonneg_iff.mp (posSemidef_conjTranspose_mul_self B).trace_nonneg).2
  calc
    (trace ((A ⊗ₖ B)ᴴ * (A ⊗ₖ B))).re =
        (trace (Aᴴ * A) * trace (Bᴴ * B)).re := by
          rw [trace_conjTranspose_mul_self_kronecker]
    _ = (trace (Aᴴ * A)).re * (trace (Bᴴ * B)).re := by
          rw [Complex.mul_re, hA_im, hB_im, mul_zero, sub_zero]

end FrobeniusKronecker

section KroneckerContinuity

variable {X R : Type*} [TopologicalSpace X] [TopologicalSpace R] [Mul R] [ContinuousMul R]
  {m n p q : Type*}

/-- The Kronecker product is jointly continuous in its two arguments. -/
theorem _root_.Continuous.matrix_kronecker {A : X → Matrix m n R} {B : X → Matrix p q R}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x) ⊗ₖ (B x) := by
  refine continuous_matrix fun r c => ?_
  obtain ⟨i₁, i₂⟩ := r
  obtain ⟨j₁, j₂⟩ := c
  exact (hA.matrix_elem i₁ j₁).mul (hB.matrix_elem i₂ j₂)

end KroneckerContinuity

section FrobeniusDeterminant

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Determinant AM--GM lower bound for the Hilbert--Schmidt trace form.**

If a square complex matrix has determinant of norm one, then the square of its
Frobenius norm is at least the dimension.  Equivalently,
`(Fintype.card n : ℝ) ≤ (trace (Aᴴ * A)).re`.

This is the singular-value AM--GM estimate used in Wolf's compactness argument
for Lorentz normal forms. -/
theorem card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one
    (A : Matrix n n ℂ) (hdet : ‖A.det‖ = 1) :
    (Fintype.card n : ℝ) ≤ (trace (Aᴴ * A)).re := by
  classical
  let B : Matrix n n ℂ := Aᴴ * A
  have hBherm : B.IsHermitian := by
    simpa only [B] using Matrix.isHermitian_conjTranspose_mul_self A
  have hBpsd : B.PosSemidef := by
    simpa only [B] using Matrix.posSemidef_conjTranspose_mul_self A
  have hdetB : Matrix.det B = 1 := by
    change Matrix.det (Aᴴ * A) = 1
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    have hconj : star A.det * A.det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
      simpa [Complex.star_def, Complex.normSq_eq_norm_sq] using
        (Complex.normSq_eq_conj_mul_self (z := A.det)).symm
    rw [hconj, hdet]
    norm_num
  have hprod_eq : ∏ i, hBherm.eigenvalues i = 1 := by
    have h : Matrix.det B = ∏ i, (hBherm.eigenvalues i : ℂ) :=
      hBherm.det_eq_prod_eigenvalues
    rw [hdetB] at h
    have h' : ((∏ i, hBherm.eigenvalues i : ℝ) : ℂ) = 1 := by
      simpa only [Complex.ofReal_prod] using h.symm
    exact_mod_cast h'
  have hcard_pos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := n)
  have hamgm : 1 ≤ (∑ i, hBherm.eigenvalues i) / (Fintype.card n : ℝ) := by
    have hweights_pos : 0 < ∑ _i : n, (1 : ℝ) := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
        hcard_pos
    have h :=
      Real.geom_mean_le_arith_mean
        (s := Finset.univ) (w := fun _ => (1 : ℝ))
        (z := fun i => hBherm.eigenvalues i)
        (by intro i hi; positivity)
        hweights_pos
        (by intro i hi; simpa only using hBpsd.eigenvalues_nonneg i)
    simpa only [ge_iff_le, Real.rpow_one, hprod_eq, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, _root_.mul_inv_rev, Real.one_rpow,
      one_mul] using h
  have hsum_ge : (Fintype.card n : ℝ) ≤ ∑ i, hBherm.eigenvalues i :=
    (one_le_div hcard_pos).mp hamgm
  have htrace_eq : (trace B).re = ∑ i, hBherm.eigenvalues i := by
    simpa only [Complex.coe_algebraMap, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re hBherm.trace_eq_sum_eigenvalues
  simpa only [B] using hsum_ge.trans_eq htrace_eq.symm

end FrobeniusDeterminant

section PosSemidefTrace

variable {n : Type*} [Fintype n]

namespace PosSemidef

/-- The trace product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ trace (A * B) := by
  classical
  let U : Matrix n n ℂ := ↑hB.isHermitian.eigenvectorUnitary
  let Λ : n → ℂ := fun i => ↑(hB.isHermitian.eigenvalues i)
  have hspec : B = U * diagonal Λ * Uᴴ := by
    simpa [U, Λ, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Function.comp_def] using hB.isHermitian.spectral_theorem
  have hUAU_psd : (Uᴴ * A * U).PosSemidef := by
    simpa only [mul_assoc, conjTranspose_conjTranspose] using
      hA.mul_mul_conjTranspose_same (B := Uᴴ)
  have hΛ_nonneg : ∀ i, 0 ≤ Λ i := by
    intro i
    change (0 : ℂ) ≤ ↑(hB.isHermitian.eigenvalues i)
    exact_mod_cast (hB.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hB i)
  have htrace_eq :
      trace (A * B) = trace ((Uᴴ * A * U) * diagonal Λ) := by
    rw [hspec]
    calc
      trace (A * (U * diagonal Λ * Uᴴ))
          = trace ((A * U) * diagonal Λ * Uᴴ) := by
              simp [mul_assoc]
      _ = trace (Uᴴ * (A * U) * diagonal Λ) := by
              simpa only using (trace_mul_cycle (A * U) (diagonal Λ) Uᴴ)
      _ = trace ((Uᴴ * A * U) * diagonal Λ) := by
              simp [mul_assoc]
  rw [htrace_eq, trace]
  refine Finset.sum_nonneg ?_
  intro i _hi
  have hdiag_nonneg : 0 ≤ (Uᴴ * A * U) i i := hUAU_psd.diag_nonneg
  change 0 ≤ (((Uᴴ * A * U) * diagonal Λ) i i)
  have hentry :
      (((Uᴴ * A * U) * diagonal Λ) i i) = (Uᴴ * A * U) i i * Λ i := by
    rw [mul_apply]
    simp [diagonal_apply]
  rw [hentry]
  exact mul_nonneg hdiag_nonneg (hΛ_nonneg i)

end PosSemidef

end PosSemidefTrace

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
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp htrace_zero

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
