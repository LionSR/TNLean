/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import TNLean.Analysis.Entropy

/-!
# Klein's inequality for the quantum relative entropy

This file proves **Klein's inequality**: the quantum relative entropy of two
density matrices is nonnegative,
`D(ρ‖σ) = Re tr(ρ(log ρ − log σ)) ≥ 0`.

## Main result

* `quantumRelativeEntropy_nonneg`: for density matrices `ρ`, `σ` (positive
  semidefinite, trace one) with `σ` of full rank, `0 ≤ D(ρ‖σ)`.

## Proof outline

Write `ρ = ∑ᵢ pᵢ |eᵢ⟩⟨eᵢ|` and `σ = ∑ⱼ qⱼ |fⱼ⟩⟨fⱼ|` in their eigenbases. The
overlap numbers `Pᵢⱼ = |⟨eᵢ|fⱼ⟩|²` form a doubly stochastic matrix, since the
two eigenbases are orthonormal. A trace computation gives
`Re tr(ρ log ρ) = ∑ᵢ pᵢ log pᵢ` and `Re tr(ρ log σ) = ∑ᵢⱼ pᵢ Pᵢⱼ log qⱼ`, so

  `D(ρ‖σ) = ∑ᵢ pᵢ log pᵢ − ∑ᵢⱼ pᵢ Pᵢⱼ log qⱼ`.

The row sums `∑ⱼ Pᵢⱼ = 1` let the first sum be written over the index pair, and
the resulting expression `∑ᵢⱼ pᵢ Pᵢⱼ (log pᵢ − log qⱼ)` is bounded below using
the scalar tangent inequality `log x ≤ x − 1` together with the doubly
stochastic row and column sums and the trace-one normalizations of `p` and `q`.
This avoids the matrix Jensen / operator-convexity machinery entirely: the only
analytic input is `Real.log_le_sub_one_of_pos`.

## References

* Klein's inequality; see e.g. [M. Wolf, *Quantum Channels & Operations: Guided
  Tour*, Chapter 8 (Distance Measures)][Wolf2012QChannels].
* Layer 3 of the relative-entropy elimination route for strong subadditivity,
  `docs/paper-gaps/cpsv16_ssa_from_lieb_route.tex`.
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral form of a Hermitian matrix as a literal product
`U * diagonal (↑eigenvalues) * star U`, where `U` is the eigenvector unitary. -/
theorem spectral_form {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
        * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- The Hermitian functional calculus `hA.cfc f` as a literal product
`U * diagonal (↑(f ∘ eigenvalues)) * star U`. -/
theorem cfc_form {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hA.cfc f = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))
        * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

end Matrix.IsHermitian

namespace TNLean.Klein

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of `diagonal p * W * diagonal d * star W` as a double sum over the
overlap entries `W i j`. -/
theorem trace_diag_conj (p d : n → ℂ) (W : Matrix n n ℂ) :
    Matrix.trace (Matrix.diagonal p * W * Matrix.diagonal d * star W)
      = ∑ i, ∑ j, p i * d j * (W i j * star (W i j)) := by
  have hA : Matrix.diagonal p * W = Matrix.of (fun i j => p i * W i j) := by
    ext i j; simp [Matrix.diagonal_mul]
  have hB : Matrix.diagonal d * star W = Matrix.of (fun j k => d j * star (W k j)) := by
    ext j k; simp [Matrix.diagonal_mul, Matrix.star_apply]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Trace of `ρ * (hσ.cfc f)` as a double sum over the eigenvalues weighted by
the overlap matrix `W = star Uρ * Uσ` of the two eigenvector unitaries. -/
theorem trace_mul_cfc_eq_double_sum {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (ρ * hσ.cfc f)
      = ∑ i, ∑ j, (hρ.eigenvalues i : ℂ) * ((f (hσ.eigenvalues j) : ℝ) : ℂ)
          * (((star (hρ.eigenvectorUnitary : Matrix n n ℂ))
                * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j
            * star (((star (hρ.eigenvectorUnitary : Matrix n n ℂ))
                * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j)) := by
  set Vρ : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hVρ
  set Vσ : Matrix n n ℂ := (hσ.eigenvectorUnitary : Matrix n n ℂ)
  set dp : n → ℂ := fun i => ((hρ.eigenvalues i : ℝ) : ℂ)
  set dm : n → ℂ := fun j => ((f (hσ.eigenvalues j) : ℝ) : ℂ)
  set W : Matrix n n ℂ := star Vρ * Vσ with hW
  have hρ_eq : ρ = Vρ * Matrix.diagonal dp * star Vρ := hρ.spectral_form
  have hcfc_eq : hσ.cfc f = Vσ * Matrix.diagonal dm * star Vσ := hσ.cfc_form f
  conv_lhs => rw [hρ_eq, hcfc_eq]
  -- Reduce the conjugated product to `diagonal dp * W * diagonal dm * star W`
  -- via trace cyclicity, then apply `trace_diag_conj`.
  have hstarW : star W = star Vσ * Vρ := by rw [hW, star_mul, star_star]
  rw [← trace_diag_conj dp dm W, hstarW,
    show (Vρ * Matrix.diagonal dp * star Vρ * (Vσ * Matrix.diagonal dm * star Vσ))
        = Vρ * (Matrix.diagonal dp * (star Vρ * Vσ) * Matrix.diagonal dm * star Vσ) by
      simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm Vρ _, ← hW]
  simp only [Matrix.mul_assoc]

/-- Real part of `trace (ρ * hσ.cfc f)` as a real double sum weighted by the
doubly stochastic overlap matrix `P i j = |W i j|²`. -/
theorem re_trace_mul_cfc_eq_double_sum {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (ρ * hσ.cfc f)).re
      = ∑ i, ∑ j, hρ.eigenvalues i * f (hσ.eigenvalues j)
          * Complex.normSq (((star (hρ.eigenvectorUnitary : Matrix n n ℂ))
              * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  rw [trace_mul_cfc_eq_double_sum hρ hσ f, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set W : Matrix n n ℂ := (star (hρ.eigenvectorUnitary : Matrix n n ℂ))
    * (hσ.eigenvectorUnitary : Matrix n n ℂ)
  have hnsq : W i j * star (W i j) = ((Complex.normSq (W i j) : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [hnsq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- For a unitary matrix `W` (`W * star W = 1`), the row sums of `|W i j|²`
equal one. -/
theorem row_sum_normSq_eq_one {W : Matrix n n ℂ} (hW : W * star W = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h1 : (W * star W) i i = 1 := by rw [hW, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have hsum : ∑ j, W i j * (star W) j i = ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self, mul_comm]
  rw [hsum] at h1
  exact_mod_cast h1

/-- For a unitary matrix `W` (`star W * W = 1`), the column sums of `|W i j|²`
equal one. -/
theorem col_sum_normSq_eq_one {W : Matrix n n ℂ} (hW : star W * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h1 : (star W * W) j j = 1 := by rw [hW, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have hsum : ∑ i, (star W) j i * W i j = ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]
  rw [hsum] at h1
  exact_mod_cast h1

omit [DecidableEq n] in
/-- **Classical Gibbs / Klein core.** For a probability vector `p` (`pᵢ ≥ 0`,
`∑ pᵢ = 1`), strictly positive `q` summing to one, and a doubly stochastic
matrix `P` (nonnegative entries, row sums one and column sums one),
`∑ᵢⱼ pᵢ Pᵢⱼ log qⱼ ≤ ∑ᵢ pᵢ log pᵢ`.

The proof is the scalar Gibbs inequality: the per-term bound
`pᵢ (log qⱼ − log pᵢ) ≤ qⱼ − pᵢ` from `log x ≤ x − 1`, summed against the
doubly stochastic weights, telescopes to `∑ⱼ qⱼ − ∑ᵢ pᵢ = 0`. -/
theorem gibbs_core (p q : n → ℝ) (P : n → n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_pos : ∀ j, 0 < q j) (hq_sum : ∑ j, q j = 1)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_row : ∀ i, ∑ j, P i j = 1) (hP_col : ∀ j, ∑ i, P i j = 1) :
    ∑ i, ∑ j, p i * P i j * Real.log (q j) ≤ ∑ i, p i * Real.log (p i) := by
  -- Rewrite the right-hand side over the index pair using the row sums.
  have hRHS : ∑ i, p i * Real.log (p i)
      = ∑ i, ∑ j, p i * P i j * Real.log (p i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP_row i, mul_one]
  rw [hRHS, ← sub_nonneg, ← Finset.sum_sub_distrib]
  -- Per row, bound the difference below by `∑ⱼ Pᵢⱼ (pᵢ − qⱼ)`.
  have hterm : ∀ i,
      (∑ j, p i * P i j * Real.log (p i)) - (∑ j, p i * P i j * Real.log (q j))
        ≥ ∑ j, P i j * (p i - q j) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases eq_or_lt_of_le (hp_nonneg i) with hpi | hpi
    · -- `pᵢ = 0`: the difference vanishes and `Pᵢⱼ (0 − qⱼ) ≤ 0`.
      rw [← hpi]
      simp only [zero_mul, sub_zero, zero_sub]
      linarith [mul_nonneg (hP_nonneg i j) (hq_pos j).le]
    · -- `0 < pᵢ`: scale the scalar tangent inequality `log x ≤ x − 1`.
      have hlog : Real.log (q j) - Real.log (p i) ≤ q j / p i - 1 := by
        rw [← Real.log_div (hq_pos j).ne' hpi.ne']
        exact Real.log_le_sub_one_of_pos (div_pos (hq_pos j) hpi)
      have hkey : p i * (Real.log (q j) - Real.log (p i)) ≤ q j - p i := by
        have h := mul_le_mul_of_nonneg_left hlog hpi.le
        rwa [show p i * (q j / p i - 1) = q j - p i by
          rw [mul_sub, mul_one, mul_div_cancel₀ _ hpi.ne']] at h
      have hmul := mul_le_mul_of_nonneg_left hkey (hP_nonneg i j)
      nlinarith [hmul]
  refine le_trans ?_ (Finset.sum_le_sum fun i _ => hterm i)
  -- The lower bound sums to `∑ⱼ qⱼ − ∑ᵢ pᵢ = 0`.
  have hzero : ∑ i, ∑ j, P i j * (p i - q j) = 0 := by
    have hrow : ∀ i, ∑ j, P i j * (p i - q j)
        = p i * (∑ j, P i j) - ∑ j, P i j * q j := fun i => by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [hrow, hP_row]
    rw [Finset.sum_sub_distrib]
    simp only [mul_one]
    have hswap : ∑ i, ∑ j, P i j * q j = ∑ j, q j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, hP_col j, one_mul]
    rw [hp_sum, hswap, hq_sum, sub_self]
  rw [hzero]

/-- A positive semidefinite matrix with invertible determinant has strictly
positive eigenvalues. -/
theorem eigenvalues_pos_of_posSemidef_isUnit_det {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) (hσ_inv : IsUnit σ.det) (j : n) :
    0 < hσ.isHermitian.eigenvalues j := by
  have hne : (hσ.isHermitian.eigenvalues j : ℂ) ≠ 0 := fun hzero => hσ_inv.ne_zero <| by
    rw [hσ.isHermitian.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hzero
  exact lt_of_le_of_ne (hσ.eigenvalues_nonneg j) (Ne.symm fun h => hne (by rw [h]; simp))

end TNLean.Klein

open TNLean.Klein in
open scoped Matrix.Norms.L2Operator in
/-- **Klein's inequality.** The quantum relative entropy of two density matrices
is nonnegative: `D(ρ‖σ) = Re tr(ρ(log ρ − log σ)) ≥ 0`.

Here `ρ` and `σ` are density matrices — positive semidefinite, trace one — and
`σ` is assumed of full rank (`IsUnit σ.det`), the standard support condition
making `log σ` finite on the range of `ρ`.

Source: Klein's inequality; layer 3 of the relative-entropy elimination route
for strong subadditivity, `docs/paper-gaps/cpsv16_ssa_from_lieb_route.tex`;
blueprint `thm:klein_inequality`. -/
theorem quantumRelativeEntropy_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hρ_tr : ρ.trace = 1)
    (hσ : σ.PosSemidef) (hσ_tr : σ.trace = 1) (hσ_inv : IsUnit σ.det) :
    0 ≤ quantumRelativeEntropy ρ σ := by
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub, sub_nonneg]
  -- `D ≥ 0` ↔ `Re tr(ρ log σ) ≤ Re tr(ρ log ρ)`.
  have hlogρ : CFC.log ρ = hρ.isHermitian.cfc Real.log := by
    rw [CFC.log]; exact Matrix.IsHermitian.cfc_eq hρ.isHermitian Real.log
  have hlogσ : CFC.log σ = hσ.isHermitian.cfc Real.log := by
    rw [CFC.log]; exact Matrix.IsHermitian.cfc_eq hσ.isHermitian Real.log
  rw [hlogρ, hlogσ]
  set p : n → ℝ := fun i => hρ.isHermitian.eigenvalues i with hp_def
  set q : n → ℝ := fun j => hσ.isHermitian.eigenvalues j with hq_def
  set W : Matrix n n ℂ := (star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
    * (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hW_def
  set P : n → n → ℝ := fun i j => Complex.normSq (W i j) with hP_def
  -- `Re tr(ρ log ρ) = ∑ᵢ pᵢ log pᵢ`, from the eigenvalue form of the entropy.
  have hself : (Matrix.trace (ρ * hρ.isHermitian.cfc Real.log)).re
      = ∑ i, p i * Real.log (p i) := by
    have h := vonNeumannEntropy_eq_neg_trace_mul_log hρ.isHermitian
    rw [hlogρ, vonNeumannEntropy] at h
    have hre : (Matrix.trace (ρ * hρ.isHermitian.cfc Real.log)).re
        = -∑ i, Real.negMulLog (hρ.isHermitian.eigenvalues i) := by linarith
    rw [hre, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.negMulLog, hp_def]; ring
  -- `Re tr(ρ log σ) = ∑ᵢⱼ pᵢ Pᵢⱼ log qⱼ`, from the overlap double sum.
  have hcross : (Matrix.trace (ρ * hσ.isHermitian.cfc Real.log)).re
      = ∑ i, ∑ j, p i * P i j * Real.log (q j) := by
    rw [re_trace_mul_cfc_eq_double_sum hρ.isHermitian hσ.isHermitian Real.log]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hp_def, hq_def, hP_def, hW_def]; ring
  rw [hself, hcross]
  -- The overlap matrix `W` of the two eigenbases is unitary.
  have hρ_uu : star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
      * (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self hρ.isHermitian.eigenvectorUnitary
  have hρ_uu' : (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
      * star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hρ.isHermitian.eigenvectorUnitary.prop
  have hσ_uu : star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
      * (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self hσ.isHermitian.eigenvectorUnitary
  have hσ_uu' : (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
      * star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hσ.isHermitian.eigenvectorUnitary.prop
  have hWunit_row : W * star W = 1 := by
    rw [hW_def, star_mul, star_star]
    calc star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
            * (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
            * (star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
              * (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
        = star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
            * ((hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
              * star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
            * (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hσ_uu', Matrix.mul_one, hρ_uu]
  have hWunit_col : star W * W = 1 := by
    rw [hW_def, star_mul, star_star]
    calc star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
            * (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
            * (star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
              * (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
        = star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
            * ((hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
              * star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
            * (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hρ_uu', Matrix.mul_one, hσ_uu]
  -- Conclude with the classical Gibbs inequality.
  exact gibbs_core p q P (fun i => hρ.eigenvalues_nonneg i)
    (posSemidef_trace_one_eigenvalues_sum_one hρ hρ_tr)
    (fun j => eigenvalues_pos_of_posSemidef_isUnit_det hσ hσ_inv j)
    (posSemidef_trace_one_eigenvalues_sum_one hσ hσ_tr)
    (fun i j => Complex.normSq_nonneg _)
    (fun i => row_sum_normSq_eq_one hWunit_row i)
    (fun j => col_sum_normSq_eq_one hWunit_col j)
