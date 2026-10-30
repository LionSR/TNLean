/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.HalfChainSpectrum
import QICLean.Algebra.OperatorNormFrobenius

/-!
# Dimension-independent stability of the physical half-chain spectrum

Read an actual ring vector as the matrix of coefficients of its two
halves. Its operator norm is bounded by the vector norm. Factoring the
difference of the two reduced matrices gives a bound independent of the
physical half-chain dimension. Weyl's inequality then controls every
ordered, zero-padded half-chain eigenvalue of normalized periodic states.

These comparisons allow a physically vanishing canonical remainder to
be discarded before passing to the half-chain spectrum. They do not
assume a canonical decomposition or a spectral-convergence conclusion.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6 and the half-chain
coefficient decomposition, lines 970–993.
-/

noncomputable section

open Filter Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators ComplexOrder

namespace MPSTensor

variable {d D E L : ℕ}

/-- The actual coefficients of a ring vector, separated into its two
halves. Source: PGVWC07, arXiv:quant-ph/0608197, lines 970–976. -/
def ringBipartiteKernel (ψ : MPVSpace d (L + L)) : Matrix (Cfg d L) (Cfg d L) ℂ :=
  fun σ τ ↦ ψ (Fin.append σ τ)

/-- The reduced matrix of the actual ring vector after tracing out the
second half. Source: PGVWC07, arXiv:quant-ph/0608197, lines 979–985. -/
def ringVectorReducedMatrix (ψ : MPVSpace d (L + L)) : Matrix (Cfg d L) (Cfg d L) ℂ :=
  ringBipartiteKernel ψ * (ringBipartiteKernel ψ)ᴴ

/-- Reshaping the actual coefficient vector is contractive from its
Euclidean norm to the matrix operator norm. No dimension factor occurs.
Source: PGVWC07, arXiv:quant-ph/0608197, lines 970–976. -/
theorem norm_ringBipartiteKernel_le (ψ : MPVSpace d (L + L)) :
    ‖ringBipartiteKernel ψ‖ ≤ ‖ψ‖ := by
  have hsum : (∑ p : Cfg d L × Cfg d L, ‖ringBipartiteKernel ψ p.1 p.2‖ ^ 2) =
      ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact (Fin.appendEquiv L L).sum_comp (fun σ : Cfg d (L + L) ↦ ‖ψ σ‖ ^ 2)
  have h := Matrix.toEuclideanCLM_norm_sq_le_sum_norm_sq (ringBipartiteKernel ψ)
  rw [hsum] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (by simpa only [← Matrix.cstar_norm_def] using h)

/-- The reduced matrices of two actual ring vectors are close whenever
the vectors are close, uniformly in chain length and physical dimension.
Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6, lines 970–993. -/
theorem norm_ringVectorReducedMatrix_sub_le (ψ φ : MPVSpace d (L + L)) :
    ‖ringVectorReducedMatrix ψ - ringVectorReducedMatrix φ‖ ≤
      (‖ψ‖ + ‖φ‖) * ‖ψ - φ‖ := by
  have hsub : ringBipartiteKernel ψ - ringBipartiteKernel φ =
      ringBipartiteKernel (ψ - φ) := rfl
  have hfactor : ringVectorReducedMatrix ψ - ringVectorReducedMatrix φ =
      (ringBipartiteKernel ψ - ringBipartiteKernel φ) * (ringBipartiteKernel ψ)ᴴ +
        ringBipartiteKernel φ * (ringBipartiteKernel ψ - ringBipartiteKernel φ)ᴴ := by
    simp only [ringVectorReducedMatrix, Matrix.conjTranspose_sub, sub_mul, mul_sub]
    abel
  rw [hfactor]
  calc
    _ ≤ ‖(ringBipartiteKernel ψ - ringBipartiteKernel φ) * (ringBipartiteKernel ψ)ᴴ‖ +
        ‖ringBipartiteKernel φ * (ringBipartiteKernel ψ - ringBipartiteKernel φ)ᴴ‖ :=
      norm_add_le _ _
    _ ≤ ‖ringBipartiteKernel ψ - ringBipartiteKernel φ‖ * ‖ringBipartiteKernel ψ‖ +
        ‖ringBipartiteKernel φ‖ * ‖ringBipartiteKernel ψ - ringBipartiteKernel φ‖ := by
      have h₁ := norm_mul_le (ringBipartiteKernel ψ - ringBipartiteKernel φ)
        (ringBipartiteKernel ψ)ᴴ
      have h₂ := norm_mul_le (ringBipartiteKernel φ)
        (ringBipartiteKernel ψ - ringBipartiteKernel φ)ᴴ
      rw [Matrix.l2_opNorm_conjTranspose] at h₁ h₂
      exact add_le_add h₁ h₂
    _ ≤ ‖ψ - φ‖ * ‖ψ‖ + ‖φ‖ * ‖ψ - φ‖ := by
      simp only [hsub]
      gcongr <;> exact norm_ringBipartiteKernel_le _
    _ = _ := by ring

/-- The finite half-chain normalization is the squared norm of the
actual original ring vector. Source: PGVWC07, arXiv:quant-ph/0608197,
lines 970–985, finite normalization in Theorem 6. -/
theorem halfChainNormSq_eq_norm_mpvState_sq (A : MPSTensor d D) (L : ℕ) :
    halfChainNormSq A L = ‖mpvState A (L + L)‖ ^ 2 := by
  rw [halfChainNormSq_eq_sum, EuclideanSpace.norm_sq_eq,
    ← (Fin.appendEquiv L L).sum_comp, Fintype.sum_prod_type]
  simp only [mpvState_apply, Complex.normSq_eq_norm_sq]
  rfl

/-- The actual normalized reduced matrix is the reduced matrix of the
actual normalized periodic vector, including zero-norm lengths.
Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6, lines 970–993. -/
theorem normalizedHalfChainReducedMatrix_eq_ringVectorReducedMatrix
    (A : MPSTensor d D) (L : ℕ) :
    normalizedHalfChainReducedMatrix A L =
      ringVectorReducedMatrix (normalizedMPVState A (L + L)) := by
  have hK : ringBipartiteKernel (normalizedMPVState A (L + L)) =
      ((‖mpvState A (L + L)‖ : ℂ)⁻¹) • halfChainKernel A L := by
    ext σ τ
    simp only [ringBipartiteKernel, normalizedMPVState, PiLp.smul_apply,
      mpvState_apply, Matrix.smul_apply, halfChainKernel_apply, smul_eq_mul]
  rw [ringVectorReducedMatrix, hK, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, normalizedHalfChainReducedMatrix,
    halfChainNormSq_eq_norm_mpvState_sq]
  ext σ τ
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.star_def,
    map_inv₀, Complex.conj_ofReal, pow_two, Complex.ofReal_mul, Complex.ofReal_inv,
    _root_.mul_inv_rev, halfChainReducedMatrix]

private theorem norm_normalizedMPVState_le_one (A : MPSTensor d D) (N : ℕ) :
    ‖normalizedMPVState A N‖ ≤ 1 := by
  by_cases h : mpvState A N = 0
  · simp only [normalizedMPVState, h, smul_zero, norm_zero, zero_le_one]
  · exact (norm_normalizedMPVState h).le

private theorem norm_normalizedMPVState_sub_self_le (A : MPSTensor d D) (N : ℕ) :
    ‖normalizedMPVState A N - mpvState A N‖ ≤ |1 - ‖mpvState A N‖| := by
  by_cases h : mpvState A N = 0
  · simp only [normalizedMPVState, h, smul_zero, sub_self, norm_zero, sub_zero,
      abs_one, zero_le_one]
  have hn : ‖mpvState A N‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hid : normalizedMPVState A N - mpvState A N =
      (((‖mpvState A N‖⁻¹ - 1 : ℝ) : ℂ)) • mpvState A N := by
    simp only [normalizedMPVState, Complex.ofReal_sub, Complex.ofReal_inv,
      Complex.ofReal_one, sub_smul, one_smul]
  rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  apply le_of_eq
  calc
    _ = |(‖mpvState A N‖⁻¹ - 1) * ‖mpvState A N‖| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
    _ = _ := by rw [sub_mul, inv_mul_cancel₀ hn, one_mul]

/-- A physical remainder and a norm-one limit control normalization
without a dimension-dependent denominator. This estimate includes
zero-norm ring lengths. Source: PGVWC07, arXiv:quant-ph/0608197,
Theorem 6, finite normalization after the half-chain decomposition. -/
theorem norm_normalizedMPVState_sub_le (A : MPSTensor d D) (B : MPSTensor d E) (N : ℕ) :
    ‖normalizedMPVState A N - normalizedMPVState B N‖ ≤
      2 * ‖mpvState A N - mpvState B N‖ + 2 * |‖mpvState B N‖ - 1| := by
  have hFirst : |1 - ‖mpvState A N‖| ≤
      ‖mpvState A N - mpvState B N‖ + |‖mpvState B N‖ - 1| := by
    calc
      _ = |‖mpvState A N‖ - 1| := abs_sub_comm _ _
      _ ≤ |‖mpvState A N‖ - ‖mpvState B N‖| + |‖mpvState B N‖ - 1| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (abs_norm_sub_norm_le _ _) le_rfl
  calc
    _ = ‖(normalizedMPVState A N - mpvState A N) +
        (mpvState A N - mpvState B N) +
        (mpvState B N - normalizedMPVState B N)‖ := by congr 1; abel
    _ ≤ ‖normalizedMPVState A N - mpvState A N‖ +
        ‖mpvState A N - mpvState B N‖ +
        ‖mpvState B N - normalizedMPVState B N‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |1 - ‖mpvState A N‖| + ‖mpvState A N - mpvState B N‖ +
        |1 - ‖mpvState B N‖| := by
      rw [norm_sub_rev (mpvState B N)]
      exact add_le_add
        (add_le_add (norm_normalizedMPVState_sub_self_le A N) le_rfl)
        (norm_normalizedMPVState_sub_self_le B N)
    _ ≤ _ := by rw [abs_sub_comm 1 ‖mpvState B N‖]; linarith

/-- An actual vanishing physical remainder and a norm-one dominant
vector imply convergence of the normalized periodic vectors. No
normalization-error estimate is a premise.
Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6, lines 970–993. -/
theorem tendsto_normalizedMPVState_sub_of_mpvState_sub
    (A : MPSTensor d D) (B : MPSTensor d E) (length : ℕ → ℕ)
    (hStates : Tendsto (fun n : ℕ ↦ ‖mpvState A (length n) - mpvState B (length n)‖)
      atTop (𝓝 0))
    (hNorm : Tendsto (fun n : ℕ ↦ ‖mpvState B (length n)‖) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ ↦
      ‖normalizedMPVState A (length n) - normalizedMPVState B (length n)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_normalizedMPVState_sub_le A B (length n))
  have h := (hStates.const_mul 2).add ((hNorm.sub_const 1).norm.const_mul 2)
  simpa only [sub_self, norm_zero, Real.norm_eq_abs, mul_zero, add_zero] using h

/-- Weyl's inequality for the decreasing spectra followed by zeroes.
This is the finite-dimensional spectral comparison used in PGVWC07,
arXiv:quant-ph/0608197, Theorem 6, with multiplicities retained. -/
theorem abs_halfChainEigenvalues_sub_le (A : MPSTensor d D) (B : MPSTensor d E)
    (L k : ℕ) :
    |halfChainEigenvalues A L k - halfChainEigenvalues B L k| ≤
      2 * ‖normalizedMPVState A (L + L) - normalizedMPVState B (L + L)‖ := by
  have hA := (posSemidef_normalizedHalfChainReducedMatrix A L).isHermitian
  have hB := (posSemidef_normalizedHalfChainReducedMatrix B L).isHermitian
  have hEig : |hA.paddedEigenvalues k - hB.paddedEigenvalues k| ≤
      ‖normalizedHalfChainReducedMatrix A L - normalizedHalfChainReducedMatrix B L‖ := by
    by_cases hk : k < Fintype.card (Cfg d L)
    · have h := hA.abs_eigenvalues₀_sub_le hB ⟨k, hk⟩
      rwa [← hA.paddedEigenvalues_fin ⟨k, hk⟩, ← hB.paddedEigenvalues_fin ⟨k, hk⟩] at h
    · rw [hA.paddedEigenvalues_eq_zero (Nat.le_of_not_lt hk),
        hB.paddedEigenvalues_eq_zero (Nat.le_of_not_lt hk), sub_self, abs_zero]
      exact norm_nonneg _
  apply hEig.trans
  rw [normalizedHalfChainReducedMatrix_eq_ringVectorReducedMatrix,
    normalizedHalfChainReducedMatrix_eq_ringVectorReducedMatrix]
  apply (norm_ringVectorReducedMatrix_sub_le _ _).trans
  exact mul_le_mul_of_nonneg_right
    (by linarith [norm_normalizedMPVState_le_one A (L + L),
      norm_normalizedMPVState_le_one B (L + L)]) (norm_nonneg _)

/-- A vanishing difference of actual normalized periodic vectors gives
the same limit for every ordered half-chain eigenvalue. The physical
dimension may grow with the ring length; no fixed-dimensional continuity
assumption is used. Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6. -/
theorem tendsto_halfChainEigenvalues_of_normalizedMPVState_sub
    (A : MPSTensor d D) (B : MPSTensor d E)
    (hStates : Tendsto
      (fun L : ℕ ↦ ‖normalizedMPVState A (L + L) - normalizedMPVState B (L + L)‖)
      atTop (𝓝 0)) (k : ℕ) {r : ℝ}
    (hB : Tendsto (fun L ↦ halfChainEigenvalues B L k) atTop (𝓝 r)) :
    Tendsto (fun L ↦ halfChainEigenvalues A L k) atTop (𝓝 r) := by
  have hDiff : Tendsto (fun L ↦ halfChainEigenvalues A L k - halfChainEigenvalues B L k)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun L ↦ ?_) (by simpa using hStates.const_mul 2)
    simpa only [Real.norm_eq_abs] using abs_halfChainEigenvalues_sub_le A B L k
  have h := hDiff.add hB
  simpa only [sub_add_cancel, zero_add] using h

end MPSTensor
