/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.HalfChainSchmidt
import TNLean.MPS.ParentHamiltonian.HalfChainSpectralComparison
import QICLean.Analysis.MatrixSqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Positive half-chain spectral representatives

The positive boundary matrix \(H_L=\sqrt{G_L}W_L\sqrt{G_L}\) has the same nonzero
eigenvalues, with multiplicity, as the physical half-chain reduced matrix.
Its trace is the squared norm of the actual ring vector, so normalization uses
that finite-size norm rather than the limiting norm.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6 and the preceding
Schmidt calculation, lines 970–993 of MPSarchive.tex. The transfer map here is
trace preserving; the diagonal fixed point is its right fixed point. This is
the conjugate-transposed Kraus convention relative to the source.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker
open Filter Polynomial
open scoped Topology

namespace MPSTensor

variable {d D : ℕ}

/-- The positive boundary representative \(\sqrt{G_L}W_L\sqrt{G_L}\) of the
half-chain reduced spectrum. -/
noncomputable def halfChainSpectralMatrix (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  CFC.sqrt (halfChainGram A L) *
    (halfChainSwapMatrix A L * (halfChainSwapMatrix A L)ᴴ) *
      CFC.sqrt (halfChainGram A L)

/-- The boundary spectral representative is positive, including when the
half-chain Gram matrix is singular. -/
theorem posSemidef_halfChainSpectralMatrix (A : MPSTensor d D) (L : ℕ) :
    (halfChainSpectralMatrix A L).PosSemidef := by
  simpa only [halfChainSpectralMatrix, Matrix.conjTranspose_cfc_sqrt] using
    (Matrix.posSemidef_self_mul_conjTranspose (halfChainSwapMatrix A L)).mul_mul_conjTranspose_same
      (CFC.sqrt (halfChainGram A L))

/-- The physical and positive boundary characteristic polynomials agree after
adding precisely \(D^2\) and \(d^L\) zero eigenvalues, respectively. -/
theorem charpoly_halfChainSpectralMatrix (A : MPSTensor d D) (L : ℕ) :
    X ^ (D * D) * (halfChainReducedMatrix A L).charpoly =
      X ^ d ^ L * (halfChainSpectralMatrix A L).charpoly := by
  rw [charpoly_halfChainReducedMatrix]
  congr 1
  symm
  rw [halfChainSpectralMatrix, Matrix.mul_assoc,
    Matrix.charpoly_mul_comm (CFC.sqrt (halfChainGram A L)), Matrix.mul_assoc,
    CFC.sqrt_mul_sqrt_self (halfChainGram A L)
      (Matrix.posSemidef_conjTranspose_mul_self (halfChainMatrix A L)).nonneg,
    halfChainSwapMatrix_mul_conjTranspose]

/-- The squared norm of the finite ring, expressed as the trace of its actual
unnormalized reduced density matrix. -/
noncomputable def halfChainNormSq (A : MPSTensor d D) (L : ℕ) : ℝ :=
  (halfChainReducedMatrix A L).trace.re

/-- The finite-size normalization is the sum of squared ring amplitudes. -/
theorem halfChainNormSq_eq_sum (A : MPSTensor d D) (L : ℕ) :
    halfChainNormSq A L =
      ∑ σ : Cfg d L, ∑ τ : Cfg d L, Complex.normSq (mpv A (Fin.append σ τ)) := by
  simp only [halfChainNormSq, Matrix.trace, halfChainReducedMatrix_apply,
    Matrix.diag_apply, Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- The actual squared ring norm is nonnegative. -/
theorem halfChainNormSq_nonneg (A : MPSTensor d D) (L : ℕ) :
    0 ≤ halfChainNormSq A L := by
  rw [halfChainNormSq_eq_sum]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The positive boundary representative has the same trace as the physical
reduced matrix, including at zero-norm ring lengths. -/
theorem trace_halfChainSpectralMatrix (A : MPSTensor d D) (L : ℕ) :
    (halfChainSpectralMatrix A L).trace = (halfChainReducedMatrix A L).trace := by
  rw [halfChainSpectralMatrix, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self (halfChainGram A L)
      (Matrix.posSemidef_conjTranspose_mul_self (halfChainMatrix A L)).nonneg,
    halfChainReducedMatrix_eq_mul_swap_gram,
    ← halfChainSwapMatrix_mul_conjTranspose, halfChainGram, Matrix.mul_assoc,
    Matrix.trace_mul_comm (halfChainMatrix A L)ᴴ, Matrix.mul_assoc]

/-- The normalized physical reduced matrix. At zero-norm lengths it is defined
as zero; convergence theorems establish that such lengths are eventually absent. -/
noncomputable def normalizedHalfChainReducedMatrix (A : MPSTensor d D) (L : ℕ) :
    Matrix (Cfg d L) (Cfg d L) ℂ :=
  (halfChainNormSq A L)⁻¹ • halfChainReducedMatrix A L

/-- The normalized positive boundary spectral representative, divided by the
same actual ring norm as the physical reduced matrix. -/
noncomputable def normalizedHalfChainSpectralMatrix (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  (halfChainNormSq A L)⁻¹ • halfChainSpectralMatrix A L

/-- Positivity of the normalized physical reduced matrix. -/
theorem posSemidef_normalizedHalfChainReducedMatrix (A : MPSTensor d D) (L : ℕ) :
    (normalizedHalfChainReducedMatrix A L).PosSemidef :=
  (posSemidef_halfChainReducedMatrix A L).smul
    (inv_nonneg.mpr (halfChainNormSq_nonneg A L))

/-- Positivity of the normalized boundary spectral representative. -/
theorem posSemidef_normalizedHalfChainSpectralMatrix (A : MPSTensor d D) (L : ℕ) :
    (normalizedHalfChainSpectralMatrix A L).PosSemidef :=
  (posSemidef_halfChainSpectralMatrix A L).smul
    (inv_nonneg.mpr (halfChainNormSq_nonneg A L))


/-- The positive boundary representative after normalization still has exactly
the physical spectrum, with finite-size zero padding. -/
theorem charpoly_normalizedHalfChainSpectralMatrix (A : MPSTensor d D) (L : ℕ) :
    X ^ (D * D) * (normalizedHalfChainReducedMatrix A L).charpoly =
      X ^ d ^ L * (normalizedHalfChainSpectralMatrix A L).charpoly := by
  let c : ℝ := (halfChainNormSq A L)⁻¹
  let P := halfChainMatrix A L
  let W := halfChainSwapMatrix A L * (halfChainSwapMatrix A L)ᴴ
  let S := CFC.sqrt (halfChainGram A L)
  have hphys : normalizedHalfChainReducedMatrix A L = P * (c • W * Pᴴ) := by
    simp only [normalizedHalfChainReducedMatrix, halfChainReducedMatrix_eq_mul_swap_gram,
      ← halfChainSwapMatrix_mul_conjTranspose, c, P, W, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc]
  have hbound : normalizedHalfChainSpectralMatrix A L = S * (c • W) * S := by
    simp only [normalizedHalfChainSpectralMatrix, halfChainSpectralMatrix, S, c, W,
      Matrix.mul_smul, Matrix.smul_mul]
  have hsq : S * S = halfChainGram A L :=
    CFC.sqrt_mul_sqrt_self (halfChainGram A L)
      (Matrix.posSemidef_conjTranspose_mul_self (halfChainMatrix A L)).nonneg
  rw [hphys, hbound]
  have h := Matrix.charpoly_mul_comm' P (c • W * Pᴴ)
  have hb : (S * (c • W) * S).charpoly = (c • W * halfChainGram A L).charpoly := by
    rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm S (c • W * S), Matrix.mul_assoc, hsq]
  rw [hb]
  simpa only [Matrix.mul_assoc, P, halfChainGram, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fun] using h

section Limit

variable (A : MPSTensor d D) (lam : Fin D → ℝ)

/-- The limiting overlap matrix, diagonal with entry \(\lambda_\alpha\)
on boundary pair \((\alpha,\beta)\). -/
noncomputable def halfChainGramLimit : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.diagonal fun p => (lam p.1 : ℂ)

/-- The limiting two-boundary density, diagonal with entries
\(\lambda_\alpha\lambda_\beta\), equivalently \(\Lambda\otimes\Lambda\). -/
noncomputable def halfChainSpectrumLimit : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.diagonal fun p => ((lam p.1 * lam p.2 : ℝ) : ℂ)

/-- The diagonal limiting matrix is exactly the Kronecker square of the
fixed-point density. -/
theorem halfChainSpectrumLimit_eq_kronecker :
    halfChainSpectrumLimit lam =
      (Matrix.diagonal fun a => (lam a : ℂ)) ⊗ₖ (Matrix.diagonal fun a => (lam a : ℂ)) := by
  simp only [halfChainSpectrumLimit, Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]

/-- Nonnegative fixed-point weights give a positive two-boundary limit. -/
theorem posSemidef_halfChainSpectrumLimit (hlam : ∀ a, 0 ≤ lam a) :
    (halfChainSpectrumLimit lam).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro p
  exact Complex.zero_le_real.mpr (mul_nonneg (hlam p.1) (hlam p.2))

/-- The limiting two-boundary density has trace one. -/
theorem trace_halfChainSpectrumLimit (htr : ∑ a, lam a = 1) :
    (halfChainSpectrumLimit lam).trace = 1 := by
  simp only [halfChainSpectrumLimit, Matrix.trace_diagonal, Fintype.sum_prod_type,
    Complex.ofReal_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  norm_cast
  rw [htr, one_mul]

private theorem trace_diagonal_lam (htr : ∑ a, lam a = 1) :
    (Matrix.diagonal (fun a => (lam a : ℂ))).trace = 1 := by
  simp only [Matrix.trace_diagonal, ← Complex.ofReal_sum, htr, Complex.ofReal_one]

/-- The geometric transfer-error estimate implies convergence of the actual
half-chain Gram matrices. No positivity or invertibility is needed here. -/
theorem tendsto_halfChainGram
    (htr : ∑ a, lam a = 1)
    (hTP : IsTracePreservingMap (Kraus.transferMap A))
    (hfix : Kraus.transferMap A (Matrix.diagonal fun a => (lam a : ℂ)) =
      Matrix.diagonal fun a => (lam a : ℂ))
    (hgap : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A - fixedPointProj (Matrix.diagonal fun a => (lam a : ℂ))
          (by rw [trace_diagonal_lam lam htr]; exact one_ne_zero))) < 1) :
    Tendsto (halfChainGram A) atTop (𝓝 (halfChainGramLimit lam)) := by
  have ht := trace_diagonal_lam lam htr
  obtain ⟨C, r, _, hr0, hr1, hbound⟩ :=
    exists_geometric_bound_halfChainGram_sub_fixedPointProj A
      (Matrix.diagonal fun a => (lam a : ℂ)) (by rw [ht]; exact one_ne_zero) hTP hfix hgap
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_pi_nhds.mpr
  intro q
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun L : ℕ => C * r ^ L) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with L hL
  simpa only [fixedPointProj_single_entry_diagonal, ht, div_one, halfChainGramLimit] using
    hbound L hL p q

private theorem sqrt_diagonal_boundary (g : Fin D × Fin D → ℝ) (hg : ∀ p, 0 ≤ g p) :
    CFC.sqrt (Matrix.diagonal fun p : Fin D × Fin D => (g p : ℂ)) =
      Matrix.diagonal (fun p : Fin D × Fin D => (Real.sqrt (g p) : ℂ)) := by
  have hG : (Matrix.diagonal fun p : Fin D × Fin D => (g p : ℂ)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun p => Complex.zero_le_real.mpr (hg p)
  have hS : (Matrix.diagonal
      (fun p : Fin D × Fin D => (Real.sqrt (g p) : ℂ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun _ =>
      Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  apply (CFC.sqrt_eq_iff _ _ hG.nonneg hS.nonneg).mpr
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  simp [← Complex.ofReal_mul, Real.mul_self_sqrt (hg p)]

/-- Convergence of the positive Hermitian representatives follows from the
geometric Gram convergence and continuity of the positive square root. This
statement includes singular nonnegative fixed points and asserts no quantitative
square-root rate. -/
theorem tendsto_halfChainSpectralMatrix_of_diagonal
    (g : Fin D × Fin D → ℝ) (hg : ∀ p, 0 ≤ g p)
    (hG : Tendsto (halfChainGram A) atTop
      (𝓝 (Matrix.diagonal fun p : Fin D × Fin D => (g p : ℂ)))) :
    Tendsto (halfChainSpectralMatrix A) atTop
      (𝓝 (Matrix.diagonal fun p : Fin D × Fin D => ((g p * g p.swap : ℝ) : ℂ))) := by
  have hpos : (Matrix.diagonal fun p : Fin D × Fin D => (g p : ℂ)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun p => Complex.zero_le_real.mpr (hg p)
  have hS : Tendsto (fun L => CFC.sqrt (halfChainGram A L)) atTop
      (𝓝 (CFC.sqrt (Matrix.diagonal fun p : Fin D × Fin D => (g p : ℂ)))) :=
    (CFC.continuousOn_sqrt _ hpos.nonneg).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hG, Eventually.of_forall fun L =>
        (Matrix.posSemidef_conjTranspose_mul_self (halfChainMatrix A L)).nonneg⟩)
  have hW : Tendsto (fun L => halfChainSwapMatrix A L * (halfChainSwapMatrix A L)ᴴ)
      atTop (𝓝 (Matrix.diagonal fun p : Fin D × Fin D => (g p.swap : ℂ))) := by
    apply tendsto_pi_nhds.mpr
    intro p
    apply tendsto_pi_nhds.mpr
    intro q
    simp_rw [halfChainSwapMatrix_mul_conjTranspose]
    have h := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hG q.swap) p.swap
    convert h using 1
    · rfl
    · congr 1
      by_cases hpq : p = q
      · subst hpq; simp
      · have hswap : q.swap ≠ p.swap := fun h => hpq (Prod.swap_injective h).symm
        simp [hpq, hswap]
  have heq : CFC.sqrt (Matrix.diagonal fun p : Fin D × Fin D => (g p : ℂ)) *
      (Matrix.diagonal fun p : Fin D × Fin D => (g p.swap : ℂ)) *
        CFC.sqrt (Matrix.diagonal fun p : Fin D × Fin D => (g p : ℂ)) =
          Matrix.diagonal (fun p : Fin D × Fin D => ((g p * g p.swap : ℝ) : ℂ)) := by
    rw [sqrt_diagonal_boundary g hg, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    have hs : (Real.sqrt (g p) : ℂ) * (Real.sqrt (g p) : ℂ) = (g p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg p)]
    push_cast
    calc
      (Real.sqrt (g p) : ℂ) * (g p.swap : ℂ) * (Real.sqrt (g p) : ℂ) =
          ((Real.sqrt (g p) : ℂ) * (Real.sqrt (g p) : ℂ)) * (g p.swap : ℂ) := by ring
      _ = _ := by rw [hs]
  have h := (hS.mul hW).mul hS
  rw [heq] at h
  exact h

/-- In trace-preserving convention the two-boundary limit is
\(\Lambda\otimes\Lambda\). -/
theorem tendsto_halfChainSpectralMatrix (hlam : ∀ a, 0 ≤ lam a)
    (hG : Tendsto (halfChainGram A) atTop (𝓝 (halfChainGramLimit lam))) :
    Tendsto (halfChainSpectralMatrix A) atTop (𝓝 (halfChainSpectrumLimit lam)) :=
  tendsto_halfChainSpectralMatrix_of_diagonal A (fun p => lam p.1) (fun p => hlam p.1) hG

/-- The actual finite-ring norm tends to one; no finite-length normalization
hypothesis is imposed. -/
theorem tendsto_halfChainNormSq (htr : ∑ a, lam a = 1)
    (hH : Tendsto (halfChainSpectralMatrix A) atTop (𝓝 (halfChainSpectrumLimit lam))) :
    Tendsto (halfChainNormSq A) atTop (𝓝 1) := by
  have ht : Tendsto (fun L => (halfChainSpectralMatrix A L).trace) atTop
      (𝓝 (halfChainSpectrumLimit lam).trace) :=
    tendsto_finsetSum _ fun p _ => tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hH p) p
  rw [trace_halfChainSpectrumLimit lam htr] at ht
  change Tendsto (fun L => (halfChainReducedMatrix A L).trace.re) atTop (𝓝 1)
  simpa only [trace_halfChainSpectralMatrix, Complex.one_re, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp ht

/-- The ring state is nonzero at every sufficiently large even length. -/
theorem eventually_halfChainNormSq_pos
    (hZ : Tendsto (halfChainNormSq A) atTop (𝓝 1)) :
    ∀ᶠ L in atTop, 0 < halfChainNormSq A L :=
  hZ.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

/-- Dividing by the actual finite-ring norm preserves the two-boundary limit. -/
theorem tendsto_normalizedHalfChainSpectralMatrix
    (hZ : Tendsto (halfChainNormSq A) atTop (𝓝 1))
    (hH : Tendsto (halfChainSpectralMatrix A) atTop (𝓝 (halfChainSpectrumLimit lam))) :
    Tendsto (normalizedHalfChainSpectralMatrix A) atTop (𝓝 (halfChainSpectrumLimit lam)) := by
  change Tendsto (fun L => (halfChainNormSq A L)⁻¹ • halfChainSpectralMatrix A L) _ _
  simpa only [inv_one, one_smul] using
    (hZ.inv₀ one_ne_zero).smul hH

end Limit

/-- At every nonzero ring length the physical reduced matrix has trace one. -/
theorem trace_normalizedHalfChainReducedMatrix (A : MPSTensor d D) (L : ℕ)
    (hZ : halfChainNormSq A L ≠ 0) :
    (normalizedHalfChainReducedMatrix A L).trace = 1 := by
  have him := (RCLike.nonneg_iff.mp (posSemidef_halfChainReducedMatrix A L).trace_nonneg).2
  have heq : (halfChainReducedMatrix A L).trace = (halfChainNormSq A L : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using him
  rw [normalizedHalfChainReducedMatrix, Matrix.trace_smul, heq]
  simp [Complex.real_smul, hZ]


/-- The decreasing eigenvalues of the actual normalized physical reduced
matrix, counted with multiplicity and extended by zeros beyond \(d^L\). -/
noncomputable def halfChainEigenvalues (A : MPSTensor d D) (L : ℕ) : ℕ → ℝ :=
  (posSemidef_normalizedHalfChainReducedMatrix A L).isHermitian.paddedEigenvalues

/-- The physical entanglement spectrum equals the decreasing spectrum of the
positive \(D^2\)-dimensional boundary representative, with zeros extending both
lists. This equality is valid at every finite size, even when \(d^L<D^2\). -/
theorem halfChainEigenvalues_eq_boundary (A : MPSTensor d D) (L : ℕ) :
    halfChainEigenvalues A L =
      (posSemidef_normalizedHalfChainSpectralMatrix A L).isHermitian.paddedEigenvalues := by
  apply (posSemidef_normalizedHalfChainReducedMatrix A L).paddedEigenvalues_eq_of_charpoly
    (posSemidef_normalizedHalfChainSpectralMatrix A L)
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun] using
    charpoly_normalizedHalfChainSpectralMatrix A L

/-- Every physical eigenvalue beyond the squared bond dimension is zero,
independently of the physical half-chain dimension. -/
theorem halfChainEigenvalues_eq_zero (A : MPSTensor d D) (L k : ℕ) (hk : D * D ≤ k) :
    halfChainEigenvalues A L k = 0 := by
  rw [halfChainEigenvalues_eq_boundary]
  exact Matrix.IsHermitian.paddedEigenvalues_eq_zero _ (by simpa using hk)

/-- Positive boundary convergence implies convergence of every ordered physical
reduced-density eigenvalue, after normalization by the actual finite ring norm.
The limit is the decreasing list of \(\lambda_\alpha\lambda_\beta\), with
multiplicities and trailing zeros. -/
theorem tendsto_halfChainEigenvalues_of_spectralMatrix
    (A : MPSTensor d D) (lam : Fin D → ℝ) (hlam : ∀ a, 0 ≤ lam a)
    (htr : ∑ a, lam a = 1)
    (hH : Tendsto (halfChainSpectralMatrix A) atTop (𝓝 (halfChainSpectrumLimit lam)))
    (k : ℕ) :
    Tendsto (fun L => halfChainEigenvalues A L k) atTop
      (𝓝 ((posSemidef_halfChainSpectrumLimit lam hlam).isHermitian.paddedEigenvalues k)) := by
  simp_rw [halfChainEigenvalues_eq_boundary]
  exact Matrix.IsHermitian.paddedEigenvalues_tendsto
    (fun L => (posSemidef_normalizedHalfChainSpectralMatrix A L).isHermitian)
    (posSemidef_halfChainSpectrumLimit lam hlam).isHermitian
    (tendsto_normalizedHalfChainSpectralMatrix A lam (tendsto_halfChainNormSq A lam htr hH) hH) k

/-- The half-chain entanglement spectrum converges in trace-preserving
convention under the complementary transfer gap. The same geometric error
\(Cr^L\) established for the Gram entries supplies the convergence input;
no diagonalizability or finite-length normalization assumption is added.
Source: PGVWC07, Theorem 6, in conjugate-transposed Kraus convention. -/
theorem tendsto_halfChainEigenvalues
    (A : MPSTensor d D) (lam : Fin D → ℝ) (hlam : ∀ a, 0 ≤ lam a)
    (htr : ∑ a, lam a = 1)
    (hTP : IsTracePreservingMap (Kraus.transferMap A))
    (hfix : Kraus.transferMap A (Matrix.diagonal fun a => (lam a : ℂ)) =
      Matrix.diagonal fun a => (lam a : ℂ))
    (hgap : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A - fixedPointProj (Matrix.diagonal fun a => (lam a : ℂ))
          (by rw [trace_diagonal_lam lam htr]; exact one_ne_zero))) < 1)
    (k : ℕ) :
    Tendsto (fun L => halfChainEigenvalues A L k) atTop
      (𝓝 ((posSemidef_halfChainSpectrumLimit lam hlam).isHermitian.paddedEigenvalues k)) :=
  tendsto_halfChainEigenvalues_of_spectralMatrix A lam hlam htr
    (tendsto_halfChainSpectralMatrix A lam hlam (tendsto_halfChainGram A lam htr hTP hfix hgap)) k

end MPSTensor
