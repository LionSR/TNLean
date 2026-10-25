/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritFamily
import QICLean.Analysis.KyFanNorm

/-!
# Middle-cut tail of the qutrit family

The explicit marginal of the qutrit state bounds the mass captured by a
finite-rank projection. Source: Schuch, Wolf, Verstraete and Cirac,
arXiv:0705.0292v2, `paper_v2.tex`, lines 475–479.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.EntropyScaling

private theorem trace_mul_qutritMiddleMarginal {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (P : Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ) :
    (P * qutritMiddleMarginal N p).trace.re =
      ∑ i : QutritLabel N, (P (qutritWord N i) (qutritWord N i)).re *
        qutritWeight N p i := by
  rw [qutritMiddleMarginal_factorization hN hp hp']
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.mul_apply, qutritBasisMatrix, EuclideanSpace.basisFun_apply]

private theorem sum_projection_qutritWord_le {N : ℕ} (hN : 0 < N)
    {P : Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) :
    (∑ i : QutritLabel N, (P (qutritWord N i) (qutritWord N i)).re) ≤ P.trace.re := by
  classical
  have hpos : P.PosSemidef := by
    simpa only [hP.eq, hPP] using Matrix.posSemidef_conjTranspose_mul_self P
  rw [Matrix.trace, Complex.re_sum]
  rw [← Finset.sum_image (f := fun a ↦ (P a a).re)
    (fun i _ j _ h ↦ qutritWord_injective hN h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ (Complex.nonneg_iff.mp (hpos.diag_nonneg (i := i))).1)

/-- A projection captures at most the flag weight and its remaining rank times
one binary weight. Source: arXiv:0705.0292v2, lines 475–479. -/
theorem trace_projection_qutritMiddleMarginal_le {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hflag : p / (2 : ℝ) ^ N ≤ 1 - p)
    {P : Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) :
    (P * qutritMiddleMarginal N p).trace.re ≤
      1 - p + ((P.rank : ℝ) - 1) * (p / (2 : ℝ) ^ N) := by
  have hproj : IsStarProjection P := ⟨hPP, hP⟩
  have hone := Complex.nonneg_iff.mp
    ((Matrix.nonneg_iff_posSemidef.mp hproj.one_sub.nonneg).diag_nonneg
      (i := qutritWord N (.inl ())))
  have hdiag : (P (qutritWord N (.inl ())) (qutritWord N (.inl ()))).re ≤ 1 := by
    simpa using hone.1
  have hsum := sum_projection_qutritWord_le hN hP hPP
  rw [← hP.rank_eq_trace_re_of_idem hPP] at hsum
  rw [trace_mul_qutritMiddleMarginal hN hp hp']
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, qutritWeight, ← Finset.sum_mul] at hsum ⊢
  change (P (qutritWord N (.inl default)) (qutritWord N (.inl default))).re ≤ 1 at hdiag
  generalize ht : p / (2 : ℝ) ^ N = t at *
  have ht0 : 0 ≤ t := ht ▸ div_nonneg hp (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hflag) (sub_nonneg.mpr hdiag),
    mul_le_mul_of_nonneg_right hsum ht0]

/-- The middle marginal is positive semidefinite, being the Gram matrix of the
middle coefficient matrix. Source: arXiv:0705.0292v2, equation `eq:magicstate`. -/
theorem qutritMiddleMarginal_posSemidef (N : ℕ) (p : ℝ) :
    (qutritMiddleMarginal N p).PosSemidef := by
  rw [qutritMiddleMarginal, partialTraceRight_vecMulVec_eq]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The mass of the largest `D` squared Schmidt coefficients is bounded by the
flag weight plus `D-1` binary weights. The estimate holds for every `D`.
Source: arXiv:0705.0292v2, lines 475–479. -/
theorem kyFanNorm_qutritMiddleMarginal_le {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hflag : p / (2 : ℝ) ^ N ≤ 1 - p) (D : ℕ) :
    (qutritMiddleMarginal_posSemidef N p).isHermitian.kyFanNorm D ≤
      1 - p + ((D : ℝ) - 1) * (p / (2 : ℝ) ^ N) := by
  obtain ⟨P, hP, hPP, htr, hcapture⟩ :=
    (qutritMiddleMarginal_posSemidef N p).isHermitian.exists_isProj_trace_eq_kyFanNorm D
  have hbound := trace_projection_qutritMiddleMarginal_le hN hp hp' hflag hP hPP
  rw [hcapture, hP.rank_eq_trace_re_of_idem hPP, htr] at hbound
  refine hbound.trans ?_
  gcongr
  exact min_le_left _ _

/-- The middle marginal has trace one. Source: arXiv:0705.0292v2,
equation `eq:magicstate`. -/
theorem trace_qutritMiddleMarginal {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : (qutritMiddleMarginal N p).trace.re = 1 := by
  simpa only [Matrix.one_mul, Matrix.one_apply_eq, Complex.one_re, one_mul,
    sum_qutritWeight] using trace_mul_qutritMiddleMarginal hN hp hp' 1

/-- The discarded middle-cut mass has the lower bound used in the source's
single-copy obstruction. Source: arXiv:0705.0292v2, lines 475–479. -/
theorem one_sub_kyFanNorm_qutritMiddleMarginal_ge {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hflag : p / (2 : ℝ) ^ N ≤ 1 - p) (D : ℕ) :
    ((2 : ℝ) ^ N - ((D : ℝ) - 1)) * p / (2 : ℝ) ^ N ≤
      1 - (qutritMiddleMarginal_posSemidef N p).isHermitian.kyFanNorm D := by
  have hb := kyFanNorm_qutritMiddleMarginal_le hN hp hp' hflag D
  have hpow : (2 : ℝ) ^ N ≠ 0 := by positivity
  have heq : ((2 : ℝ) ^ N - ((D : ℝ) - 1)) * p / (2 : ℝ) ^ N =
      p - ((D : ℝ) - 1) * (p / (2 : ℝ) ^ N) := by
    field_simp
  rw [heq]
  linarith

/-- For the source family, the flag is a largest Schmidt weight for `N ≥ 2`.
Source: arXiv:0705.0292v2, lines 421–425 and 475–479. -/
theorem qutritFamily_flagWeight_ge {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ)⁻¹ / (2 : ℝ) ^ N ≤ 1 - (N : ℝ)⁻¹ := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : (N : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn
  have hp : (N : ℝ)⁻¹ / (2 : ℝ) ^ N ≤ (N : ℝ)⁻¹ :=
    div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  linarith

/-- The discarded middle-cut mass for the source's qutrit family.
No separate hypothesis ordering its Schmidt coefficients is required.
Source: arXiv:0705.0292v2, lines 475–479. -/
theorem one_sub_kyFanNorm_qutritFamily_ge {N : ℕ} (hN : 2 ≤ N) (D : ℕ) :
    ((2 : ℝ) ^ N - ((D : ℝ) - 1)) * (N : ℝ)⁻¹ / (2 : ℝ) ^ N ≤
      1 - (qutritMiddleMarginal_posSemidef N (N : ℝ)⁻¹).isHermitian.kyFanNorm D := by
  exact one_sub_kyFanNorm_qutritMiddleMarginal_ge (by omega) (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ N by omega)))
    (qutritFamily_flagWeight_ge hN) D

/-- The expression for discarded mass at bond zero equals one. For the normalized
source state this is its full Schmidt mass. Source:
arXiv:0705.0292v2, equation `eq:magicstate` and lines 475–479. -/
theorem one_sub_kyFanNorm_qutritMiddleMarginal_zero (N : ℕ) (p : ℝ) :
    1 - (qutritMiddleMarginal_posSemidef N p).isHermitian.kyFanNorm 0 = 1 := by
  simp [Matrix.IsHermitian.kyFanNorm]

end TNLean.MPS.AreaLaw.EntropyScaling
