/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.MaximalSupport

/-!
# The support of a maximum-rank fixed point carries every fixed point

Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012) quantifies over an arbitrary
maximum-rank fixed-point density matrix. The results here transfer the maximal-support
property from the constructed witness of
`Kraus.exists_maximalSupport_fixedPoint` to every fixed point of maximum rank: if $\rho$
is a positive semidefinite fixed point of the trace-preserving Kraus map $T$ whose rank
bounds the rank of every fixed-point density matrix, then the support projection $Q$ of
$\rho$ satisfies $Q X Q = X$ for every fixed point $X$ of $T$. Consequently conjugation by
$\sqrt{\rho}$ maps the weighted corner carrier of
`Kraus.weightedCornerFixedPointsStarSubalgebra` onto the full fixed-point set at every
such $\rho$, which realizes the conjugated set
$\rho^{-1/2}\,\{X \mid T(X) = X\}\,\rho^{-1/2}$ of the corollary, with the inverse square
root taken on the support of $\rho$.

The comparison with the constructed witness $\rho_0$ goes through the rank: the support
projection of a positive semidefinite matrix has the same rank as the matrix, and its
trace is that rank. From $Q_0 \rho Q_0 = \rho$ the rank of $\rho$ is at most that of
$\rho_0$; maximality applied to the normalization of $\rho_0$ gives the reverse
inequality; and two orthogonal projections $P \preceq Q_0$ (in the sense $Q_0 P = P$)
with equal traces are equal, so the support projections coincide.

## Main results

* `Kraus.rank_stationaryProj` -- the support projection of a positive semidefinite matrix
  has the rank of the matrix.
* `Kraus.trace_stationaryProj` -- the trace of the support projection is the rank.
* `Kraus.maximalSupport_of_maximalRank` -- the support of a fixed point of maximum rank
  carries every fixed point.
* `Kraus.exists_weightedCorner_sqrt_eq_of_maximalRank` -- at every fixed point of maximum
  rank, conjugation by the square root maps the weighted corner carrier onto the full
  fixed-point set.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **The support projection has the rank of the matrix.** For positive semidefinite
$\rho$ with spectral decomposition $\rho = U\,\mathrm{diag}(\lambda)\,U^{\dagger}$, the
support projection is $U\,\mathrm{diag}(\mathbf 1_{\lambda > 0})\,U^{\dagger}$, and both
ranks count the indices with $\lambda_i \neq 0$, which for nonnegative eigenvalues are
the indices with $\lambda_i > 0$. -/
theorem rank_stationaryProj {ρ : Mat} (hρ_psd : ρ.PosSemidef) :
    (stationaryProj hρ_psd).rank = ρ.rank := by
  have hrank_re :=
    (isOrthogonalProjection_stationaryProj hρ_psd).1.rank_eq_trace_re_of_idem
      (isOrthogonalProjection_stationaryProj hρ_psd).2
  have htrace : (stationaryProj hρ_psd).trace = (ρ.rank : ℂ) := by
    simpa [stationaryProj] using hρ_psd.supportProj_trace
  rw [htrace] at hrank_re
  exact_mod_cast hrank_re

/-- **The trace of the support projection is the rank.** In the spectral decomposition
the support projection is $U\,\mathrm{diag}(\mathbf 1_{\lambda > 0})\,U^{\dagger}$, whose
trace counts the positive eigenvalues, and for a positive semidefinite matrix that count
is the rank. -/
theorem trace_stationaryProj {ρ : Mat} (hρ_psd : ρ.PosSemidef) :
    (stationaryProj hρ_psd).trace = (ρ.rank : ℂ) := by
  simpa [stationaryProj] using hρ_psd.supportProj_trace

/-- **The support of a fixed point of maximum rank carries every fixed point.** Let $T$
be a trace-preserving Kraus map and let $\rho$ be a positive semidefinite fixed point of
$T$ whose rank bounds the rank of every fixed-point density matrix (every positive
semidefinite fixed point of unit trace). Then the support projection $Q$ of $\rho$
satisfies $Q X Q = X$ for every fixed point $X$ of $T$. In Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012) the maximum-rank fixed point is a density
matrix; unit trace of $\rho$ itself is not needed for the conclusion and is not assumed
here. The support projection of $\rho$ is compared with that of the constructed maximal
witness through the rank: the two support projections have equal traces and one absorbs
the other, so they coincide. -/
theorem maximalSupport_of_maximalRank
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ)
    (hρ_max : ∀ σ : Mat, σ.PosSemidef → σ.trace = 1 → map K σ = σ → σ.rank ≤ ρ.rank) :
    ∀ X : Mat, map K X = X →
      stationaryProj hρ_psd * X * stationaryProj hρ_psd = X := by
  classical
  obtain ⟨ρ₀, hρ₀_psd, hρ₀_fix, hmax⟩ := exists_maximalSupport_fixedPoint K h_tp
  set Q₀ : Mat := stationaryProj hρ₀_psd with hQ₀def
  set P : Mat := stationaryProj hρ_psd with hPdef
  have hQ₀herm : Q₀ᴴ = Q₀ := (isOrthogonalProjection_stationaryProj hρ₀_psd).1.eq
  have hPherm : Pᴴ = P := (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
  have hQ₀idem : Q₀ * Q₀ = Q₀ := (isOrthogonalProjection_stationaryProj hρ₀_psd).2
  have hPidem : P * P = P := (isOrthogonalProjection_stationaryProj hρ_psd).2
  rcases eq_or_ne ρ₀ 0 with hρ₀0 | hρ₀ne
  · -- Degenerate case: every fixed point vanishes, and the claim is trivial.
    have hQ₀0 : Q₀ = 0 := by
      refine Matrix.ext_of_mulVec_single fun j => ?_
      rw [hQ₀def, Matrix.zero_mulVec]
      exact MPSTensor.supportProj_mulVec_eq_zero_of_mulVec_eq_zero
        (ρ := ρ₀) (hρ := hρ₀_psd) _ (by rw [hρ₀0, Matrix.zero_mulVec])
    intro X hX
    have hX0 : X = 0 := by
      have h := hmax X hX
      rw [hQ₀0] at h
      simpa using h.symm
    rw [hX0, Matrix.mul_zero, Matrix.zero_mul]
  · -- The trace of the nonzero maximal witness is a nonzero nonnegative real number.
    have hc_nonneg : (0 : ℂ) ≤ ρ₀.trace := hρ₀_psd.trace_nonneg
    have hc_ne : ρ₀.trace ≠ 0 := by
      intro h0
      have hS_herm : (CFC.sqrt ρ₀)ᴴ = CFC.sqrt ρ₀ :=
        (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ₀)).isHermitian.eq
      have hSS : CFC.sqrt ρ₀ * CFC.sqrt ρ₀ = ρ₀ :=
        CFC.sqrt_mul_sqrt_self ρ₀ hρ₀_psd.nonneg
      have htr : ((CFC.sqrt ρ₀)ᴴ * CFC.sqrt ρ₀).trace = 0 := by
        rw [hS_herm, hSS]
        exact h0
      have hsq0 : CFC.sqrt ρ₀ = 0 :=
        Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
      exact hρ₀ne (by rw [← hSS, hsq0, Matrix.mul_zero])
    have him : ρ₀.trace.im = 0 := ((Complex.nonneg_iff.mp hc_nonneg).2).symm
    have hre_nonneg : 0 ≤ ρ₀.trace.re := (Complex.nonneg_iff.mp hc_nonneg).1
    have hre_ne : ρ₀.trace.re ≠ 0 := by
      intro h
      exact hc_ne (Complex.ext h him)
    have htr_eq : ρ₀.trace = ((ρ₀.trace.re : ℝ) : ℂ) := by
      exact Complex.ext rfl (by simp [him])
    set c : ℝ := (ρ₀.trace.re)⁻¹ with hcdef
    have hc_re_nonneg : 0 ≤ c := inv_nonneg.mpr hre_nonneg
    have hc_re_ne : c ≠ 0 := inv_ne_zero hre_ne
    -- The normalization of the maximal witness is a fixed-point density matrix.
    set σ : Mat := ((c : ℝ) : ℂ) • ρ₀ with hσdef
    have hσ_psd : σ.PosSemidef := by
      have h := hρ₀_psd.conjTranspose_mul_mul_same
        (((Real.sqrt c : ℝ) : ℂ) • (1 : Mat))
      have heq : (((Real.sqrt c : ℝ) : ℂ) • (1 : Mat))ᴴ * ρ₀ *
          (((Real.sqrt c : ℝ) : ℂ) • (1 : Mat)) = σ := by
        rw [hσdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
        congr 1
        rw [show star (((Real.sqrt c : ℝ) : ℂ)) = ((Real.sqrt c : ℝ) : ℂ) by simp]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc_re_nonneg]
      rw [← heq]
      exact h
    have hσ_tr : σ.trace = 1 := by
      rw [hσdef, Matrix.trace_smul, htr_eq, smul_eq_mul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hre_ne, Complex.ofReal_one]
    have hσ_fix : map K σ = σ := by
      rw [hσdef, map_smul, hρ₀_fix]
    have hσ_rank : σ.rank = ρ₀.rank := by
      rw [hσdef, Matrix.smul_eq_diagonal_mul]
      refine Matrix.rank_mul_eq_right_of_isUnit_det _ _ ?_
      rw [Matrix.det_diagonal, Finset.prod_const]
      exact (isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hc_re_ne)).pow _
    -- The two ranks agree.
    have h1 : ρ₀.rank ≤ ρ.rank := hσ_rank ▸ hρ_max σ hσ_psd hσ_tr hσ_fix
    have hQ₀ρQ₀ : Q₀ * ρ * Q₀ = ρ := hmax ρ hρ_fix
    have h2 : ρ.rank ≤ ρ₀.rank := by
      calc ρ.rank = (Q₀ * ρ * Q₀).rank := by rw [hQ₀ρQ₀]
        _ ≤ (Q₀ * ρ).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Q₀.rank := Matrix.rank_mul_le_left _ _
        _ = ρ₀.rank := rank_stationaryProj hρ₀_psd
    have hrank_eq : ρ.rank = ρ₀.rank := le_antisymm h2 h1
    -- The support of `ρ` is contained in the support of the maximal witness.
    have hρQ₀ : ρ * Q₀ = ρ := by
      conv_lhs => rw [← hQ₀ρQ₀]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hQ₀idem, ← Matrix.mul_assoc]
      exact hQ₀ρQ₀
    have hPQ₀ : P * Q₀ = P := by
      have hsub : P * (1 - Q₀) = 0 := by
        refine Matrix.ext_of_mulVec_single fun j => ?_
        rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
        refine MPSTensor.supportProj_mulVec_eq_zero_of_mulVec_eq_zero
          (ρ := ρ) (hρ := hρ_psd) _ ?_
        rw [Matrix.mulVec_mulVec,
          show ρ * (1 - Q₀) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, hρQ₀, sub_self],
          Matrix.zero_mulVec]
      rw [Matrix.mul_sub, Matrix.mul_one] at hsub
      exact (sub_eq_zero.mp hsub).symm
    have hQ₀P : Q₀ * P = P := by
      have h := congrArg Matrix.conjTranspose hPQ₀
      rwa [Matrix.conjTranspose_mul, hQ₀herm, hPherm] at h
    -- Two projections with equal traces, one absorbing the other, coincide.
    have hR : (Q₀ - P) * (Q₀ - P) = Q₀ - P := by
      rw [mul_sub (Q₀ - P) Q₀ P, sub_mul Q₀ P Q₀, sub_mul Q₀ P P,
        hQ₀idem, hPQ₀, hQ₀P, hPidem]
      abel
    have hRH : (Q₀ - P)ᴴ = Q₀ - P := by
      rw [Matrix.conjTranspose_sub, hQ₀herm, hPherm]
    have hRtr : ((Q₀ - P)ᴴ * (Q₀ - P)).trace = 0 := by
      rw [hRH, hR, Matrix.trace_sub, hQ₀def, hPdef, trace_stationaryProj hρ₀_psd,
        trace_stationaryProj hρ_psd, hrank_eq, sub_self]
    have hPeq : P = Q₀ := by
      have h := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hRtr
      exact (sub_eq_zero.mp h).symm
    intro X hX
    rw [hPeq]
    exact hmax X hX

/-- **Conjugation by the square root at every fixed point of maximum rank.** Let $T$ be a
trace-preserving Kraus map and let $\rho$ be a positive semidefinite fixed point of $T$
whose rank bounds the rank of every fixed-point density matrix. Then every fixed point
$X$ of $T$ arises as $X = \sqrt{\rho}\, Y \sqrt{\rho}$ for a corner-supported $Y$ with
$\sqrt{\rho}\, Y \sqrt{\rho}$ fixed by $T$: conjugation by $\sqrt{\rho}$ maps the carrier
of `Kraus.weightedCornerFixedPointsStarSubalgebra` onto the full fixed-point set, which
realizes the set $\rho^{-1/2}\,\{X \mid T(X) = X\}\,\rho^{-1/2}$ of Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012) at every fixed point of maximum rank, with
the inverse square root taken on the support of $\rho$. -/
theorem exists_weightedCorner_sqrt_eq_of_maximalRank
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ)
    (hρ_max : ∀ σ : Mat, σ.PosSemidef → σ.trace = 1 → map K σ = σ → σ.rank ≤ ρ.rank)
    {X : Mat} (hX_fix : map K X = X) :
    ∃ Y : Mat, stationaryProj hρ_psd * Y * stationaryProj hρ_psd = Y ∧
      map K (CFC.sqrt ρ * Y * CFC.sqrt ρ) = CFC.sqrt ρ * Y * CFC.sqrt ρ ∧
      CFC.sqrt ρ * Y * CFC.sqrt ρ = X :=
  exists_weightedCorner_sqrt_eq_of_fixedPoint K h_tp hρ_psd hρ_fix hX_fix
    (maximalSupport_of_maximalRank K h_tp hρ_psd hρ_fix hρ_max X hX_fix)

end Kraus
