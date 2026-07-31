/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Analysis.Entropy
import TNLean.Analysis.SupportCompression
import TNLean.Analysis.SupportLogJensen
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The order-two sandwiched trace functional

This file introduces only the order-two trace functional
\[
  \operatorname{Tr}\!\left[
    \left(\omega^{-1/4}\rho\,\omega^{-1/4}\right)^2
  \right],
\]
which is the expression inside the logarithm in the order-two sandwiched
Rényi divergence for trace-one states satisfying
\(\operatorname{supp}\rho\subseteq\operatorname{supp}\omega\). Negative powers
vanish on the zero eigenspace. Outside this support domain the totalized trace
functional below remains finite, whereas the sandwiched divergence is infinite.

The logarithmic comparison with quantum relative entropy requires the
monotonicity in the order of the sandwiched Rényi divergence. That analytic
result is not asserted here.

## Main definitions

* `TNLean.sandwichedRenyiTwoTrace` — the order-two sandwiched trace functional.

## Main results

* `TNLean.sandwichedRenyiTwoTrace_nonneg` — positivity on
  positive-semidefinite arguments.
* `TNLean.posDef_rpow_neg_quarter_mul_self` — the faithful identity
  \(\omega^{-1/4}\omega^{-1/4}=\omega^{-1/2}\).
* `TNLean.sandwichedRenyiTwoTrace_eq_weighted` — a cyclically reordered trace
  expression for faithful \(\omega\); when \(\rho\) is Hermitian, its common
  value is the squared Hilbert--Schmidt norm of the sandwiched matrix.

## References

* Müller-Lennert, Dupuis, Szehr, Fehr, and Tomamichel,
  *On quantum Rényi entropies: a new generalization and some properties*,
  arXiv:1306.3142v4, Definition 2 and Theorem 5.
* Beigi, *Sandwiched Rényi divergence satisfies data processing inequality*,
  arXiv:1306.5920, Theorem 7.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

open scoped Matrix.Norms.L2Operator

private local instance instRenyiTwoNormedRing : NormedRing Mat :=
  Matrix.instL2OpNormedRing
private local instance instRenyiTwoNormedAlgebra : NormedAlgebra ℂ Mat :=
  Matrix.instL2OpNormedAlgebra
private local instance instRenyiTwoCStarRing : CStarRing Mat :=
  Matrix.instCStarRing
private local instance instRenyiTwoPartialOrder : PartialOrder Mat :=
  Matrix.instPartialOrder
private local instance instRenyiTwoStarOrderedRing : StarOrderedRing Mat :=
  Matrix.instStarOrderedRing
private local instance instRenyiTwoCStarAlgebra : CStarAlgebra Mat :=
  CStarAlgebra.mk

namespace Matrix.PosSemidef

/-- Sandwiching a positive-semidefinite matrix between equal real powers of a
positive-semidefinite matrix preserves positive semidefiniteness. -/
theorem rpow_mul_mul_rpow
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef) (r : ℝ) :
    (ω ^ r * ρ * ω ^ r).PosSemidef := by
  have hωr_nonneg : 0 ≤ ω ^ r := by
    rw [CFC.rpow_eq_cfc_real hω.nonneg]
    exact cfc_nonneg fun x hx ↦
      Real.rpow_nonneg (spectrum_nonneg_of_nonneg hω.nonneg hx) r
  have hωr : (ω ^ r).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hωr_nonneg
  simpa only [hωr.isHermitian.eq] using hρ.mul_mul_conjTranspose_same (ω ^ r)

end Matrix.PosSemidef

namespace TNLean

/-- The order-two sandwiched trace functional
\(\operatorname{Re}\operatorname{Tr}[(\omega^{-1/4}\rho\omega^{-1/4})^2]\).

For positive-semidefinite matrices the real part is redundant. When the
matrices have trace one and
\(\operatorname{supp}\rho\subseteq\operatorname{supp}\omega\), its logarithm
is the order-two sandwiched Rényi divergence. The negative power is zero on the
zero eigenspace, so this totalized functional remains finite outside that
support domain and must not there be identified with the divergence; see
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2 and lines 94--96. -/
noncomputable def sandwichedRenyiTwoTrace (ρ ω : Mat) : ℝ :=
  let q := ω ^ (-(1 / 4 : ℝ))
  (Matrix.trace ((q * ρ * q) * (q * ρ * q))).re

/-- The order-two sandwiched trace functional is nonnegative on
positive-semidefinite arguments.

This is the positivity of the expression in Müller-Lennert et al.,
arXiv:1306.3142v4, Definition 2, specialized to order two. -/
theorem sandwichedRenyiTwoTrace_nonneg
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef) :
    0 ≤ sandwichedRenyiTwoTrace ρ ω := by
  let q := ω ^ (-(1 / 4 : ℝ))
  have hX : (q * ρ * q).PosSemidef :=
    _root_.Matrix.PosSemidef.rpow_mul_mul_rpow hρ hω (-(1 / 4 : ℝ))
  exact (Complex.nonneg_iff.mp (hX.trace_mul_nonneg hX)).1

/-- For a positive-definite matrix, two inverse quarter-powers multiply to the
inverse square root.

This is the exponent identity used in the order-two specialization of
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2. -/
theorem posDef_rpow_neg_quarter_mul_self
    {ω : Mat} (hω : ω.PosDef) :
    ω ^ (-(1 / 4 : ℝ)) * ω ^ (-(1 / 4 : ℝ)) = ω ^ (-(1 / 2 : ℝ)) := by
  rw [← CFC.rpow_add hω.isUnit]
  congr 1
  ring

/-- For faithful \(\omega\), the order-two sandwiched trace satisfies the
algebraic identity
\(\operatorname{Re}\operatorname{Tr}
  (\rho\omega^{-1/2}\rho\omega^{-1/2})\).

No Hermiticity assumption on \(\rho\) is needed for this cyclic trace identity.
When \(\rho\) is Hermitian, in particular when it is positive semidefinite,
\(\omega^{-1/4}\rho\omega^{-1/4}\) is Hermitian, and the common value is its
squared Hilbert--Schmidt norm. This is the order-two expression in
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2. -/
theorem sandwichedRenyiTwoTrace_eq_weighted
    {ρ ω : Mat} (hω : ω.PosDef) :
    sandwichedRenyiTwoTrace ρ ω =
      (Matrix.trace (ρ * ω ^ (-(1 / 2 : ℝ)) * ρ * ω ^ (-(1 / 2 : ℝ)))).re := by
  rw [sandwichedRenyiTwoTrace]
  let q := ω ^ (-(1 / 4 : ℝ))
  have hq : q * q = ω ^ (-(1 / 2 : ℝ)) :=
    posDef_rpow_neg_quarter_mul_self hω
  have hcycle :
      Matrix.trace ((q * ρ * q) * (q * ρ * q)) =
        Matrix.trace (ρ * (q * q) * ρ * (q * q)) := by
    calc
      Matrix.trace ((q * ρ * q) * (q * ρ * q)) =
          Matrix.trace (q * (ρ * q * q * ρ * q)) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((ρ * q * q * ρ * q) * q) :=
        Matrix.trace_mul_comm q _
      _ = Matrix.trace (ρ * (q * q) * ρ * (q * q)) := by
        congr 1
        simp only [Matrix.mul_assoc]
  rw [hcycle, hq]

/-- For a positive-semidefinite trace-one state and a faithful reference,
Umegaki relative entropy is bounded by the logarithm of the order-two
sandwiched trace.

This is the finite-dimensional faithful-reference comparison
\[
  D(\rho\Vert\omega)
    \leq \log\operatorname{Tr}(\rho\,\omega^{-1/2}\rho\,\omega^{-1/2}).
\]
The proof applies the support-aware Jensen inequality to the relative modular
operator \((\sqrt\rho)^T\otimes\omega^{-1/2}\) and then uses
Hilbert--Schmidt Cauchy--Schwarz on \(R\) and \(R\omega^{-1/2}R\). -/
theorem quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_posDef
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosDef) (hρtr : ρ.trace = 1) :
    quantumRelativeEntropy ρ ω ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) := by
  let R : Mat := CFC.sqrt ρ
  let T : Mat := ω ^ (-(1 / 2 : ℝ))
  let Aop : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    Matrix.kronecker (Matrix.transpose R) T
  let v : Fin D × Fin D → ℂ := Matrix.vec R
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  have hRR : R * R = ρ := by
    dsimp only [R]
    exact CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hRt : (Matrix.transpose R).PosSemidef := hR.transpose
  have hTpsd : T.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hTpd : T.PosDef := by
    have hTpsd' : (ω ^ (-(1 / 2 : ℝ))).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    apply hTpsd'.posDef_iff_isUnit.mpr
    apply IsUnit.of_mul_eq_one (ω ^ (1 / 2 : ℝ))
    rw [← CFC.rpow_add hω.isUnit]
    convert CFC.rpow_zero ω using 1
    norm_num
  have hAop : Aop.PosSemidef := hRt.kronecker hTpsd
  have hvnorm : star v ⬝ᵥ v = (1 : ℂ) := by
    dsimp only [v, R]
    rw [Matrix.star_vec_dotProduct_vec]
    have hRherm : (CFC.sqrt ρ).IsHermitian :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian
    rw [hRherm.eq, hRR, hρtr]
  have hsupport : hAop.supportProj *ᵥ v = v := by
    have hsupportA :
        hAop.supportProj = Matrix.kronecker hRt.supportProj hTpsd.supportProj :=
      hRt.supportProj_kronecker hTpsd
    rw [hsupportA, hTpd.supportProj_eq_one]
    dsimp only [v, R, T, Aop]
    rw [Matrix.kronecker, Matrix.kronecker_mulVec_vec]
    simp only [Matrix.one_mul]
    have hPRt :
        hRt.supportProj * Matrix.transpose (CFC.sqrt ρ) =
          Matrix.transpose (CFC.sqrt ρ) :=
      hRt.isHermitian.supportProj_mul_self
    have hRPt : CFC.sqrt ρ * hRt.supportProjᵀ = CFC.sqrt ρ := by
      have ht := congrArg Matrix.transpose hPRt
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using ht
    rw [hRPt]
  have hj := hAop.re_dotProduct_cfc_log_mulVec_le_log hvnorm hsupport
  have hlogAop : CFC.log Aop =
      Matrix.kronecker (CFC.log (Matrix.transpose R)) hTpsd.supportProj +
        Matrix.kronecker hRt.supportProj (CFC.log T) := by
    dsimp only [Aop]
    rw [Matrix.kronecker]
    exact Matrix.PosSemidef.cfc_log_kronecker hRt hTpsd
  have hlogT : CFC.log T = (-(1 / 2 : ℝ)) • CFC.log ω := by
    dsimp only [T]
    exact Matrix.PosDef.cfc_log_rpow hω (-(1 / 2 : ℝ))
  have hlogR : CFC.log R = (1 / 2 : ℝ) • CFC.log ρ := by
    dsimp only [R]
    exact Matrix.PosSemidef.cfc_log_sqrt hρ
  have hlogRt : CFC.log (Matrix.transpose R) = Matrix.transpose (CFC.log R) := by
    dsimp only [R]
    rw [CFC.log, CFC.log]
    rw [← Matrix.cfc_transpose hR.isHermitian Real.log]
  have htermR :
      (star v ⬝ᵥ
          ((Matrix.kronecker (CFC.log (Matrix.transpose R)) hTpsd.supportProj) *ᵥ
            v)).re =
        (1 / 2 : ℝ) * (Matrix.trace (ρ * CFC.log ρ)).re := by
    rw [hTpd.supportProj_eq_one]
    dsimp only [v, R]
    rw [Matrix.kronecker, Matrix.kronecker_mulVec_vec]
    simp only [Matrix.one_mul]
    rw [Matrix.star_vec_dotProduct_vec]
    rw [hlogRt, hlogR]
    simp only [Matrix.transpose_transpose]
    rw [hR.isHermitian.eq, ← Matrix.mul_assoc, hRR]
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp
  have htermW :
      (star v ⬝ᵥ ((Matrix.kronecker hRt.supportProj (CFC.log T)) *ᵥ v)).re =
        (-(1 / 2 : ℝ)) * (Matrix.trace (ρ * CFC.log ω)).re := by
    dsimp only [v, R]
    rw [Matrix.kronecker, Matrix.kronecker_mulVec_vec]
    rw [Matrix.star_vec_dotProduct_vec]
    have hPRt : hRt.supportProj * (CFC.sqrt ρ)ᵀ = (CFC.sqrt ρ)ᵀ :=
      hRt.isHermitian.supportProj_mul_self
    have hRPt : CFC.sqrt ρ * hRt.supportProjᵀ = CFC.sqrt ρ := by
      have ht := congrArg Matrix.transpose hPRt
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using ht
    rw [Matrix.mul_assoc (CFC.log T) (CFC.sqrt ρ) hRt.supportProjᵀ, hRPt]
    rw [hR.isHermitian.eq]
    calc
      (Matrix.trace (CFC.sqrt ρ * (CFC.log T * CFC.sqrt ρ))).re =
          (Matrix.trace ((CFC.sqrt ρ * CFC.log T) * CFC.sqrt ρ)).re := by
        rw [Matrix.mul_assoc]
      _ = (Matrix.trace (CFC.sqrt ρ * (CFC.sqrt ρ * CFC.log T))).re := by
        rw [Matrix.trace_mul_comm]
      _ = (Matrix.trace (ρ * CFC.log T)).re := by
        rw [← Matrix.mul_assoc, hRR]
      _ = (-(1 / 2 : ℝ)) * (Matrix.trace (ρ * CFC.log ω)).re := by
        rw [hlogT, Matrix.mul_smul, Matrix.trace_smul]
        simp
  have hleft :
      (star v ⬝ᵥ (CFC.log Aop *ᵥ v)).re =
        (1 / 2 : ℝ) * quantumRelativeEntropy ρ ω := by
    rw [hlogAop, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    rw [htermR, htermW, quantumRelativeEntropy_eq_trace_mul_log_sub]
    ring
  have hrealInner (x y : EuclideanSpace ℂ (Fin D × Fin D)) :
      inner ℝ x y = (inner ℂ x y).re := by
    simp [PiLp.inner_apply, RCLike.inner_apply, Complex.inner]
  let X : EuclideanSpace ℂ (Fin D × Fin D) :=
    Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) R
  let Y : EuclideanSpace ℂ (Fin D × Fin D) :=
    Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (R * T * R)
  have hmoment_inner :
      (star v ⬝ᵥ (Aop *ᵥ v)).re = inner ℝ X Y := by
    dsimp only [v, Aop, X, Y]
    rw [Matrix.kronecker]
    rw [Matrix.kronecker_mulVec_vec]
    rw [Matrix.star_vec_dotProduct_vec]
    rw [hrealInner, Matrix.inner_frobeniusEquivEuclidean]
    rw [hR.isHermitian.eq]
    rw [Matrix.transpose_transpose]
    calc
      (Matrix.trace (R * (T * R * R))).re =
          (Matrix.trace ((R * T * R) * R)).re := by
        simp only [Matrix.mul_assoc]
      _ = (Matrix.trace (R * (R * T * R))).re := by
        rw [Matrix.trace_mul_comm]
  have hXX : inner ℝ X X = 1 := by
    dsimp only [X, R]
    rw [hrealInner, Matrix.inner_frobeniusEquivEuclidean]
    rw [hR.isHermitian.eq, hRR, hρtr]
    simp
  have hYY : inner ℝ Y Y = sandwichedRenyiTwoTrace ρ ω := by
    dsimp only [Y]
    rw [hrealInner, Matrix.inner_frobeniusEquivEuclidean]
    have hTherm : T.IsHermitian := hTpsd.isHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR.isHermitian.eq, hTherm.eq]
    rw [sandwichedRenyiTwoTrace_eq_weighted hω]
    dsimp only [T]
    calc
      (Matrix.trace ((R * (ω ^ (-(1 / 2 : ℝ)) * R)) *
            (R * ω ^ (-(1 / 2 : ℝ)) * R))).re =
          (Matrix.trace (R * (ω ^ (-(1 / 2 : ℝ)) * (R * R) *
            ω ^ (-(1 / 2 : ℝ)) * R))).re := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = (Matrix.trace (R * (ω ^ (-(1 / 2 : ℝ)) * ρ *
            ω ^ (-(1 / 2 : ℝ)) * R))).re := by
        rw [hRR]
      _ = (Matrix.trace ((ω ^ (-(1 / 2 : ℝ)) * ρ *
            ω ^ (-(1 / 2 : ℝ)) * R) * R)).re := by
        rw [Matrix.trace_mul_comm]
      _ = (Matrix.trace ((ω ^ (-(1 / 2 : ℝ)) * ρ *
            ω ^ (-(1 / 2 : ℝ))) * ρ)).re := by
        rw [← hRR]
        simp only [Matrix.mul_assoc]
      _ = (Matrix.trace (ρ * (ω ^ (-(1 / 2 : ℝ)) * ρ *
            ω ^ (-(1 / 2 : ℝ))))).re := by
        rw [Matrix.trace_mul_comm]
      _ = (Matrix.trace (ρ * ω ^ (-(1 / 2 : ℝ)) * ρ *
            ω ^ (-(1 / 2 : ℝ)))).re := by
        simp only [Matrix.mul_assoc]
  have hm_sq_le : ((star v ⬝ᵥ (Aop *ᵥ v)).re) ^ 2 ≤
      sandwichedRenyiTwoTrace ρ ω := by
    have hcs := real_inner_mul_inner_self_le X Y
    have hcs' : inner ℝ X Y * inner ℝ X Y ≤ sandwichedRenyiTwoTrace ρ ω := by
      calc
        inner ℝ X Y * inner ℝ X Y ≤ inner ℝ X X * inner ℝ Y Y := hcs
        _ = sandwichedRenyiTwoTrace ρ ω := by rw [hXX, hYY, one_mul]
    simpa [pow_two, hmoment_inner] using hcs'
  have hv_ne : v ≠ 0 := by
    intro hv0
    have hzero : star v ⬝ᵥ v = (0 : ℂ) := by
      rw [hv0]
      simp
    rw [hzero] at hvnorm
    norm_num at hvnorm
  have hm_pos_complex : (0 : ℂ) < star v ⬝ᵥ (Aop *ᵥ v) :=
    Matrix.PosSemidef.dotProduct_mulVec_pos_of_supportProj_fixed hAop hv_ne
      (by simpa only [] using hsupport)
  have hm_pos : 0 < (star v ⬝ᵥ (Aop *ᵥ v)).re :=
    (Complex.lt_def.mp hm_pos_complex).1
  let m : ℝ := (star v ⬝ᵥ (Aop *ᵥ v)).re
  have hhalf_le_logm : (1 / 2 : ℝ) * quantumRelativeEntropy ρ ω ≤ Real.log m := by
    dsimp only [m]
    rw [← hleft]
    exact hj
  have hm_sq_le' : m ^ 2 ≤ sandwichedRenyiTwoTrace ρ ω := by
    dsimp only [m]
    exact hm_sq_le
  have hm_pos' : 0 < m := by
    dsimp only [m]
    exact hm_pos
  have hlog_sq_le : Real.log (m ^ 2) ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) :=
    Real.log_le_log (sq_pos_of_pos hm_pos') hm_sq_le'
  have htwolog_eq : 2 * Real.log m = Real.log (m ^ 2) := by
    rw [pow_two, Real.log_mul hm_pos'.ne' hm_pos'.ne']
    ring
  have hD_le_twolog : quantumRelativeEntropy ρ ω ≤ 2 * Real.log m := by
    nlinarith
  calc
    quantumRelativeEntropy ρ ω ≤ 2 * Real.log m := hD_le_twolog
    _ = Real.log (m ^ 2) := htwolog_eq
    _ ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) := hlog_sq_le

end TNLean

end
