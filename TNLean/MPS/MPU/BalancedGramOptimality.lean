/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.BalancedGramMetrics
import QICLean.Algebra.FrobeniusHilbert
import QICLean.Analysis.MatrixSqrt

/-!
# Optimality of the balanced positive Gram contraction

If positive definite bond metrics satisfy `Tr(PQ) = 1`, their inverse
trace pairing is at least the square of the bond dimension. The dual metric
`Q = P⁻¹/r` attains this bound. This is a consequence of the balanced
normalization in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The comparison concerns the contraction within this positive-metric merging
scheme. It gives no lower bound on the complexity of arbitrary quantum
circuits.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPUCircuit

variable {ι : Type*} [Fintype ι]

open scoped Classical in
private theorem sqrt_product_gram_trace {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    ((CFC.sqrt Q * CFC.sqrt P)ᴴ * (CFC.sqrt Q * CFC.sqrt P)).trace =
      (P * Q).trace := by
  rw [conjTranspose_mul, conjTranspose_cfc_sqrt, conjTranspose_cfc_sqrt,
    ← Matrix.mul_assoc (CFC.sqrt P * CFC.sqrt Q) (CFC.sqrt Q) (CFC.sqrt P),
    Matrix.mul_assoc (CFC.sqrt P) (CFC.sqrt Q) (CFC.sqrt Q),
    CFC.sqrt_mul_sqrt_self Q hQ.nonneg, trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self P hP.nonneg]

variable [DecidableEq ι]

/-- For normalized positive bond metrics, the inverse trace pairing is
at least the square of the bond dimension. No commutation assumption on
the metrics is required. Derived consequence of the balanced contraction
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_sq_le_trace_inv_mul_inv_of_trace_mul_eq_one
    {P Q : Matrix ι ι ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hnorm : (P * Q).trace = 1) :
    (Fintype.card ι : ℝ) ^ 2 ≤ (Q⁻¹ * P⁻¹).trace.re := by
  let X := CFC.sqrt Q * CFC.sqrt P
  let Y := CFC.sqrt Q⁻¹ * CFC.sqrt P⁻¹
  have hXY : Xᴴ * Y = 1 := by
    dsimp [X, Y]
    rw [conjTranspose_mul, conjTranspose_cfc_sqrt, conjTranspose_cfc_sqrt,
      ← hQ.posSemidef.inv_sqrt, ← hP.posSemidef.inv_sqrt]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hQ.isUnit_det_cfc_sqrt,
      Matrix.mul_nonsing_inv _ hP.isUnit_det_cfc_sqrt]
  have hYX : Yᴴ * X = 1 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one]
      using congrArg Matrix.conjTranspose hXY
  have hXX : (Xᴴ * X).trace = 1 :=
    (sqrt_product_gram_trace hP.posSemidef hQ.posSemidef).trans hnorm
  have hYY : (Yᴴ * Y).trace = (Q⁻¹ * P⁻¹).trace :=
    (sqrt_product_gram_trace hP.inv.posSemidef hQ.inv.posSemidef).trans
      (trace_mul_comm _ _)
  have hcs := inner_mul_inner_self_le (𝕜 := ℂ)
    (frobeniusEquivEuclidean ι ι X) (frobeniusEquivEuclidean ι ι Y)
  simp only [inner_frobeniusEquivEuclidean, hXY, hYX, hXX, hYY,
    trace_one] at hcs
  simpa [pow_two] using hcs

/-- The dual Gram metric attains the dimension-squared inverse trace
pairing. Derived consequence of the balanced normalization in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem trace_dualGramMetric_inv_mul_inv_re [Nonempty ι]
    {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ((dualGramMetric P)⁻¹ * P⁻¹).trace.re = (Fintype.card ι : ℝ) ^ 2 := by
  rw [trace_dualGramMetric_inv_mul_inv hP]
  simp [pow_two, Complex.mul_re]

/-- The dual Gram metric is feasible and minimizes the inverse trace
pairing among positive definite metrics with `Tr(PQ) = 1`. This is
optimality within the positive-metric joining scheme, rather than a
lower bound for arbitrary quantum circuits. Derived consequence of
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem dualGramMetric_minimizes_inverse_trace [Nonempty ι]
    {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    (dualGramMetric P).PosDef ∧ (P * dualGramMetric P).trace = 1 ∧
      ∀ Q : Matrix ι ι ℂ, Q.PosDef → (P * Q).trace = 1 →
        ((dualGramMetric P)⁻¹ * P⁻¹).trace.re ≤ (Q⁻¹ * P⁻¹).trace.re := by
  refine ⟨dualGramMetric_posDef hP,
    trace_mul_dualGramMetric_eq_one hP (by simp), ?_⟩
  intro Q hQ hnorm
  rw [trace_dualGramMetric_inv_mul_inv_re hP]
  exact card_sq_le_trace_inv_mul_inv_of_trace_mul_eq_one hP hQ hnorm

end MPUCircuit
