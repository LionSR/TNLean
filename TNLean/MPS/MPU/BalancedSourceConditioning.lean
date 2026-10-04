/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.BalancedGramMetrics
import Mathlib.Analysis.Real.Sqrt

/-!
# The source transpose convention for balanced joining metrics

In the left-row, right-column virtual convention, the source interval
amplitude is `L * A * Rᵀ`. The balanced metrics correspond to
`L² = P` and `R² = Qᵀ`, where `Q` is the inverse of `P` divided by the
bond dimension. The source squared joining norm therefore has trace
`trace ((Q⁻¹)ᵀ * (P⁻¹)ᵀ)`, whose positive square root is the dimension.

This is a derived consequence of the determinant normalization in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The source expression is
arXiv:2508.08160, `eq:def_q_k`, local source lines 1375--1379. The appendix
at lines 2123--2124 restricts its optimization to physical cap-Gram sets;
these results do not assert membership of the balanced metrics in those
sets or a bound on that restricted infimum. They also do not assert a
circuit-complexity lower bound.
-/

open Matrix
open scoped ComplexOrder

namespace MPUCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reversing both inverse matrices by transpose gives the source's
squared joining-norm trace in the ordinary virtual-matrix convention.
Source: arXiv:2508.08160, `eq:def_q_k`, local source lines 1375--1379;
transpose correspondence derived in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem trace_transpose_inv_mul_transpose_inv (P Q : Matrix ι ι ℂ) :
    trace ((Q⁻¹)ᵀ * (P⁻¹)ᵀ) = trace (P⁻¹ * Q⁻¹) := by
  rw [← Matrix.transpose_mul, Matrix.trace_transpose]

/-- The balanced dual metric makes the source squared joining norm equal
to the squared bond dimension. This identity is derived from positivity,
without an assumed trace or conditioning bound. Source: the derived
normalization in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, compared with
arXiv:2508.08160, `eq:def_q_k`, local source lines 1375--1379. -/
theorem trace_transpose_dualGramMetric_inv_mul_transpose_inv [Nonempty ι]
    {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    trace (((dualGramMetric P)⁻¹)ᵀ * (P⁻¹)ᵀ) = (Fintype.card ι : ℂ) ^ 2 := by
  rw [trace_transpose_inv_mul_transpose_inv, Matrix.trace_mul_comm]
  exact trace_dualGramMetric_inv_mul_inv hP

/-- The positive square root of the real source squared joining-norm
trace is exactly the bond dimension for the balanced metrics. This is
an explicit candidate norm, without a claim about the cap-restricted
infimum in arXiv:2508.08160, local source lines 2123--2124.
Source: the derived consequence of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem sqrt_re_trace_transpose_dualGramMetric_inv_mul_transpose_inv [Nonempty ι]
    {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    Real.sqrt (trace (((dualGramMetric P)⁻¹)ᵀ * (P⁻¹)ᵀ)).re =
      (Fintype.card ι : ℝ) := by
  rw [trace_transpose_dualGramMetric_inv_mul_transpose_inv hP]
  have hreal : ((Fintype.card ι : ℂ) ^ 2).re = (Fintype.card ι : ℝ) ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [hreal, Real.sqrt_sq (Nat.cast_nonneg _)]

end MPUCircuit
