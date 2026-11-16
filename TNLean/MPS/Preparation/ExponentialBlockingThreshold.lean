/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InjectivityCutoff

/-!
# Exact thresholds for an assumed exponential error certificate

The bound `K N^k exp(-r q) ≤ ε` is equivalent to one explicit affine logarithmic threshold
on `q`. Its natural ceiling is the least nonnegative integral scale satisfying that
certificate. This is sharp for the scalar certificate, not a proof that a class of
inhomogeneous MPS has this error rate, or that its actual optimal blocking scale is sharp.

Source context: arXiv:2307.01696, eq. (23) and the inhomogeneous remark after eq. (19).
The source's numerical eq. (S42) is not a uniform rate theorem for all inhomogeneous chains.
-/

namespace MPSPreparation

/-- The exact real blocking threshold for a polynomial-exponential error certificate.
It concerns the certificate, not the optimal approximation error of a state family. -/
theorem mul_pow_mul_exp_neg_le_iff {K N ε r q : ℝ} {k : ℕ}
    (hK : 0 < K) (hN : 0 < N) (hε : 0 < ε) (hr : 0 < r) :
    K * (N ^ k * Real.exp (-(r * q))) ≤ ε ↔
      (Real.log K + k * Real.log N - Real.log ε) / r ≤ q := by
  have heq : K * (N ^ k * Real.exp (-(r * q))) =
      Real.exp (Real.log K + k * Real.log N - r * q) := by
    rw [Real.exp_sub, Real.exp_add, ← Real.log_pow, Real.exp_log hK,
      Real.exp_log (pow_pos hN k), Real.exp_neg]
    ring
  calc
    _ ↔ Real.exp (Real.log K + k * Real.log N - r * q) ≤ Real.exp (Real.log ε) := by
      rw [heq, Real.exp_log hε]
    _ ↔ _ := by
      rw [Real.exp_le_exp, div_le_iff₀ hr]
      constructor <;> intro h <;> nlinarith

/-- The least natural blocking scale satisfying the assumed scalar certificate is the
natural ceiling of its exact logarithmic threshold. This is not a state-preparation lower
bound. -/
theorem mul_pow_mul_exp_neg_nat_le_iff {K N ε r : ℝ} {k q : ℕ}
    (hK : 0 < K) (hN : 0 < N) (hε : 0 < ε) (hr : 0 < r) :
    K * (N ^ k * Real.exp (-(r * q))) ≤ ε ↔
      ⌈(Real.log K + k * Real.log N - Real.log ε) / r⌉₊ ≤ q := by
  rw [mul_pow_mul_exp_neg_le_iff hK hN hε hr]
  exact Nat.ceil_le.symm

/-- Retaining the number-of-blocks factor `N/q` gives the exact criterion
`r q + log q ≥ log(K N/ε)`. The rate parameter is supplied, not inferred. This scalar
identity does not assert the uniform MPS error estimate appearing in its left side.
Source context: arXiv:2307.01696, eq. (23) and Supplemental Material, eq. (S12). -/
theorem mul_div_mul_exp_neg_le_iff {K N q ε r : ℝ}
    (hK : 0 < K) (hN : 0 < N) (hq : 0 < q) (hε : 0 < ε) :
    K * (N / q * Real.exp (-(r * q))) ≤ ε ↔
      Real.log K + Real.log N - Real.log ε ≤ r * q + Real.log q := by
  have heq : K * (N / q * Real.exp (-(r * q))) =
      Real.exp (Real.log K + Real.log N - Real.log q - r * q) := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hK, Real.exp_log hN,
      Real.exp_log hq, Real.exp_neg]
    ring
  calc
    _ ↔ Real.exp (Real.log K + Real.log N - Real.log q - r * q) ≤
        Real.exp (Real.log ε) := by rw [heq, Real.exp_log hε]
    _ ↔ _ := by rw [Real.exp_le_exp]; constructor <;> intro h <;> linarith

end MPSPreparation
