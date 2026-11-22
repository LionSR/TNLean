/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-!
# Boundary Gram matrices for a parity rotation

For the factorization `I ⊗ c I + P ⊗ i s Q`, with Hermitian involutions
`P,Q`, the boundary Gram matrices are `[[1,x],[x,1]]` and
`[[c²,i c s y],[-i c s y,s²]]`. The real parameters `x,y` are expectations
of the two involutions in the exterior density operators.

This module computes the trace of the inverse Gram product. It does not
formalize the identification of the matrices with all admissible boundary
choices or a circuit implementation of the parity rotation.

Source context: arXiv:2508.08160v2, `references/2508.08160/main.tex`,
boundary Gram sets in Lemma `lem:isometries`, lines 1756--1818, and the
conditioning infimum `eq:def_q_k`, lines 1373--1378.
The example and its mathematical derivation are recorded in
`docs/audits/2026-10-02_mpu_tree_conditioning.tex`.
-/

open Matrix

namespace MPUCircuit

/-- Left boundary Gram matrix for the factors `I,P` of a parity rotation. -/
def parityLeftGram (x : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, x; x, 1]

/-- Right boundary Gram matrix for the factors `c I,i s Q` of a parity rotation. -/
def parityRightGram (c s y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![c ^ 2, Complex.I * c * s * y; -Complex.I * c * s * y, s ^ 2]

/-- The trace of the inverse Gram product has no mixed term in the exterior
expectations, because the left off-diagonal entries are symmetric and the
right off-diagonal entries are antisymmetric.

The identity holds algebraically over the complex numbers; interpreting the
matrices as positive Gram matrices additionally requires real parameters.
Source context: `eq:def_q_k` in arXiv:2508.08160v2. -/
theorem trace_inverse_parityGrams (c s x y : ℂ) :
    trace ((parityRightGram c s y)⁻¹ * ((parityLeftGram x)⁻¹)ᵀ) =
      (c ^ 2 + s ^ 2) / (c ^ 2 * s ^ 2 * (1 - x ^ 2) * (1 - y ^ 2)) := by
  rw [Matrix.inv_def, Matrix.inv_def]
  simp [parityRightGram, parityLeftGram, Matrix.det_fin_two,
    Matrix.adjugate_fin_two, Ring.inverse_eq_inv, Matrix.trace_fin_two,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  rw [show c ^ 2 * s ^ 2 - c ^ 2 * s ^ 2 * y ^ 2 +
      c ^ 2 * s ^ 2 * y ^ 2 * x ^ 2 - c ^ 2 * s ^ 2 * x ^ 2 =
      (c ^ 2 * s ^ 2 - c ^ 2 * s ^ 2 * y ^ 2) * (1 - x ^ 2) by ring]
  rw [_root_.mul_inv_rev]
  ring

end MPUCircuit
