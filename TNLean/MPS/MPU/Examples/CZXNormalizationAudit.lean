/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Basic
import TNLean.MPS.Examples.GHZ
import TNLean.Algebra.ComplexSqrt

/-!
# A normalization obstruction in the printed CZX tensor

**Local fix (not implemented here):** arXiv:1703.09188, Example `example:czx`,
lines 1914–1930, prints a normalized Hadamard in an unscaled periodic
contraction. That literal tensor is not an MPU. The 2025 diagram
(arXiv:2502.20257, `eq:MPU_CZX`) instead uses the unnormalized matrix of
`eq:deltas` and two additional physical Z gates. See
`docs/paper-gaps/mpu_czx_tensor_normalization.tex`. This file checks only the
2017 obstruction; it does not define the shared CZX MPU or identify the
2025 tensor with an undecorated block.
-/

noncomputable section
open scoped Matrix
namespace MPOTensor.CZX

/-- The literal printed tensor of arXiv:1703.09188, Example `example:czx`
(lines 1923–1929). This is a counterexample witness, not the shared CZX MPU. -/
def printed2017Tensor : MPOTensor 2 2 :=
  fun u d l r ↦ MPSTensor.pauliX u d * (if u = l then 1 else 0) *
    ((↑(Real.sqrt 2) : ℂ)⁻¹ * (-1) ^ (l.val * r.val))

/-- At two sites the all-zero output row has just one entry, of value one half.
Source: direct contraction of arXiv:1703.09188, `example:czx`. -/
theorem printed2017Tensor_two_zero_row (τ : Fin 2 → Fin 2) :
    mpo printed2017Tensor 2 (fun _ ↦ 0) τ =
      if τ = (fun _ ↦ 1) then (1 / 2 : ℂ) else 0 := by
  have hs : (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← pow_two, Complex.ofReal_sqrt_sq 2 (by norm_num)]
    norm_num
  generalize ha : τ 0 = a
  generalize hb : τ 1 = b
  have ht : τ = ![a, b] := by
    ext i; fin_cases i <;> simp_all
  subst τ
  fin_cases a <;> fin_cases b <;>
    norm_num [mpo, mpoMatrixEntry, List.ofFn_succ, evalWord_cons, evalWord_nil,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, printed2017Tensor,
      MPSTensor.pauliX, hs, funext_iff, Fin.forall_fin_two]

/-- The literal normalized-Hadamard tensor in arXiv:1703.09188,
`example:czx`, fails the MPU predicate already at length two. -/
theorem printed2017Tensor_not_isMPU : ¬ IsMPU printed2017Tensor := by
  intro h
  have he := congrFun (congrFun (h.mpo_mul_conjTranspose_mpo (by decide : 1 < 2))
    (fun _ ↦ 0)) (fun _ ↦ 0)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    printed2017Tensor_two_zero_row] at he
  norm_num [Matrix.one_apply, Fintype.sum_ite_eq', Fintype.sum_ite_eq, map_ofNat] at he

end MPOTensor.CZX
