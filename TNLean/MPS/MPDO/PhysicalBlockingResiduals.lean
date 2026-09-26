/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# Physical blocking with residual sites

A finite MPO word need not have length divisible by a blocking length. This
module separates an arbitrary residual prefix and suffix from the complete
blocks in the middle. The residual matrix products remain inside the virtual
trace. This extends the closed-chain physical blocking used in
arXiv:1606.00608, Appendix C.4, lines 1952--2017.
-/

namespace MPOTensor

/-- The matrix entry of a closed MPO chain is the trace of its residual prefix,
blocked middle, and residual suffix products. The two residual factors are
retained even when the total chain length is not divisible by the blocking
length. This extends the closed-chain blocking identity of arXiv:1606.00608,
Appendix C.4, lines 1952--2017. -/
theorem mpo_apply_prefix_blockTensor_suffix
    {d D : ℕ} (U : MPOTensor d D) (L p m s : ℕ)
    (i₀ j₀ : Fin p → Fin d)
    (i₁ j₁ : Fin m → Fin (MPSTensor.blockPhysDim d L))
    (i₂ j₂ : Fin s → Fin d) :
    mpo U (p + (m * L + s))
        (Fin.append i₀ (Fin.append (MPSTensor.blockedConfigEquiv d m L i₁) i₂))
        (Fin.append j₀ (Fin.append (MPSTensor.blockedConfigEquiv d m L j₁) j₂)) =
      Matrix.trace
        (evalWord U (List.ofFn i₀) (List.ofFn j₀) *
          evalWord (blockTensor U L) (List.ofFn i₁) (List.ofFn j₁) *
          evalWord U (List.ofFn i₂) (List.ofFn j₂)) := by
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_fin_append]
  rw [evalWord_append U (List.ofFn i₀) (List.ofFn j₀)
    (List.ofFn ((MPSTensor.blockedConfigEquiv d m L) i₁) ++ List.ofFn i₂)
    (List.ofFn ((MPSTensor.blockedConfigEquiv d m L) j₁) ++ List.ofFn j₂) (by simp)]
  rw [evalWord_append U
    (List.ofFn ((MPSTensor.blockedConfigEquiv d m L) i₁))
    (List.ofFn ((MPSTensor.blockedConfigEquiv d m L) j₁))
    (List.ofFn i₂) (List.ofFn j₂) (by simp)]
  rw [MPSTensor.ofFn_blockedConfigEquiv, MPSTensor.ofFn_blockedConfigEquiv]
  rw [← evalWord_blockTensor_ofFn U L i₁ j₁]
  rw [Matrix.mul_assoc]

end MPOTensor
