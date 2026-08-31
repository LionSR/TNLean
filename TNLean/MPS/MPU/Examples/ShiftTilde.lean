/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.MPS.MPDO.SitewisePhysicalMatrix
import TNLean.MPS.MPU.Examples.Shift
import TNLean.MPS.MPU.KetLeftMul

/-!
# Swap-transformed shift matrix product unitaries

The swap transformation in arXiv:1703.09188, equations `threeMPU2`
(lines 2046--2062), multiplies every local physical operator on the left by
the swap of the two spins. This file defines the three transformed tensors,
proves their exact finite-chain formulas, and proves that they remain MPUs.

No symmetry-phase classification is asserted here.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- The local physical swap on the two $d$-dimensional spins, in the flattened
`Fin (d * d)` coordinates used by `MPOTensor`. -/
noncomputable def shiftPhysicalSwap (d : ℕ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  Equiv.Perm.permMatrix ℂ (bondPairSwapEquiv d)

/-- The flattened local matrix exchanges the two spin coordinates. -/
@[simp] theorem shiftPhysicalSwap_apply (d : ℕ) (i j k l : Fin d) :
    shiftPhysicalSwap d (finProdFinEquiv (i, j)) (finProdFinEquiv (k, l)) =
      if i = l ∧ j = k then 1 else 0 := by
  simp [shiftPhysicalSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix,
    bondPairSwapEquiv_apply, bondPairSwap_finProdFinEquiv, and_comm]

/-- The local physical swap is unitary. -/
theorem shiftPhysicalSwap_mem_unitaryGroup (d : ℕ) :
    shiftPhysicalSwap d ∈ Matrix.unitaryGroup (Fin (d * d)) ℂ :=
  Equiv.Perm.permMatrix_mem_unitaryGroup (bondPairSwapEquiv d)

/-- The transformed tensor generating
$\widetilde U_1^{(N)} = \mathbb S^{\otimes N} U_1^{(N)}$. -/
noncomputable def shiftExampleTildeU₁ (d : ℕ) : MPOTensor (d * d) 1 :=
  (shiftExampleU₁ d).ketLeftMul (shiftPhysicalSwap d)

/-- The transformed tensor generating
$\widetilde U_2^{(N)} = \mathbb S^{\otimes N} U_2^{(N)}$. -/
noncomputable def shiftExampleTildeU₂ (d : ℕ) : MPOTensor (d * d) (d * d) :=
  (shiftExampleU₂ d).ketLeftMul (shiftPhysicalSwap d)

/-- The transformed tensor generating
$\widetilde U_3^{(N)} = \mathbb S^{\otimes N} U_3^{(N)}$. -/
noncomputable def shiftExampleTildeU₃ (d : ℕ) : MPOTensor (d * d) (d * d) :=
  (shiftExampleU₃ d).ketLeftMul (shiftPhysicalSwap d)

/-- Exact all-chain formula for $\widetilde U_1^{(N)}=\mathbb S^{\otimes N}$. -/
theorem mpo_shiftExampleTildeU₁ (d N : ℕ) :
    mpo (shiftExampleTildeU₁ d) N = sitewisePhysicalMatrix (shiftPhysicalSwap d) N := by
  rw [shiftExampleTildeU₁, mpo_ketLeftMul, mpo_shiftExampleU₁, Matrix.mul_one]

/-- Exact all-chain formula for
$\widetilde U_2^{(N)}=\mathbb S^{\otimes N}(T^{(N)\dagger}\otimes T^{(N)})$. -/
theorem mpo_shiftExampleTildeU₂ (d N : ℕ) [NeZero N] :
    mpo (shiftExampleTildeU₂ d) N =
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N *
        Matrix.reindex (finTupleProdEquiv N d d).symm
          (finTupleProdEquiv N d d).symm
          ((Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ ⊗ₖ
            Equiv.Perm.permMatrix ℂ (rotateConfig N d)) := by
  rw [shiftExampleTildeU₂, mpo_ketLeftMul, mpo_shiftExampleU₂]

/-- Exact all-chain formula for
$\widetilde U_3^{(N)}=\mathbb S^{\otimes N}(T^{(N)}\otimes T^{(N)\dagger})$. -/
theorem mpo_shiftExampleTildeU₃ (d N : ℕ) [NeZero N] :
    mpo (shiftExampleTildeU₃ d) N =
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N *
        Matrix.reindex (finTupleProdEquiv N d d).symm
          (finTupleProdEquiv N d d).symm
          (Equiv.Perm.permMatrix ℂ (rotateConfig N d) ⊗ₖ
            (Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ) := by
  rw [shiftExampleTildeU₃, mpo_ketLeftMul, mpo_shiftExampleU₃]

/-- $\widetilde U_1$ is an MPU. -/
theorem shiftExampleTildeU₁_isMPU (d : ℕ) : IsMPU (shiftExampleTildeU₁ d) :=
  (shiftExampleU₁_isMPU d).ketLeftMul (shiftPhysicalSwap_mem_unitaryGroup d)

/-- $\widetilde U_2$ is an MPU. -/
theorem shiftExampleTildeU₂_isMPU (d : ℕ) : IsMPU (shiftExampleTildeU₂ d) :=
  (shiftExampleU₂_isMPU d).ketLeftMul (shiftPhysicalSwap_mem_unitaryGroup d)

/-- $\widetilde U_3$ is an MPU. -/
theorem shiftExampleTildeU₃_isMPU (d : ℕ) : IsMPU (shiftExampleTildeU₃ d) :=
  (shiftExampleU₃_isMPU d).ketLeftMul (shiftPhysicalSwap_mem_unitaryGroup d)

end MPOTensor
