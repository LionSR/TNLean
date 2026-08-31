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

private def shiftExampleChainSwap (d N : ℕ) : Equiv.Perm (Fin N → Fin (d * d)) :=
  (finTupleProdEquiv N d d).trans
    ((Equiv.prodComm _ _).trans (finTupleProdEquiv N d d).symm)

private def shiftExampleChainU₂ (d N : ℕ) : Equiv.Perm (Fin N → Fin (d * d)) :=
  (finTupleProdEquiv N d d).trans
    (((rotateConfig N d).symm.prodCongr (rotateConfig N d)).trans
      (finTupleProdEquiv N d d).symm)

private def shiftExampleChainU₃ (d N : ℕ) : Equiv.Perm (Fin N → Fin (d * d)) :=
  (finTupleProdEquiv N d d).trans
    (((rotateConfig N d).prodCongr (rotateConfig N d).symm).trans
      (finTupleProdEquiv N d d).symm)

private theorem sitewise_shiftPhysicalSwap_eq_permMatrix (d N : ℕ) :
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N =
      Equiv.Perm.permMatrix ℂ (shiftExampleChainSwap d N) := by
  classical
  have hchain : shiftExampleChainSwap d N =
      Equiv.piCongrRight (fun _ : Fin N => bondPairSwapEquiv d) := by
    apply Equiv.ext
    intro σ
    funext n
    change finProdFinEquiv ((σ n).modNat, (σ n).divNat) = bondPairSwap (σ n)
    rfl
  rw [hchain]
  ext σ τ
  simp only [sitewisePhysicalMatrix, shiftPhysicalSwap, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply]
  rw [Fintype.prod_boole]
  simp [funext_iff]

private theorem shiftExampleU₂_chain_eq_permMatrix (d N : ℕ) :
    Matrix.reindex (finTupleProdEquiv N d d).symm
          (finTupleProdEquiv N d d).symm
          ((Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ ⊗ₖ
            Equiv.Perm.permMatrix ℂ (rotateConfig N d)) =
      Equiv.Perm.permMatrix ℂ (shiftExampleChainU₂ d N) := by
  classical
  ext σ τ
  simp [shiftExampleChainU₂, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply, Equiv.symm_apply_eq,
    Prod.ext_iff, ite_and]
  split <;> simp_all

private theorem shiftExampleU₃_chain_eq_permMatrix (d N : ℕ) :
    Matrix.reindex (finTupleProdEquiv N d d).symm
          (finTupleProdEquiv N d d).symm
          (Equiv.Perm.permMatrix ℂ (rotateConfig N d) ⊗ₖ
            (Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ) =
      Equiv.Perm.permMatrix ℂ (shiftExampleChainU₃ d N) := by
  classical
  ext σ τ
  simp [shiftExampleChainU₃, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply, Equiv.symm_apply_eq,
    Prod.ext_iff, ite_and]
  split <;> simp_all

private theorem shiftExampleChain_conjugacy (d N : ℕ) :
    (shiftExampleChainSwap d N).trans (shiftExampleChainU₃ d N) =
      (((shiftExampleChainSwap d N).trans (shiftExampleChainSwap d N)).trans
        (shiftExampleChainU₂ d N)).trans (shiftExampleChainSwap d N) := by
  apply Equiv.ext
  intro σ
  simp [shiftExampleChainSwap, shiftExampleChainU₂, shiftExampleChainU₃]

/-- Exact all-chain conjugacy
$\widetilde U_3^{(N)}=\mathbb S^{\otimes N}\widetilde U_2^{(N)}\mathbb S^{\otimes N}$.

Source: arXiv:1703.09188, equation `tildeU3` (lines 2059--2062). -/
theorem mpo_shiftExampleTildeU₃_eq_swap_mul_tildeU₂_mul_swap
    (d N : ℕ) [NeZero N] :
    mpo (shiftExampleTildeU₃ d) N =
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N *
        mpo (shiftExampleTildeU₂ d) N *
          sitewisePhysicalMatrix (shiftPhysicalSwap d) N := by
  rw [mpo_shiftExampleTildeU₃, mpo_shiftExampleTildeU₂,
    sitewise_shiftPhysicalSwap_eq_permMatrix,
    shiftExampleU₂_chain_eq_permMatrix, shiftExampleU₃_chain_eq_permMatrix]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul,
    ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1
  exact shiftExampleChain_conjugacy d N

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
