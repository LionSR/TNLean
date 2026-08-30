/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.Shift
import TNLean.MPS.MPDO.SitewisePhysicalMatrix

/-!
# Swap-transformed shift matrix product unitaries

The swap transformation in arXiv:1703.09188, equations `threeMPU2`
(lines 2046--2062), multiplies every local physical operator on the left by
the swap of the two spins. This file defines the three transformed tensors,
proves their exact finite-chain formulas, and proves that they remain MPUs.

No symmetry-phase classification is asserted here.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D : ℕ}

private theorem trace_mul_evalWord_ketLeftMul_ofFn
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ}
    (X : Matrix (Fin D) (Fin D) ℂ) (σ τ : Fin N → Fin d) :
    Matrix.trace (X * evalWord (M.ketLeftMul P) (List.ofFn σ) (List.ofFn τ)) =
      ∑ ρ : Fin N → Fin d, (∏ n : Fin N, P (σ n) (ρ n)) *
        Matrix.trace (X * evalWord M (List.ofFn ρ) (List.ofFn τ)) := by
  induction N generalizing X with
  | zero => simp
  | succ n ih =>
      simp only [List.ofFn_succ, evalWord_cons, ketLeftMul]
      rw [← Matrix.mul_assoc, Matrix.mul_sum, Finset.sum_mul, Matrix.trace_sum]
      simp_rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      have reindex : ∀ F : (Fin (n + 1) → Fin d) → ℂ,
          ∑ ρ, F ρ = ∑ k : Fin d, ∑ ρ' : Fin n → Fin d, F (Fin.cons k ρ') :=
        fun F => by
          rw [← Fintype.sum_prod_type']
          exact ((Fin.consEquiv fun _ : Fin (n + 1) ↦ Fin d).sum_comp F).symm
      rw [reindex]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      rw [Matrix.mul_assoc]
      ring

/-- Applying a matrix to the ket leg at every site left-multiplies the closed
MPO by its sitewise tensor power. -/
theorem mpo_ketLeftMul (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    mpo (M.ketLeftMul P) N = sitewisePhysicalMatrix P N * mpo M N := by
  ext σ τ
  simp only [Matrix.mul_apply, mpo_apply, mpoMatrixEntry, sitewisePhysicalMatrix]
  simpa only [Matrix.one_mul] using
    trace_mul_evalWord_ketLeftMul_ofFn M P (1 : Matrix (Fin D) (Fin D) ℂ) σ τ

/-- Left multiplication by a one-site unitary preserves the MPU property. -/
theorem IsMPU.ketLeftMul {M : MPOTensor d D} (hM : IsMPU M)
    {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    IsMPU (M.ketLeftMul P) := by
  intro N hN
  rw [mpo_ketLeftMul]
  apply (Matrix.unitaryGroup (Fin N → Fin d) ℂ).mul_mem
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose,
      sitewisePhysicalMatrix_isometry P]
    rw [Matrix.mem_unitaryGroup_iff'] at hP
    simpa only [Matrix.star_eq_conjTranspose] using hP
  · exact hM.mpo_mem_unitaryGroup hN

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
    shiftPhysicalSwap d ∈ Matrix.unitaryGroup (Fin (d * d)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [shiftPhysicalSwap, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

/-- The paper's transformed tensor $\widetilde{\mathcal U}_1=\mathcal U_1\mathbb S$,
implemented by the exact local physical left action. -/
noncomputable def shiftExampleTildeU₁ (d : ℕ) : MPOTensor (d * d) 1 :=
  (shiftExampleU₁ d).ketLeftMul (shiftPhysicalSwap d)

/-- The paper's transformed tensor $\widetilde{\mathcal U}_2=\mathcal U_2\mathbb S$,
implemented by the exact local physical left action. -/
noncomputable def shiftExampleTildeU₂ (d : ℕ) : MPOTensor (d * d) (d * d) :=
  (shiftExampleU₂ d).ketLeftMul (shiftPhysicalSwap d)

/-- The paper's transformed tensor $\widetilde{\mathcal U}_3=\mathcal U_3\mathbb S$,
implemented by the exact local physical left action. -/
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
