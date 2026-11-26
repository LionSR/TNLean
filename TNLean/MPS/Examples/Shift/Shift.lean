/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Unitary.Identity
import Mathlib.LinearAlgebra.Matrix.Permutation
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import TNLean.MPS.Operator.DensityOperator.AreaLaw
import TNLean.MPS.Operator.Periodic.OperatorCyclicSum
import TNLean.MPS.CanonicalForm.SimpleMPO.StackedLayers
import TNLean.MPS.MPU.Simple.SourceFactorContraction
import TNLean.MPS.MPU.CanonicalForm.TensorProduct
import QICLean.Algebra.Kronecker.MaximallyEntangled

/-!
# Shift matrix product unitaries

The examples in arXiv:1703.09188, lines 1980--2001.

## Main definitions

* `rightShiftTensor` and `leftShiftTensor`: bond-$d$ tensors for the right and
  left cyclic shifts.
* `identityMPUTensor`: the bond-one identity tensor, imported from
  `TNLean.MPS.MPU.Identity`.
* `shiftExampleU₁`, `shiftExampleU₂`, and `shiftExampleU₃`: the three operator
  families $U_1$, $U_2$, and $U_3$ from the source.

## Main results

* `mpo_rightShiftTensor` and `mpo_leftShiftTensor`: exact finite-chain shift
  formulas.
* `rightShiftTensor_isMPU` and `leftShiftTensor_isMPU`: the shift tensors are
  matrix product unitaries.
* `mpo_shiftExampleU₁`, `mpo_shiftExampleU₂`, and `mpo_shiftExampleU₃`: exact
  finite-chain formulas for the three examples.
* `shiftExampleU₁_isMPU`, `shiftExampleU₂_isMPU`, and `shiftExampleU₃_isMPU`:
  the three examples are matrix product unitaries.
* `MPOTensor.shiftExampleU₃_physicalSwap_eq_swapMatrix_mul_shiftExampleU₂_mul_swapMatrix`:
  physical-species swap for the shift examples.
-/

section Shift

open scoped Matrix Kronecker

namespace MPOTensor

/-- The bond-$d$ tensor whose closed MPO is the right shift. -/
def rightShiftTensor (d : ℕ) : MPOTensor d d :=
  fun (i, j) ↦ Matrix.single i j 1

@[simp] theorem rightShiftTensor_apply (d : ℕ) (i j α β : Fin d) :
    rightShiftTensor d (i, j) α β = if i = α ∧ j = β then 1 else 0 := by
  rfl

/-- Entry formula fixing the row convention: Mathlib's permutation matrix for
`rotateConfig` is exactly the source right shift. -/
theorem mpo_rightShiftTensor_apply (d N : ℕ) [NeZero N]
    (σ τ : Fin N → Fin d) :
    mpo (rightShiftTensor d) N σ τ =
      Equiv.Perm.permMatrix ℂ (rotateConfig N d) σ τ := by
  rw [MPOTensor.mpo_apply_eq_sum_cyclic]
  by_cases hστ : rotateConfig N d σ = τ
  · rw [Fintype.sum_eq_single σ]
    · have hp : ∀ n, τ n = σ (n + 1) := by
        intro n
        simpa only [rotateConfig_apply, Function.comp_apply, finRotate_apply]
          using (congrFun hστ n).symm
      have hcomp : σ ∘ finRotate N = τ := by
        simpa only [rotateConfig_apply] using hστ
      simp [rightShiftTensor, hp, Equiv.Perm.permMatrix,
        PEquiv.toMatrix, hcomp]
    · intro g hg
      obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
      apply Finset.prod_eq_zero (Finset.mem_univ n)
      simp [rightShiftTensor, hn.symm]
  · have hcomp : σ ∘ finRotate N ≠ τ := by
      simpa only [rotateConfig_apply] using hστ
    have hrhs : Equiv.Perm.permMatrix ℂ (rotateConfig N d) σ τ = 0 := by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, hcomp]
    rw [hrhs]
    apply Finset.sum_eq_zero
    intro g _
    by_cases hg : g = σ
    · subst g
      have hpoint : ∃ n, σ (n + 1) ≠ τ n := by
        simpa only [rotateConfig_apply, Function.comp_apply, finRotate_apply,
          ne_eq] using Function.ne_iff.mp hστ
      obtain ⟨n, hn⟩ := hpoint
      apply Finset.prod_eq_zero (Finset.mem_univ n)
      simp [rightShiftTensor, hn.symm]
    · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
      apply Finset.prod_eq_zero (Finset.mem_univ n)
      simp [rightShiftTensor, hn.symm]

/-- The bond-$d$ tensor generates the source right shift on every nonempty chain. -/
theorem mpo_rightShiftTensor (d N : ℕ) [NeZero N] :
    mpo (rightShiftTensor d) N = Equiv.Perm.permMatrix ℂ (rotateConfig N d) := by
  ext σ τ
  exact mpo_rightShiftTensor_apply d N σ τ

/-- The right-shift tensor is an MPU. -/
theorem rightShiftTensor_isMPU (d : ℕ) : IsMPU (rightShiftTensor d) := by
  intro N hN
  let : NeZero N := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)⟩
  rw [mpo_rightShiftTensor]
  exact Equiv.Perm.permMatrix_mem_unitaryGroup (rotateConfig N d)

/-- The adjoint tensor generates the left shift. -/
def leftShiftTensor (d : ℕ) : MPOTensor d d :=
  physicalAdjointTensor (rightShiftTensor d)

/-- The adjoint shift has the expected all-chain operator formula. -/
theorem mpo_leftShiftTensor (d N : ℕ) [NeZero N] :
    mpo (leftShiftTensor d) N =
      (Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ := by
  rw [leftShiftTensor, mpo_physicalAdjointTensor_eq_conjTranspose,
    mpo_rightShiftTensor]

/-- The left-shift tensor is an MPU. -/
theorem leftShiftTensor_isMPU (d : ℕ) : IsMPU (leftShiftTensor d) :=
  (rightShiftTensor_isMPU d).physicalAdjointTensor

/-- The paper's $U_1$, the identity on two spins at each site. -/
noncomputable def shiftExampleU₁ (d : ℕ) : MPOTensor (d * d) 1 :=
  tensorProduct (identityMPUTensor d) (identityMPUTensor d)

/-- The paper's $U_2=T^\dagger\otimes T$. -/
def shiftExampleU₂ (d : ℕ) : MPOTensor (d * d) (d * d) :=
  tensorProduct (leftShiftTensor d) (rightShiftTensor d)

/-- The paper's $U_3=T\otimes T^\dagger$. -/
def shiftExampleU₃ (d : ℕ) : MPOTensor (d * d) (d * d) :=
  tensorProduct (rightShiftTensor d) (leftShiftTensor d)

/-- Exact all-chain formula for $U_1$. -/
theorem mpo_shiftExampleU₁ (d N : ℕ) : mpo (shiftExampleU₁ d) N = 1 := by
  rw [shiftExampleU₁, mpo_tensorProduct, mpo_identityMPUTensor,
    Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv _

/-- Exact all-chain formula for $U_2$. -/
theorem mpo_shiftExampleU₂ (d N : ℕ) [NeZero N] :
    mpo (shiftExampleU₂ d) N =
      Matrix.reindex (finTupleProdEquiv N d d).symm
        (finTupleProdEquiv N d d).symm
        ((Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ ⊗ₖ
          Equiv.Perm.permMatrix ℂ (rotateConfig N d)) := by
  rw [shiftExampleU₂, mpo_tensorProduct, mpo_leftShiftTensor,
    mpo_rightShiftTensor]

/-- Exact all-chain formula for $U_3$. -/
theorem mpo_shiftExampleU₃ (d N : ℕ) [NeZero N] :
    mpo (shiftExampleU₃ d) N =
      Matrix.reindex (finTupleProdEquiv N d d).symm
        (finTupleProdEquiv N d d).symm
        (Equiv.Perm.permMatrix ℂ (rotateConfig N d) ⊗ₖ
          (Equiv.Perm.permMatrix ℂ (rotateConfig N d))ᴴ) := by
  rw [shiftExampleU₃, mpo_tensorProduct, mpo_rightShiftTensor,
    mpo_leftShiftTensor]

/-- $U_1$ is an MPU. -/
theorem shiftExampleU₁_isMPU (d : ℕ) : IsMPU (shiftExampleU₁ d) :=
  (identityMPUTensor_isMPU d).tensorProduct (identityMPUTensor_isMPU d)

/-- $U_2$ is an MPU. -/
theorem shiftExampleU₂_isMPU (d : ℕ) : IsMPU (shiftExampleU₂ d) :=
  (leftShiftTensor_isMPU d).tensorProduct (rightShiftTensor_isMPU d)

/-- $U_3$ is an MPU. -/
theorem shiftExampleU₃_isMPU (d : ℕ) : IsMPU (shiftExampleU₃ d) :=
  (rightShiftTensor_isMPU d).tensorProduct (leftShiftTensor_isMPU d)

end MPOTensor

end Shift

section ShiftSwap

/-!
## Physical-species swap for the shift examples

A local refinement of the finite-chain observations in arXiv:1703.09188,
lines 1999--2001 and 2240--2245: exchanging the two spins at every site swaps
$U_2$ and $U_3$.
-/

open scoped Matrix

namespace MPOTensor

private theorem swapMatrix_mul_mul_swapMatrix_apply
    (d : ℕ) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (α₁ α₂ β₁ β₂ : Fin d) :
    (Matrix.swapMatrix d * M * Matrix.swapMatrix d) (α₁, α₂) (β₁, β₂) =
      M (α₂, α₁) (β₂, β₁) := by
  have swap_mul_apply (γ₁ γ₂ : Fin d) :
      (Matrix.swapMatrix d * M) (α₁, α₂) (γ₁, γ₂) =
        M (α₂, α₁) (γ₁, γ₂) := by
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_prod_type, Matrix.swapMatrix_apply]
    rw [Finset.sum_eq_single α₂]
    · rw [Finset.sum_eq_single α₁]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · intro x _ hx
      apply Finset.sum_eq_zero
      intro y _
      simp [Ne.symm hx]
    · simp
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_prod_type, Matrix.swapMatrix_apply, swap_mul_apply]
  rw [Finset.sum_eq_single β₂]
  · rw [Finset.sum_eq_single β₁]
    · simp
    · intro x _ hx
      simp [hx]
    · simp
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    simp [hx]
  · simp

/-- Swapping the two physical species exchanges the local tensors $U_2$ and
$U_3$, up to the corresponding swap of their two virtual factors.

The physical output and input coordinates are ordered as `(i₁, i₂)` and
`(j₁, j₂)`. After their exchange, the $U_3$ entry at `(i₂, i₁)` and
`(j₂, j₁)` is the $U_2$ virtual matrix conjugated by the SWAP operator. This
locally refines the finite-chain statements in arXiv:1703.09188, lines
1999--2001 and 2240--2245. -/
theorem shiftExampleU₃_physicalSwap_eq_swapMatrix_mul_shiftExampleU₂_mul_swapMatrix
    (d : ℕ) (i₁ i₂ j₁ j₂ : Fin d) :
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (shiftExampleU₃ d (finProdFinEquiv (i₂, i₁), finProdFinEquiv (j₂, j₁))) =
      Matrix.swapMatrix d *
        Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (shiftExampleU₂ d (finProdFinEquiv (i₁, i₂), finProdFinEquiv (j₁, j₂))) *
        Matrix.swapMatrix d := by
  ext ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
  rw [swapMatrix_mul_mul_swapMatrix_apply]
  simp only [Matrix.reindex_apply]
  simp [shiftExampleU₂, shiftExampleU₃, mul_comm]

end MPOTensor

end ShiftSwap
