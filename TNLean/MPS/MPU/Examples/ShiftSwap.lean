/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.MaximallyEntangled
import TNLean.MPS.MPU.Examples.Shift

/-!
# Physical-species swap for the shift examples

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
        (shiftExampleU₃ d (finProdFinEquiv (i₂, i₁)) (finProdFinEquiv (j₂, j₁))) =
      Matrix.swapMatrix d *
        Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (shiftExampleU₂ d (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv (j₁, j₂))) *
        Matrix.swapMatrix d := by
  ext ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
  rw [swapMatrix_mul_mul_swapMatrix_apply]
  simp only [Matrix.reindex_apply]
  simp [shiftExampleU₂, shiftExampleU₃, mul_comm]

end MPOTensor
