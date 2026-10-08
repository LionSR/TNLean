/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalParentExpectation
import TNLean.MPS.ParentHamiltonian.QuasiLocalOpenInteractionExpectation
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces

/-!
# Local sector expectations from open-chain kernels

Suppose that one finite open-chain interaction sum annihilates the joint MPS
space, and that its length is at least the interaction range. Each constructed
sector state then has zero local interaction expectation at every position.
Indeed, its expectation of the open sum is zero, while each summand has the
same trace insertion expectation. There is at least one summand.

An eventual equality of the finite open-chain kernel with the joint MPS space
therefore suffices. Neither simultaneous injectivity at the interaction range
nor a local parent-interaction predicate is required. Positivity of the
interaction is unnecessary for this implication.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, the finite-volume
kernel condition, and equation (3.12). These are sector membership statements;
classification of all ground states is a separate result.
-/

open scoped Matrix ComplexOrder BigOperators
open SpinChain

namespace MPSTensor

variable {d : ℕ} [NeZero d]

/-- If one open-chain interaction sum annihilates the joint MPS space, every
constructed sector state has zero expectation of the local interaction.
No positivity assumption on the interaction is needed. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, the finite-volume kernel condition,
and equation (3.12). -/
theorem quasiLocalExpectation_interval_eq_zero_of_open_groundSpaceES_le_ker
    {b : ℕ} {dim : Fin b → ℕ}
    (μ : Fin b → ℂ) (A : ∀ α, MPSTensor d (dim α)) (hμ : ∀ α, μ α ≠ 0)
    (α : Fin b) (hTP : ∑ i, (A α i)ᴴ * A α i = 1)
    {ρ : Matrix (Fin (dim α)) (Fin (dim α)) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap (A α) ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    {R N : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hRN : R ≤ N)
    (hker : groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N ≤
      LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h N))) (a : ℤ) :
    quasiLocalExpectation (A α) hTP hρ hfix htr
      (quasiLocalIntervalObservable d a R h) = 0 := by
  have hkerα : groundSpaceES (A α) N ≤
      LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h N)) := by
    apply le_trans ?_ hker
    exact groundSpaceES_block_le_toTensorFromBlocks μ A hμ α N
  have hzero := quasiLocalExpectation_interval_eq_zero_of_groundSpaceES_le_ker
    (A α) hTP hρ hfix htr a (openInteractionMatrix h N) hkerα
  rw [quasiLocalIntervalObservable_openInteractionMatrix a h hR N, map_sum] at hzero
  simp only [quasiLocalExpectation_quasiLocalIntervalObservable, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hzero ⊢
  exact (mul_eq_zero.mp hzero).resolve_left (Nat.cast_ne_zero.mpr (by omega))

/-- An eventual equality between the open-chain kernel and the joint MPS space
implies zero local interaction expectation in each constructed sector state.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, the eventual
finite-volume kernel condition. -/
theorem quasiLocalExpectation_interval_eq_zero_of_eventually_open_kernel
    {b : ℕ} {dim : Fin b → ℕ}
    (μ : Fin b → ℂ) (A : ∀ α, MPSTensor d (dim α)) (hμ : ∀ α, μ α ≠ 0)
    (α : Fin b) (hTP : ∑ i, (A α i)ᴴ * A α i = 1)
    {ρ : Matrix (Fin (dim α)) (Fin (dim α)) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap (A α) ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    {R : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R)
    (hker : ∀ᶠ N in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) (a : ℤ) :
    quasiLocalExpectation (A α) hTP hρ hfix htr
      (quasiLocalIntervalObservable d a R h) = 0 := by
  obtain ⟨N, hN, hRN⟩ := (hker.and (Filter.eventually_ge_atTop R)).exists
  apply quasiLocalExpectation_interval_eq_zero_of_open_groundSpaceES_le_ker
    μ A hμ α hTP hρ hfix htr h hR hRN (a := a)
  rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hRN, hN]

end MPSTensor
