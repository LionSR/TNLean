/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalCommutatorLocality
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalParentExpectation
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockSumIntervalSpaces

/-!
# Finite open-chain expectations from local zero energy

A nonwrapping finite-volume interaction sum is the sum of its ordinary
translated quasi-local interval observables. Consequently a linear
functional vanishing on every translate of a local interaction also
vanishes on every finite open-chain sum. Translation invariance,
positivity, normalization, and continuity of the functional are unnecessary.

This is the finite-volume zero-energy consequence used in the ground-state
face argument of Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
equation (3.12), and lines 1469--1482.

## Local sector expectations from open-chain kernels

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

section

open MPSTensor
open scoped Matrix BigOperators

open ManyBody.Interaction (chainTranslates hamiltonian_chainTranslates_eq_sum_range)

namespace SpinChain

variable {d : ℕ} [NeZero d]

/-- The quasi-local image of a finite open sum is the sum of the nonwrapping
translated interaction observables. Source: Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem quasiLocalIntervalObservable_hamiltonian_chainTranslates (a : ℤ) {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (N : ℕ) :
    quasiLocalIntervalObservable d a N ((chainTranslates R N h).hamiltonian) =
      ∑ i ∈ Finset.range (N + 1 - R),
        quasiLocalIntervalObservable d (a + (i : ℤ)) R h := by
  rw [hamiltonian_chainTranslates_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i + R ≤ N := by
    have hi'' := Finset.mem_range.mp hi
    omega
  simp only [dite_eq_left hi']
  exact quasiLocalIntervalObservable_placeAlong_chainWindow a N i h hi'

/-- Vanishing expectation on every local translate implies vanishing
expectation on every finite open interaction sum. The functional need only
be linear; in particular no translation invariance is imposed on a state.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12) and the
zero-energy face in Theorem 1.1. -/
theorem apply_quasiLocalIntervalObservable_hamiltonian_chainTranslates_eq_zero
    (φ : QuasiLocalAlgebra d →ₗ[ℂ] ℂ) {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (a : ℤ) (N : ℕ) :
    φ (quasiLocalIntervalObservable d a N ((chainTranslates R N h).hamiltonian)) = 0 := by
  simp only [quasiLocalIntervalObservable_hamiltonian_chainTranslates a h N,
    map_sum, hzero, Finset.sum_const_zero]

end SpinChain

end

section

open scoped Matrix ComplexOrder BigOperators
open SpinChain

open ManyBody.Interaction (chainTranslates)

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
    {R N : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hRN : R ≤ N)
    (hker : groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N ≤
      LinearMap.ker (Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian))) (a : ℤ) :
    quasiLocalExpectation (A α) hTP hρ hfix htr
      (quasiLocalIntervalObservable d a R h) = 0 := by
  have hkerα : groundSpaceES (A α) N ≤
      LinearMap.ker (Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian)) := by
    apply le_trans ?_ hker
    exact groundSpaceES_block_le_toTensorFromBlocks μ A hμ α N
  have hzero := quasiLocalExpectation_interval_eq_zero_of_groundSpaceES_le_ker
    (A α) hTP hρ hfix htr a ((chainTranslates R N h).hamiltonian) hkerα
  rw [quasiLocalIntervalObservable_hamiltonian_chainTranslates a h N, map_sum] at hzero
  simp only [quasiLocalExpectation_quasiLocalIntervalObservable, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hzero ⊢
  exact (mul_eq_zero.mp hzero).resolve_left (Nat.cast_ne_zero.mpr (by omega))

/-- An eventual equality between the kernel of the open-chain Hamiltonian of an interaction and
the joint MPS space implies zero local interaction expectation in each constructed sector state.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, the eventual
finite-volume kernel condition. -/
theorem quasiLocalExpectation_interval_eq_zero_of_eventually_ker_hamiltonian_chainTranslates
    {b : ℕ} {dim : Fin b → ℕ}
    (μ : Fin b → ℂ) (A : ∀ α, MPSTensor d (dim α)) (hμ : ∀ α, μ α ≠ 0)
    (α : Fin b) (hTP : ∑ i, (A α i)ᴴ * A α i = 1)
    {ρ : Matrix (Fin (dim α)) (Fin (dim α)) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap (A α) ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    {R : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hker : ∀ᶠ N in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        groundSpaceES (toTensorFromBlocks μ A) N) (a : ℤ) :
    quasiLocalExpectation (A α) hTP hρ hfix htr
      (quasiLocalIntervalObservable d a R h) = 0 := by
  obtain ⟨N, hN, hRN⟩ := (hker.and (Filter.eventually_ge_atTop R)).exists
  exact quasiLocalExpectation_interval_eq_zero_of_open_groundSpaceES_le_ker
    μ A hμ α hTP hρ hfix htr h hRN hN.ge a

end MPSTensor

end
