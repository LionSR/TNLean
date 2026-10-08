/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalCommutatorLocality

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
-/

open MPSTensor
open scoped Matrix BigOperators

namespace SpinChain

variable {d : ℕ} [NeZero d]

/-- The quasi-local image of a finite open sum is the sum of the nonwrapping
translated interaction observables. Source: Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem quasiLocalIntervalObservable_openInteractionMatrix (a : ℤ) {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (N : ℕ) :
    quasiLocalIntervalObservable d a N (openInteractionMatrix h N) =
      ∑ i ∈ Finset.range (N + 1 - R),
        quasiLocalIntervalObservable d (a + (i : ℤ)) R h := by
  rw [openInteractionMatrix, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  exact quasiLocalIntervalObservable_chainWindowOperator a N i h hR
    (by have hi' := Finset.mem_range.mp hi; omega)

/-- Vanishing expectation on every local translate implies vanishing
expectation on every finite open interaction sum. The functional need only
be linear; in particular no translation invariance is imposed on a state.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12) and the
zero-energy face in Theorem 1.1. -/
theorem apply_quasiLocalIntervalObservable_openInteractionMatrix_eq_zero
    (φ : QuasiLocalAlgebra d →ₗ[ℂ] ℂ) {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (a : ℤ) (N : ℕ) :
    φ (quasiLocalIntervalObservable d a N (openInteractionMatrix h N)) = 0 := by
  simp only [quasiLocalIntervalObservable_openInteractionMatrix a h hR N,
    map_sum, hzero, Finset.sum_const_zero]

end SpinChain
