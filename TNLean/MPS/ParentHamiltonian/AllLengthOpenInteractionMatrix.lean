/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BulkObservableCommutator

/-!
# Matrix and Euclidean open interactions at every chain length

The matrix and Euclidean sums over nonwrapping interaction windows agree at
every chain length when the interaction range is positive. On shorter chains
both sums vanish. The equality therefore transports norm gaps above the
actual kernels without an additional lower bound on the volume.

Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12).
-/

open scoped Matrix BigOperators
namespace MPSTensor
variable {d R N : ℕ}

/-- The open matrix sum vanishes when the interval is shorter than its
interaction range. Source: Nachtergaele, arXiv:cond-mat/9410110,
equation (3.12), the empty interaction sum. -/
theorem openInteractionMatrix_eq_zero_of_length_lt
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hN : N < R) :
    openInteractionMatrix h N = 0 := by
  have hEmpty : N + 1 - R = 0 := Nat.sub_eq_zero_of_le (by omega)
  simp [openInteractionMatrix, hEmpty]

/-- The Euclidean open interaction sum also vanishes on intervals shorter
than its range. Source: Nachtergaele, arXiv:cond-mat/9410110,
equation (3.12), the empty interaction sum. -/
theorem openInteractionHamiltonianES_eq_zero_of_length_lt
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hN : N < R) : openInteractionHamiltonianES h N = 0 := by
  let _ : IsEmpty (NonwrappingStart R N) := ⟨fun i => by
    have hi := i.2
    change i.1.val + R ≤ N at hi
    omega⟩
  simp [openInteractionHamiltonianES]

/-- The matrix and Euclidean open Hamiltonians agree at every chain length,
including those below the positive interaction range. Source: Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix_all
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (N : ℕ) :
    openInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin (openInteractionMatrix h N) := by
  by_cases hRN : R ≤ N
  · exact openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hRN
  · have hN : N < R := Nat.lt_of_not_ge hRN
    rw [openInteractionHamiltonianES_eq_zero_of_length_lt _ hN,
      openInteractionMatrix_eq_zero_of_length_lt h hN, map_zero]

end MPSTensor

