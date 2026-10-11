/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IsometricDeformationSymmetry
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction
import TNLean.MPS.Symmetry.GappedInteractionPath

/-!
# Matrix coordinates for general periodic interactions

The periodic sum of an arbitrary local operator in Euclidean coordinates agrees
with the sum of its embedded configuration-basis matrices. No positivity or
projection hypothesis is needed. The single-window identity is
`periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator`. This
extends the canonical-parent identities to the continuously extended local
interactions of arXiv:2203.12563, Section 5.
-/

open scoped BigOperators Matrix

namespace MPSTensor

variable {d R N : ℕ}

/-- The full Euclidean periodic sum agrees with the sum of embedded local
matrices, for every interaction range that fits in the chain. -/
theorem periodicInteractionHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator
    (h : MPOTensor.ChainOperator d R) (hRN : R ≤ N) :
    periodicInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin
        (∑ i : Fin N, MPOTensor.embedLocalOperator R N hRN i h) := by
  rw [periodicInteractionHamiltonianES, map_sum]
  simp_rw [periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator hRN _ h]

/-- The Euclidean periodic Hamiltonian of a two-site matrix is the matrix
Hamiltonian used for physical isometric gap transport. -/
theorem periodicInteractionHamiltonianES_eq_toEuclideanLin_interactionHamiltonian
    (h : MPOTensor.ChainOperator d 2) (hN : 2 ≤ N) :
    periodicInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin (interactionHamiltonian h hN) :=
  periodicInteractionHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator h hN

end MPSTensor
