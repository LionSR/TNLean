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
with the sum of its configuration-basis matrices placed on the windows of the
ring, the Hamiltonian of the translation-invariant interaction
(`ManyBody.Interaction.translationInvariant`). No positivity or projection
hypothesis is needed. The single-window identity is
`periodicLocalInteractionES_eq_toEuclideanLin_placeAlong_ringWindow`. This
extends the canonical-parent identities to the continuously extended local
interactions of arXiv:2203.12563, Section 5.
-/

open scoped BigOperators Matrix

namespace MPSTensor

variable {d R N : ℕ}

/-- The full Euclidean periodic sum agrees with the Hamiltonian of the translation-invariant
interaction of the local matrix, for every interaction range that fits in the chain. -/
theorem periodicInteractionHamiltonianES_eq_toEuclideanLin_hamiltonian
    [NeZero N] (h : MPOTensor.ChainOperator d R) (hRN : R ≤ N) :
    periodicInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian := by
  rw [periodicInteractionHamiltonianES, ManyBody.Interaction.hamiltonian, map_sum]
  simp_rw [periodicLocalInteractionES_eq_toEuclideanLin_placeAlong_ringWindow hRN _ h,
    ManyBody.Interaction.translationInvariant_term_of_le h hRN]

end MPSTensor
