/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.MPDO.CommutingForm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Matrix coordinates for canonical parent Hamiltonians

The canonical local projection and its cyclic translates admit identical
matrix descriptions in the configuration basis and the Euclidean Hilbert
space. These identities connect the parent-Hamiltonian gap estimates to
the matrix formulation of local interactions used in arXiv:1010.3732,
Section II.B (`Papers/1010.3732/paper_v3.tex`, lines 357--390).

**Transitional (#10948).** `parentInteractionES_eq_toEuclideanLin_parentMatrix`, the identity
between the Euclidean-space operator `parentInteractionES` and the matrix of the local parent
interaction, is kept until its last users are converted, then deleted with that operator.
-/

open scoped Matrix.Norms.L2Operator

namespace MPSTensor

variable {d D : ℕ}

/-- The canonical parent interaction is represented by the same matrix in
the function and Euclidean realizations of the finite configuration space.
Source: arXiv:1010.3732, Section II.D. -/
theorem parentInteractionES_eq_toEuclideanLin_parentMatrix
    (A : MPSTensor d D) (L : ℕ) :
    parentInteractionES A L = Matrix.toEuclideanLin
      (LinearMap.toMatrix' (parentInteraction A L)) :=
  (toEuclideanLin_toMatrix'_parentInteraction A L).symm

/-- A cyclic parent term is the matrix of its local interaction placed on the window of `L`
consecutive sites starting at `i`. Source: arXiv:1010.3732, Section II.B, the local Hamiltonian
sum. -/
theorem localTerm_eq_toLin'_placeAlong_ringWindow (A : MPSTensor d D)
    {L N : ℕ} (hLN : L ≤ N) (i : Fin N) :
    localTerm A L N i = Matrix.toLin'
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hLN i)
        (LinearMap.toMatrix' (parentInteraction A L))) := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [localTerm_eq_toLin'_term A L i,
    ManyBody.Interaction.translationInvariant_term_of_le _ hLN i]

/-- Canonical parent interactions have Hilbert-space operator norm at most
one, as do the projector local terms of arXiv:1010.3732, Section II.B. -/
theorem parentInteraction_toMatrix'_norm_le_one (A : MPSTensor d D) (L : ℕ) :
    ‖LinearMap.toMatrix' (parentInteraction A L)‖ ≤ 1 :=
  (isStarProjection_toMatrix'_parentInteraction A L).norm_le _

end MPSTensor
