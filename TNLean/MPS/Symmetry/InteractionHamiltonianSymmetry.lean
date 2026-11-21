/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedInteractionPath
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry

/-!
# On-site symmetry of periodic interaction Hamiltonians

A two-site interaction commuting with the tensor square of an on-site
operator gives a commuting periodic Hamiltonian at every ring length at
least two. Source context: arXiv:1010.3732, Sections II.C.2 and II.F.2.
-/

namespace MPSTensor

/-- Summing the translates of an on-site symmetric two-site interaction
preserves its on-site symmetry. Unitarity is not needed for this algebraic
identity. Source context: arXiv:1010.3732, Sections II.C.2 and II.F.2. -/
theorem hamiltonian_translationInvariant_commute_onSiteTensorPow {d N : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (A : MPOTensor.ChainOperator d 2)
    (hN : 2 ≤ N) (hA : Commute A (onSiteTensorPow 2 U)) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (ManyBody.Interaction.translationInvariant N A).hamiltonian
      (onSiteTensorPow N U) :=
  haveI : NeZero N := ⟨by omega⟩; Commute.sum_left _ _ _ fun i _ => by
    rw [ManyBody.Interaction.translationInvariant_term_of_le A hN i]
    exact placeAlong_ringWindow_commute_onSiteTensorPow U 2 hN i A hA

end MPSTensor
