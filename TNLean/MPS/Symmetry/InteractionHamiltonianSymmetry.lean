/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedInteractionPath
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry

/-!
# On-site symmetry of periodic interaction Hamiltonians

A local interaction commuting with the tensor power of an on-site operator gives a commuting
periodic Hamiltonian on every ring. Source context: arXiv:1010.3732, Sections II.C.2 and II.F.2.
-/

namespace MPSTensor

/-- Summing the translates around a ring of an on-site symmetric local interaction preserves its
on-site symmetry; on a ring shorter than the range the sum is zero. Unitarity is not needed for
this algebraic identity. Source context: arXiv:1010.3732, Sections II.C.2 and II.F.2;
lines 672--676. -/
theorem hamiltonian_translationInvariant_commute_onSiteTensorPow {d R N : ℕ} [NeZero N]
    (U : Matrix (Fin d) (Fin d) ℂ) (A : MPOTensor.ChainOperator d R)
    (hA : Commute A (onSiteTensorPow R U)) :
    Commute (ManyBody.Interaction.translationInvariant N A).hamiltonian
      (onSiteTensorPow N U) :=
  Commute.sum_left _ _ _ fun i _ ↦
    ManyBody.Interaction.forall_translationInvariant_term
      (P := fun M ↦ Commute M (onSiteTensorPow N U)) (Commute.zero_left _)
      (fun hk i ↦ placeAlong_ringWindow_commute_onSiteTensorPow U R hk i A hA) i

end MPSTensor
