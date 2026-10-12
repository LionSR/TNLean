/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BlockSumAdjointBoundary
import TNLean.MPS.Symmetry.BlockBoundaryParentHamiltonian

/-!
# Canonical parent symmetry from normal periodic adjoint duality

Compatibility of an MPS with the actual unweighted MPO block sum implies
symmetry of its periodic canonical parent under every labelled periodic
operator when the normal positive-dimensional blocks possess an involutive
periodic physical adjoint dual. The entire arbitrary-boundary range is proved
adjoint closed from these hypotheses before applying the canonical-parent
commutation theorem.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Definition `defsym`,
  Section 5, and Appendix B. This is a canonical-parent consequence with the
  physical star-representation hypothesis explicit. It does not construct a
  weak Hopf algebra or identify a weak-Hopf-averaged interaction.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r D L N : ℕ} {dim : Fin r → ℕ}
    {O : (a : Fin r) → MPOTensor d (dim a)} {A : MPSTensor d D}
    {dual : Fin r → Fin r}

/-- Compatibility and normal periodic adjoint duality imply commutation of
the canonical parent with every periodic block. Adjoint closure of the whole
assembled boundary range is derived, rather than assumed. No normality or
injectivity hypothesis on the compatible state tensor is needed. -/
theorem IsBoundaryCompatible.parentHamiltonianES_commute_mpo_block_of_periodicAdjoint
    (h : IsBoundaryCompatible (blockSum O) A)
    (hAdjoint : IsPeriodicAdjointFamily O dual) (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (O a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a) (hL : 0 < L) (hLN : L ≤ N) (a : Fin r) :
    Commute (MPSTensor.parentHamiltonianES A L N)
      (Matrix.toEuclideanLin (mpo (O a) N)) := by
  apply h.parentHamiltonianES_commute_mpo_block hL hLN ?_ a
  intro X
  obtain ⟨Y, hY⟩ := hAdjoint.isBoundaryAdjointClosed_blockSum hdual hNormal hDim X
  exact ⟨Y, hY L hL⟩

end MPOTensor
