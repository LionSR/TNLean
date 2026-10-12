/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BoundaryParentHamiltonian
import TNLean.MPS.MPDO.BlockBoundarySelector

/-!
# Individual block symmetries of canonical parent Hamiltonians

A summand boundary selector commuting with every assembled tensor letter
isolates an individual periodic MPO block. The periodic canonical parent
therefore commutes with each labelled MPO under compatibility and adjoint
closure of the entire assembled
boundary range. Adjoint closure need not hold separately for each label.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Definition `defsym`,
lines 1236--1246, and Section 5, lines 1276--1320. The star-compatible weak-Hopf
realization remains separate; see `docs/paper-gaps/glm23_wha_parent_completion.tex`.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r D L N : ℕ} {dim : Fin r → ℕ}
    {O : (a : Fin r) → MPOTensor d (dim a)} {A : MPSTensor d D}

/-- Compatibility with the assembled MPO tensor and adjoint closure of its whole
local boundary range imply commutation of the periodic parent with every
individual periodic MPO block. Source: GLM23, arXiv:2203.12563v3, `defsym` and
Section 5, lines 1276--1320, with the assembled adjoint-closure hypothesis explicit. -/
theorem IsBoundaryCompatible.parentHamiltonianES_commute_mpo_block
    (h : IsBoundaryCompatible (blockSum O) A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin (∑ a : Fin r, dim a)) (Fin (∑ a : Fin r, dim a)) ℂ,
      ∃ Y : Matrix (Fin (∑ a : Fin r, dim a)) (Fin (∑ a : Fin r, dim a)) ℂ,
        (mpoWithBoundary (blockSum O) X L)ᴴ = mpoWithBoundary (blockSum O) Y L)
    (a : Fin r) :
    Commute (MPSTensor.parentHamiltonianES A L N)
      (Matrix.toEuclideanLin (mpo (O a) N)) := by
  simpa only [mpoWithBoundary_blockSum_blockBoundarySelector] using
    h.parentHamiltonianES_commute_mpoWithBoundary hL hLN hstar
      (blockBoundarySelector_mem_commutingBoundaryAlgebra O a)

end MPOTensor
