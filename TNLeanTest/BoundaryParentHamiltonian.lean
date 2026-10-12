/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BoundaryParentHamiltonian

/-!
# Periodic boundary-parent regression tests

The cut tests retain empty complements and wrapping windows. The theorem
signatures require closure of the full boundary range, without normality or
an ambient physical unit. A zero MPO gives a concrete nonunital regression,
while the local parent is nonzero by the dimension bound.
-/

set_option linter.hashCommand false

open scoped Matrix Kronecker BigOperators

namespace BoundaryParentHamiltonianTest

variable {d D D₁ D₂ L N : ℕ}

example (T : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (K : ℕ) :
    Matrix.reindex (blockSplitEquiv d 0 K) (blockSplitEquiv d 0 K)
        (MPOTensor.mpoWithBoundary T X (0 + K)) =
      ∑ a : Fin D, ∑ b : Fin D,
        MPOTensor.mpoWithBoundary T (Matrix.single b a 1 * X) 0 ⊗ₖ
          MPOTensor.mpoWithBoundary T (Matrix.single a b 1) K :=
  MPOTensor.mpoWithBoundary_reindex_blockSplit T X 0 K

example (T : MPOTensor d D) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ MPOTensor.commutingBoundaryAlgebra T) (i : Fin N) :
    Matrix.reindex (MPOTensor.windowComplementEquiv N N le_rfl i)
        (MPOTensor.windowComplementEquiv N N le_rfl i)
        (MPOTensor.mpoWithBoundary T X N) =
      ∑ a : Fin D, ∑ b : Fin D,
        MPOTensor.mpoWithBoundary T (Matrix.single b a 1 * X) N ⊗ₖ
          MPOTensor.mpoWithBoundary T (Matrix.single a b 1) (N - N) :=
  MPOTensor.mpoWithBoundary_reindex_windowComplement T hX N le_rfl i

-- The three-site window beginning at site four wraps across the end of a five-site chain.
example (T : MPOTensor d D) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ MPOTensor.commutingBoundaryAlgebra T)
    (K : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ)
    (hcomm : ∀ Y, Commute K (MPOTensor.mpoWithBoundary T Y 3)) :
    Commute (MPOTensor.embedLocalOperator 3 5 (by omega) 4 K)
      (MPOTensor.mpoWithBoundary T X 5) :=
  MPOTensor.embedLocalOperator_commute_mpoWithBoundary T (by omega) 4 K hcomm hX

example (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (h : MPOTensor.IsBoundaryCompatible T A) (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y, (MPOTensor.mpoWithBoundary T X L)ᴴ = MPOTensor.mpoWithBoundary T Y L) :
    Commute (MPSTensor.parentHamiltonianES A L N)
      (Matrix.toEuclideanLin (MPOTensor.mpo T N)) := by
  simpa only [MPOTensor.mpoWithBoundary_one] using
    h.parentHamiltonianES_commute_mpoWithBoundary hL hLN hstar
      (MPOTensor.commutingBoundaryAlgebra T).one_mem

example (A : MPSTensor 2 1) : MPSTensor.parentInteractionES A 1 ≠ 0 :=
  MPSTensor.parentInteractionES_ne_zero A 1 (by norm_num)

example (A : MPSTensor 2 1) : MPSTensor.parentInteraction A 1 ≠ 0 :=
  MPSTensor.parentInteraction_ne_zero A 1 (by norm_num)

private def zeroMPO : MPOTensor 2 1 := fun _ _ ↦ 0

private theorem zeroMPO_boundary (X : Matrix (Fin 1) (Fin 1) ℂ)
    {n : ℕ} (hn : 0 < n) : MPOTensor.mpoWithBoundary zeroMPO X n = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      ext σ τ
      simp [MPOTensor.mpoWithBoundary, List.ofFn_succ, MPOTensor.evalWord_cons, zeroMPO]

private theorem zeroMPO_compatible (A : MPSTensor 2 1) :
    MPOTensor.IsBoundaryCompatible zeroMPO A := by
  intro X Y
  refine ⟨0, fun n hn ↦ ?_⟩
  rw [zeroMPO_boundary X hn]
  ext σ
  simp [MPSTensor.mpvWithBoundary]

-- No hypothesis identifies the represented support unit with the ambient identity.
example (A : MPSTensor 2 1) (hN : 1 ≤ N) :
    MPSTensor.parentInteractionES A 1 ≠ 0 ∧
      ∀ X ∈ MPOTensor.commutingBoundaryAlgebra zeroMPO,
        Commute (MPSTensor.parentHamiltonianES A 1 N)
          (Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary zeroMPO X N)) := by
  apply (zeroMPO_compatible A).nonzero_parentInteractionES_and_parentHamiltonianES_commute
      (by omega) hN
  · intro X
    refine ⟨0, ?_⟩
    rw [zeroMPO_boundary X (by omega), zeroMPO_boundary 0 (by omega)]
    simp
  · norm_num

end BoundaryParentHamiltonianTest

/-- info: 'MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_mpoWithBoundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_mpoWithBoundary

/-- info: 'MPOTensor.IsBoundaryCompatible.nonzero_parentInteractionES_and_parentHamiltonianES_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.IsBoundaryCompatible.nonzero_parentInteractionES_and_parentHamiltonianES_commute

/-- info: 'MPOTensor.mpoWithBoundary_reindex_windowComplement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.mpoWithBoundary_reindex_windowComplement

/-- info: 'MPSTensor.parentInteractionES_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.parentInteractionES_ne_zero
