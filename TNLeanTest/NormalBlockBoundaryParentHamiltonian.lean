/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.NormalBlockBoundaryParentHamiltonian

/-!
# Canonical parent symmetry from raw normal periodic dual blocks

This signature regression assumes periodic physical adjoint identities and
compatibility, with no supplied arbitrary-boundary adjoint-closure witness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace NormalBlockBoundaryParentHamiltonianTest

example {d r D L N : ℕ} {dim : Fin r → ℕ}
    (O : (a : Fin r) → MPOTensor d (dim a)) (A : MPSTensor d D)
    (dual : Fin r → Fin r) (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (O a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a)
    (hPeriodic : ∀ (a : Fin r) (n : ℕ), 0 < n →
      MPOTensor.mpo (O (dual a)) n = (MPOTensor.mpo (O a) n)ᴴ)
    (hCompatible : MPOTensor.IsBoundaryCompatible (MPOTensor.blockSum O) A)
    (hL : 0 < L) (hLN : L ≤ N) (a : Fin r) :
    Commute (MPSTensor.parentHamiltonianES A L N)
      (Matrix.toEuclideanLin (MPOTensor.mpo (O a) N)) :=
  hCompatible.parentHamiltonianES_commute_mpo_block_of_periodicAdjoint
    hPeriodic hdual hNormal hDim hL hLN a

/--
info: 'MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_mpo_block_of_periodicAdjoint'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_mpo_block_of_periodicAdjoint

end NormalBlockBoundaryParentHamiltonianTest
