/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Regrouping physical registers into neighboring bonds

A physical site has a left and a right virtual register. The incoming bond
at site `i` consists of the right register at its cyclic predecessor and
the left register at `i`. This is a permutation of the entire configuration
basis. It is the change of coordinates used for the independent-bond parent
Hamiltonian in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective` and equation `eq:phase-nosym:iso-hamiltonian`.

No assertion about the depth of a circuit on whole physical sites is made.
-/

namespace MPSTensor

/-- Read the incoming bond registers `(R_{i-1}, L_i)` from physical sites
`(L_i, R_i)`. The cyclic permutation also defines this equivalence for an
empty chain. Source: arXiv:1010.3732, Section II.D.2, figure `fig:iso-injective`. -/
def incomingBondEquiv (D N : ℕ) :
    (Fin N → Fin (D * D)) ≃ (Fin N → Fin D × Fin D) where
  toFun s i := ((finProdFinEquiv.symm (s ((finRotate N).symm i))).2,
    (finProdFinEquiv.symm (s i)).1)
  invFun b i := finProdFinEquiv ((b i).2, (b (finRotate N i)).1)
  left_inv s := by
    funext i
    simp only [Equiv.symm_apply_apply, Prod.eta, Equiv.apply_symm_apply]
  right_inv b := by
    funext i
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.eta]

/-- The incoming-bond change of coordinates with each bond pair encoded
by the same physical alphabet of size `D²`. Source: arXiv:1010.3732,
Section II.D.2, figure `fig:iso-injective`. -/
def incomingBondPerm (D N : ℕ) : Equiv.Perm (Fin N → Fin (D * D)) :=
  (incomingBondEquiv D N).trans (Equiv.piCongrRight fun _ => finProdFinEquiv)

/-- The permutation of physical registers into incoming bonds is unitary
on the whole chain Hilbert space. Source: arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective`. -/
theorem incomingBondPerm_mem_unitaryGroup (D N : ℕ) :
    (incomingBondPerm D N).permMatrix ℂ ∈
      Matrix.unitaryGroup (Fin N → Fin (D * D)) ℂ :=
  (incomingBondPerm D N).permMatrix_mem_unitaryGroup

end MPSTensor
