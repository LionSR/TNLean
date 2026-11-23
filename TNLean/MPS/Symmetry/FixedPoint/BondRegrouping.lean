/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import Mathlib.Logic.Equiv.Fin.Rotate
import TNLean.MPS.Operator.Interaction.PhysicalGibbsEmbedding
import TNLean.MPS.FundamentalTheorem.Sectors.FundamentalCoord

/-!
# Regrouping physical registers into neighboring bonds

A physical site has a left and a right virtual register. The incoming bond
at site `i` consists of the right register at its cyclic predecessor and
the left register at `i`. This is a permutation of the entire configuration
basis. It is the change of coordinates used for the independent-bond parent
Hamiltonian in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective` and equation `eq:phase-nosym:iso-hamiltonian`.

No assertion about the depth of a circuit on whole physical sites is made.

## Locality of the incoming-bond Hamiltonian

Regrouping incoming bonds places each one-bond interaction on the right
register of the preceding physical site and the left register of the current
site. The entry formula below includes identities on all other registers.
Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective` and equation `eq:phase-nosym:iso-hamiltonian`.
-/

section

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

end

section

namespace MPSTensor

/-- In physical coordinates a one-bond operator acts on precisely the registers
`(R_{i-1}, L_i)`, with identity factors on all remaining registers.
Source: arXiv:1010.3732, Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem incomingBondPerm_conj_local_apply {D N : ℕ} (hN : 1 ≤ N) (i : Fin N)
    (K : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (s t : Fin N → Fin (D * D)) :
    ((incomingBondPerm D N).permMatrix ℂ *
      ManyBody.placeAlong (X := fun _ ↦ Fin (D * D)) (ManyBody.ringWindow hN i)
        (MPOTensor.oneSiteOperator K) *
      ((incomingBondPerm D N).permMatrix ℂ).conjTranspose) s t =
      ∏ j, if j = i then
        K (finProdFinEquiv (incomingBondEquiv D N s j))
          (finProdFinEquiv (incomingBondEquiv D N t j))
      else if incomingBondEquiv D N s j = incomingBondEquiv D N t j then 1 else 0 := by
  classical
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def, permMatrix_conj_eq_submatrix,
    ← MPOTensor.piKronecker_mulSingle]
  change (∏ j, (Pi.mulSingle
    (M := fun _ : Fin N => Matrix (Fin (D * D)) (Fin (D * D)) ℂ) i K) j
    (incomingBondPerm D N s j) (incomingBondPerm D N t j)) = _
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [incomingBondPerm]
  · simp [hji, Matrix.one_apply, incomingBondPerm]

end MPSTensor

end
