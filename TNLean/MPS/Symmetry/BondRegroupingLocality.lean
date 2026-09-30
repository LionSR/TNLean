/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondRegrouping
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding
import TNLean.MPS.FundamentalTheorem.SectorBNT.FundamentalCoord

/-!
# Locality of the incoming-bond Hamiltonian

Regrouping incoming bonds places each one-bond interaction on the right
register of the preceding physical site and the left register of the current
site. The entry formula below includes identities on all other registers.
Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective` and equation `eq:phase-nosym:iso-hamiltonian`.
-/

namespace MPSTensor

/-- In physical coordinates a one-bond operator acts on precisely the registers
`(R_{i-1}, L_i)`, with identity factors on all remaining registers.
Source: arXiv:1010.3732, Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem incomingBondPerm_conj_local_apply {D N : ℕ} (hN : 1 ≤ N) (i : Fin N)
    (K : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (s t : Fin N → Fin (D * D)) :
    ((incomingBondPerm D N).permMatrix ℂ *
      MPOTensor.embedLocalOperator 1 N hN i (MPOTensor.oneSiteOperator K) *
      ((incomingBondPerm D N).permMatrix ℂ).conjTranspose) s t =
      ∏ j, if j = i then
        K (finProdFinEquiv (incomingBondEquiv D N s j))
          (finProdFinEquiv (incomingBondEquiv D N t j))
      else if incomingBondEquiv D N s j = incomingBondEquiv D N t j then 1 else 0 := by
  classical
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def, permMatrix_conj_eq_submatrix,
    ← MPOTensor.sitewiseMatrixFamily_mulSingle]
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
