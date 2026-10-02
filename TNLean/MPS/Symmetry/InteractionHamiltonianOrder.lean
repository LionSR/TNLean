/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedInteractionPath
import TNLean.MPS.MPDO.GSNNCHSectorSum
import Mathlib.Analysis.Matrix.Order

/-!
# Order and interpolation of periodic Hamiltonians

Summing the translates of a local interaction preserves positivity and
operator inequalities. It also commutes with affine interpolation. These
facts pass the endpoint comparison in Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2, from two sites to every periodic chain.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

/-- Affine interpolation of local interactions induces the same interpolation
of periodic Hamiltonians. Source: arXiv:1010.3732, Section II.F.2. -/
theorem interactionHamiltonian_add_smul_sub {d N : ℕ}
    (A B : MPOTensor.ChainOperator d 2) (t : ℝ) (hN : 2 ≤ N) :
    interactionHamiltonian (A + t • (B - A)) hN =
      interactionHamiltonian A hN +
        t • (interactionHamiltonian B hN - interactionHamiltonian A hN) := by
  have hmap (i : Fin N) :
      MPOTensor.embedLocalOperator 2 N hN i (A + t • (B - A)) =
        MPOTensor.embedLocalOperator 2 N hN i A +
          t • (MPOTensor.embedLocalOperator 2 N hN i B -
            MPOTensor.embedLocalOperator 2 N hN i A) := by
    let f := (MPOTensor.embedLocalOperatorAlgHom (d := d) 2 N hN i).toLinearMap
      |>.restrictScalars ℝ
    change f (A + t • (B - A)) = f A + t • (f B - f A)
    simp only [map_add, map_smul, map_sub]
  simp only [interactionHamiltonian, hmap]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum, smul_sub]

/-- A positive local interaction gives a positive periodic Hamiltonian.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem interactionHamiltonian_posSemidef {d N : ℕ}
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N) :
    (interactionHamiltonian A hN).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i hi
  exact MPOTensor.embedLocalOperator_posSemidef 2 hN i hA

/-- A local operator inequality holds for the sums of its translates on
every periodic chain. Source: arXiv:1010.3732, Section II.F.2. -/
theorem interactionHamiltonian_mono {d N : ℕ}
    {A B : MPOTensor.ChainOperator d 2} (hAB : A ≤ B) (hN : 2 ≤ N) :
    interactionHamiltonian A hN ≤ interactionHamiltonian B hN := by
  apply Finset.sum_le_sum
  intro i hi
  rw [Matrix.le_iff]
  have h := MPOTensor.embedLocalOperator_posSemidef 2 hN i (Matrix.le_iff.mp hAB)
  change ((MPOTensor.embedLocalOperatorAlgHom 2 N hN i) (B - A)).PosSemidef at h
  rw [map_sub] at h
  exact h

end MPSTensor
