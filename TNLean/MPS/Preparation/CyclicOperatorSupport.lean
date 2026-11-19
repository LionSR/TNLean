/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.WindowOperatorSupport
import TNLean.MPS.MPDO.GSNNCHSectorSum
import TNLean.Algebra.FinCyclicInduction

/-!
# Support of operators on a cyclic bond

Permuting the sites of a chain permutes the support of every operator
(`QuantumCircuit.supportedOperators_submatrix_siteEquiv`). Translating a
two-site window around the ring therefore places it in the algebra of its cyclic bond,
including the bond joining the last site to the first. The argument also applies to a
two-site ring, whose two oriented bonds have the same underlying support.

Source context: arXiv:1010.3732, Appendix C, and Hastings–Koma,
arXiv:math-ph/0507008, Appendix A, finite-volume local interactions.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators
open Matrix MPSTensor

namespace MPSPreparation

open QuantumCircuit

variable {d N : ℕ}

/-- A two-site operator on a cyclic bond acts on that bond, including the bond crossing
from the last site to the first. Source context: arXiv:1010.3732, Appendix C,
nearest-neighbour Hamiltonians on finite periodic chains. -/
theorem embedLocalOperator_twoSite_mem_supportedOperators [NeZero N] (hN : 2 ≤ N) (j : Fin N)
    (A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    MPOTensor.embedLocalOperator 2 N hN j A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
        (ringBond j) := by
  classical
  apply Fin.cyclic_induction (P := fun j ↦
    MPOTensor.embedLocalOperator 2 N hN j A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
        (ringBond j)) ?_ ?_ j
  · have h := MPSTensor.chainWindowOperator_mem_supportedOperators (d := d)
      (L := 2) (a := 0) (by omega : 0 < N) (by omega : 0 + 2 ≤ N) A
    rw [MPSTensor.chainWindowOperator_eq_embedLocalOperatorAlgHom
      (by omega : 0 < N) (by omega : 0 + 2 ≤ N)] at h
    change MPOTensor.embedLocalOperator 2 N hN 0 A ∈ _ at h
    refine ManyBody.supportedOperators_mono (D := Finset.univ.filter fun k : Fin N ↦ 0 ≤ k.val ∧
        k.val < 0 + 2) ?_ h
    intro k hk
    have hk' : k.val = 0 ∨ k.val = 1 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk; omega
    rcases hk' with hk' | hk'
    · have : k = 0 := Fin.ext (by simpa using hk')
      simp [ringBond, this]
    · have : k = 1 := Fin.ext (by simpa [Fin.val_one, Nat.mod_eq_of_lt hN] using hk')
      simp [ringBond, this]
  · intro i hi
    have h := supportedOperators_submatrix_siteEquiv (finRotate N) hi
    have himage : (ringBond i).image (finRotate N) = ringBond (i + 1) := by
      ext k
      simp [ringBond, finRotate_apply, add_assoc]
    rw [himage] at h
    have hrot : (MPOTensor.embedLocalOperator 2 N hN i A).submatrix
        (MPOTensor.rotateConfig N d) (MPOTensor.rotateConfig N d) ∈
          ManyBody.supportedOperators (fun _ ↦ Fin d) (ringBond (i + 1)) := by
      have hrc : (MPOTensor.rotateConfig N d : Cfg d N → Cfg d N) =
          fun σ ↦ σ ∘ finRotate N := funext (MPOTensor.rotateConfig_apply N d)
      rw [hrc]
      exact h
    simpa only [MPOTensor.embedLocalOperator_submatrix_rotateConfig, finRotate_apply] using hrot

end MPSPreparation
