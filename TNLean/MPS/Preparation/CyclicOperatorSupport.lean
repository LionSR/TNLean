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

Permuting the sites of a chain permutes the support of every operator. Translating a
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

/-- Permuting the sites permutes the support of an operator. Source context:
Hastings–Koma, arXiv:math-ph/0507008, Appendix A, finite-volume local interactions. -/
theorem supportedOperators_submatrix_siteEquiv {S : Set (Fin N)}
    (p : Equiv.Perm (Fin N)) {A : Matrix (Cfg d N) (Cfg d N) ℂ}
    (hA : A ∈ supportedOperators d S) :
    A.submatrix (fun σ ↦ σ ∘ p) (fun σ ↦ σ ∘ p) ∈
      supportedOperators d (p '' S) := by
  classical
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨m, hm, rfl⟩ := hA
    have heq : (rectKronecker m).submatrix (fun σ ↦ σ ∘ p) (fun σ ↦ σ ∘ p) =
        rectKronecker (fun k ↦ m (p.symm k)) := by
      ext σ τ
      simp only [Matrix.submatrix_apply, rectKronecker_apply, Function.comp_apply]
      exact (Fintype.prod_equiv p (fun k ↦ m k (σ (p k)) (τ (p k)))
        (fun k ↦ m (p.symm k) (σ k) (τ k)) (by simp))
    rw [heq]
    exact rectKronecker_mem_supportedOperators fun k hk ↦ hm _ (by
      intro h; exact hk ⟨p.symm k, h, p.apply_symm_apply k⟩)
  | zero => simp
  | add A B _ _ hA hB =>
    exact Submodule.add_mem _ hA hB
  | smul c A _ hA =>
    exact Submodule.smul_mem _ c hA

/-- A two-site operator on a cyclic bond acts on that bond, including the bond crossing
from the last site to the first. Source context: arXiv:1010.3732, Appendix C,
nearest-neighbour Hamiltonians on finite periodic chains. -/
theorem embedLocalOperator_twoSite_mem_supportedOperators [NeZero N] (hN : 2 ≤ N) (j : Fin N)
    (A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    MPOTensor.embedLocalOperator 2 N hN j A ∈ supportedOperators d (bond j) := by
  classical
  apply Fin.cyclic_induction (P := fun j ↦
    MPOTensor.embedLocalOperator 2 N hN j A ∈ supportedOperators d (bond j)) ?_ ?_ j
  · have h := MPSTensor.chainWindowOperator_mem_supportedOperators (d := d)
      (L := 2) (a := 0) (by omega : 0 < N) (by omega : 0 + 2 ≤ N) A
    rw [MPSTensor.chainWindowOperator_eq_embedLocalOperatorAlgHom
      (by omega : 0 < N) (by omega : 0 + 2 ≤ N)] at h
    change MPOTensor.embedLocalOperator 2 N hN 0 A ∈ _ at h
    refine supportedOperators_mono (S := {k : Fin N | 0 ≤ k.val ∧ k.val < 0 + 2}) ?_ h
    intro k hk
    have hk' : k.val = 0 ∨ k.val = 1 := by simp only [Set.mem_ofPred_eq] at hk; omega
    rcases hk' with hk' | hk'
    · have : k = 0 := Fin.ext (by simpa using hk')
      simp [bond, this]
    · have : k = 1 := Fin.ext (by simpa [Fin.val_one, Nat.mod_eq_of_lt hN] using hk')
      simp [bond, this]
  · intro i hi
    have h := supportedOperators_submatrix_siteEquiv (finRotate N) hi
    have himage : (finRotate N) '' bond i = bond (i + 1) := by
      ext k
      simp [bond, Set.image_insert_eq, finRotate_apply, add_assoc]
    rw [himage] at h
    have hrot : (MPOTensor.embedLocalOperator 2 N hN i A).submatrix
        (MPOTensor.rotateConfig N d) (MPOTensor.rotateConfig N d) ∈
          supportedOperators d (bond (i + 1)) := by
      have hrc : (MPOTensor.rotateConfig N d : Cfg d N → Cfg d N) =
          fun σ ↦ σ ∘ finRotate N := funext (MPOTensor.rotateConfig_apply N d)
      rw [hrc]
      exact h
    simpa only [MPOTensor.embedLocalOperator_submatrix_rotateConfig, finRotate_apply] using hrot

end MPSPreparation
