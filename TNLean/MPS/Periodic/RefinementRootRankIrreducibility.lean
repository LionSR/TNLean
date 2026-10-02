/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.RefinementRootRankCounterexample
import TNLean.MPS.Periodic.RefinementRootRankChannelSquare
import TNLean.MPS.Periodic.RefinementRootIrreducibility
import TNLean.MPS.Core.BlockingTransfer
import QICLean.Kraus.IrreducibleAction

/-!
# Irreducibility of the seven-dimensional cyclic-reset channel

The two-step matrix units act transitively on the five cyclic sectors.
Consequently the square channel, and hence its root, have no nontrivial
invariant subspace.

Source context: arXiv:1708.00029, Theorem 4.1. The example concerns the
rank of a specified channel root; it does not obstruct selecting another root.
-/

open scoped Matrix

namespace MPSTensor.CyclicResetCounterexample

private theorem square_unit_preserves
    (W : Submodule ℂ (Fin 7 → ℂ))
    (hW : Matrix.IsInvariantSubmodule square W)
    (a b : Fin 7) (hab : sector a = sector b + 2)
    (v : Fin 7 → ℂ) (hv : v ∈ W) :
    (Matrix.stdBasis ℂ (Fin 7) (Fin 7) (a, b)).mulVec v ∈ W := by
  let i : Fin 9 := twoStepIndex.symm ⟨(a,b),hab⟩
  have hi := hW i v hv
  have hi' : outputWeight a •
      (Matrix.stdBasis ℂ (Fin 7) (Fin 7) (a,b)).mulVec v ∈ W := by
    simpa only [square, i, Equiv.apply_symm_apply, Matrix.smul_mulVec] using hi
  have := W.smul_mem (outputWeight a)⁻¹ hi'
  simpa only [smul_smul, inv_mul_cancel₀ (outputWeight_ne_zero a), one_smul] using this

private def sectorRepresentative : Fin 5 → Fin 7 := ![0, 1, 3, 5, 6]

private theorem sector_sectorRepresentative (s : Fin 5) :
    sector (sectorRepresentative s) = s := by
  fin_cases s <;> decide

private theorem five_two_steps_cover (s t : Fin 5) :
    t = s + 2 ∨
    t = (s + 2) + 2 ∨
    t = ((s + 2) + 2) + 2 ∨
    t = (((s + 2) + 2) + 2) + 2 ∨
    t = ((((s + 2) + 2) + 2) + 2) + 2 := by
  fin_cases s <;> fin_cases t <;> decide

private theorem standardUnit_mulVec (a b : Fin 7) (v : Fin 7 → ℂ) :
    (Matrix.stdBasis ℂ (Fin 7) (Fin 7) (a, b)).mulVec v =
      v b • Pi.single a (1 : ℂ) := by
  ext x
  simp [Matrix.stdBasis_eq_single, Matrix.single_mulVec, Pi.single_apply,
    Function.update_apply]

/-- The nine two-step matrix units act irreducibly on the seven-dimensional
bond space. Source context: arXiv:1708.00029, Theorem 4.1 converse. -/
theorem square_isIrreducibleFamily : Kraus.IsIrreducibleFamily square := by
  classical
  apply Kraus.isIrreducibleFamily_of_isIrreducibleAction square
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hbot
  obtain ⟨b, hb⟩ : ∃ b : Fin 7, v b ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hstep (a b : Fin 7) (hab : sector a = sector b + 2)
      (v : Fin 7 → ℂ) (hv : v ∈ W) (hvb : v b ≠ 0) :
      Pi.single a (1 : ℂ) ∈ W := by
    have h := square_unit_preserves W hW a b hab v hv
    rw [standardUnit_mulVec] at h
    have h' := W.smul_mem (v b)⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ hvb, one_smul] using h'
  have hnext (s : Fin 5)
      (hs : ∀ a : Fin 7, sector a = s → Pi.single a (1 : ℂ) ∈ W) :
      ∀ a : Fin 7, sector a = s + 2 → Pi.single a (1 : ℂ) ∈ W := by
    intro a ha
    let b := sectorRepresentative s
    have hbW : Pi.single b (1 : ℂ) ∈ W :=
      hs b (sector_sectorRepresentative s)
    apply hstep a b (by simpa only [b, sector_sectorRepresentative] using ha)
      (Pi.single b (1 : ℂ)) hbW
    simp [b]
  let s := sector b
  have h1 : ∀ a : Fin 7, sector a = s + 2 → Pi.single a (1 : ℂ) ∈ W := by
    intro a ha
    exact hstep a b ha v hv hb
  have h2 := hnext (s + 2) h1
  have h3 := hnext ((s + 2) + 2) h2
  have h4 := hnext (((s + 2) + 2) + 2) h3
  have h5 := hnext ((((s + 2) + 2) + 2) + 2) h4
  have hall (a : Fin 7) : Pi.single a (1 : ℂ) ∈ W := by
    rcases five_two_steps_cover s (sector a) with h | h | h | h | h
    · exact h1 a h
    · exact h2 a h
    · exact h3 a h
    · exact h4 a h
    · exact h5 a h
  apply top_unique
  intro w _
  rw [← Finset.univ_sum_single w]
  apply Submodule.sum_mem
  intro a _
  have heq : Pi.single a (w a) = w a • Pi.single a (1 : ℂ) := by
    ext x
    by_cases h : x = a <;> simp [h]
  rw [heq]
  exact W.smul_mem (w a) (hall a)

/-- The original cyclic-reset root is irreducible because its square is.
Source context: arXiv:1708.00029, Theorem 4.1 converse. -/
theorem root_isIrreducibleFamily : Kraus.IsIrreducibleFamily root := by
  apply isIrreducibleFamily_of_transferMap_eq_blockTensor square root 2
    square_isIrreducibleFamily
  rw [transferMap_blockTensor]
  exact transferMap_square_eq_pow

end MPSTensor.CyclicResetCounterexample
