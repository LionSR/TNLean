/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Virtual rescaling for two-block uncle Hamiltonians

The printed uncle-Hamiltonian proof rescales both off-diagonal virtual blocks.
This preserves the one-site boundary-map range when the scaling factor is
nonzero. It is an invertible linear change of virtual matrix coordinates,
not in general a similarity gauge.

Source: arXiv:1210.6613, proof of Theorem `thm:unclehamiltonian`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Multiply both off-diagonal virtual blocks by the same scalar. -/
def twoBlockVirtualScale {a b : ℕ} (z : ℂ)
    (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  fun i j => if (i.val < a ↔ j.val < a) then M i j else z * M i j

/-- Off-diagonal virtual rescaling is self-adjoint for the bilinear trace
pairing; no complex conjugation occurs in this pairing. -/
theorem trace_twoBlockVirtualScale_mul {a b : ℕ} (z : ℂ)
    (M X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix.trace (twoBlockVirtualScale (a := a) z M * X) =
      Matrix.trace (M * twoBlockVirtualScale (a := a) z X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [twoBlockVirtualScale]
  by_cases h : i.val < a ↔ j.val < a
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · have h' : ¬ (j.val < a ↔ i.val < a) := fun h' => h h'.symm
    rw [ite_eq_right h, ite_eq_right h']
    ring

/-- Reciprocal nonzero scaling recovers the original virtual matrix. -/
theorem twoBlockVirtualScale_inv {a b : ℕ} {z : ℂ} (hz : z ≠ 0)
    (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    twoBlockVirtualScale (a := a) z (twoBlockVirtualScale (a := a) z⁻¹ M) = M := by
  ext i j
  simp only [twoBlockVirtualScale]
  split_ifs <;> simp [hz]

/-- The bilinear boundary map transfers virtual rescaling to its boundary
matrix, rather than treating it as a similarity gauge. -/
theorem groundSpaceMap_twoBlockVirtualScale_one {d a b : ℕ} (z : ℂ)
    (T : MPSTensor d (a + b)) (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    groundSpaceMap (fun i => twoBlockVirtualScale (a := a) z (T i)) 1 X =
      groundSpaceMap T 1 (twoBlockVirtualScale (a := a) z X) := by
  funext σ
  simpa only [groundSpaceMap_apply, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one] using
      trace_twoBlockVirtualScale_mul (a := a) z (T (σ 0)) X

/-- Nonzero off-diagonal rescaling preserves the full physical boundary-map
range of a blocked tensor. -/
theorem groundSpace_twoBlockVirtualScale_one {d a b : ℕ} {z : ℂ} (hz : z ≠ 0)
    (T : MPSTensor d (a + b)) :
    groundSpace (fun i => twoBlockVirtualScale (a := a) z (T i)) 1 =
      groundSpace T 1 := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    exact ⟨twoBlockVirtualScale (a := a) z X,
      (groundSpaceMap_twoBlockVirtualScale_one z T X).symm⟩
  · rintro _ ⟨X, rfl⟩
    refine ⟨twoBlockVirtualScale (a := a) z⁻¹ X, ?_⟩
    rw [groundSpaceMap_twoBlockVirtualScale_one, twoBlockVirtualScale_inv hz]

end MPSTensor
