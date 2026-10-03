/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Unitary assembly of a resolution of the bond space

A family of column matrices whose range operators sum to the identity and whose
column counts sum to the ambient dimension concatenates to a unitary matrix.
If each column matrix intertwines a tensor with one block, this unitary identifies
the tensor with the direct sum of those blocks while retaining every inclusion.

This is the change of bond coordinates implicit in arXiv:1708.00029,
`lem:blocking-arbitrary`, lines 432–456, used before Theorem 4.1's phase construction.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {D r : ℕ} {dim : Fin r → ℕ}

private theorem exists_unitary_with_columns (V : (a : Fin r) → Matrix (Fin D) (Fin (dim a)) ℂ)
    (hsum : ∑ a, V a * (V a)ᴴ = 1) (hdim : ∑ a, dim a = D) :
    ∃ U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ,
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      ∀ x a y, U x (finSigmaFinEquiv ⟨a, y⟩) = V a x y := by
  let U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ :=
    fun x y ↦ V ((finSigmaFinEquiv (n := dim)).symm y).1 x ((finSigmaFinEquiv (n := dim)).symm y).2
  have hinv (s : (a : Fin r) × Fin (dim a)) :
      (finSigmaFinEquiv (n := dim)).symm (finSigmaFinEquiv s) = s :=
    (finSigmaFinEquiv (n := dim)).symm_apply_apply s
  have hU (x a y) : U x (finSigmaFinEquiv ⟨a, y⟩) = V a x y := by
    dsimp only [U]
    rw [hinv]
  have hco : U * Uᴴ = 1 := by
    rw [← hsum]
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]
    rw [← Equiv.sum_comp (finSigmaFinEquiv (n := dim))]
    simp only [Fintype.sum_sigma, hU]
  refine ⟨U, hco, ?_, ?_⟩
  · exact (Matrix.IsCoisometry.isUnitaryBetween_of_card_eq U hco
      (by simpa using hdim.symm)).1
  · exact hU

private theorem mul_blockInclusion_apply (U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ)
    (a : Fin r) (x : Fin D) (y : Fin (dim a)) :
    (U * blockInclusion dim a) x y = U x (finSigmaFinEquiv ⟨a, y⟩) := by
  simp [Matrix.mul_apply, blockInclusion_apply]

/-- Assemble an identity resolution into a unitary block decomposition, preserving
its prescribed inclusions. The total column count prevents a proper coisometry.
Source: arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432–456. -/
theorem exists_unitary_toTensorFromBlocks_of_resolution {d : ℕ} (A : MPSTensor d D)
    (B : (a : Fin r) → MPSTensor d (dim a))
    (V : (a : Fin r) → Matrix (Fin D) (Fin (dim a)) ℂ)
    (hsum : ∑ a, V a * (V a)ᴴ = 1) (hdim : ∑ a, dim a = D)
    (hinter : ∀ a i, A i * V a = V a * B a i) :
    ∃ U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ,
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      (∀ a, U * blockInclusion dim a = V a) ∧
      ∀ i, A i = U * toTensorFromBlocks (fun _ ↦ 1) B i * Uᴴ := by
  obtain ⟨U, hco, hiso, hU⟩ := exists_unitary_with_columns V hsum hdim
  have hinc (a) : U * blockInclusion dim a = V a := by
    ext x y
    rw [mul_blockInclusion_apply, hU]
  refine ⟨U, hco, hiso, hinc, ?_⟩
  intro i
  have hi : A i * U = U * toTensorFromBlocks (fun _ ↦ 1) B i := by
    ext x y
    obtain ⟨⟨a, z⟩, rfl⟩ := finSigmaFinEquiv.surjective y
    have he : (A i * U) * blockInclusion dim a =
        (U * toTensorFromBlocks (fun _ ↦ 1) B i) * blockInclusion dim a := by
      rw [Matrix.mul_assoc, hinc, hinter, Matrix.mul_assoc,
        toTensorFromBlocks_mul_blockInclusion, one_smul, ← Matrix.mul_assoc, hinc]
    simpa only [mul_blockInclusion_apply] using congrFun (congrFun he x) z
  calc
    A i = A i * (U * Uᴴ) := by rw [hco, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hi]

end MPSTensor
