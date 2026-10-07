/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularFourierMatrix
import TNLean.PEPS.RegularMatrixEquiv
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Strict dimension reduction in regular matrix coordinates

An actual matrix intertwiner between the regular representation and its
irreducible blocks suffices to characterize noncommutativity. Some block has
dimension greater than one exactly when the group is noncommutative. If the
intertwiner is an isometry, this is also exactly when the single-copy dimension
is strictly smaller than the group order.

These statements are mathematical consequences of SCP10, arXiv:1001.3807,
Section 7, lines 2947–2988. They do not require a chosen orthonormal Fourier
basis or any lattice geometry.
-/

open scoped Matrix Kronecker
namespace TNLean.PEPS
open Representation
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- In actual regular matrix coordinates, a sector has dimension greater than
one exactly when the group is noncommutative. Mathematical consequence of
SCP10, Section 7, lines 2947–2988. -/
theorem exists_dimension_gt_one_iff_not_isMulCommutative_of_regular_intertwiner
    {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (hirr : ∀ i, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    (∃ i, 1 < d i) ↔ ¬ IsMulCommutative G := by
  classical
  constructor
  · rintro ⟨i, hi⟩ hcomm
    let := hcomm
    let := hirr i
    have hone : d i = 1 := by
      simpa using IsIrreducible.finrank_eq_one_of_isMulCommutative
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))
    omega
  · intro hnoncomm
    by_contra hdim
    push Not at hdim
    have hone : ∀ i, d i = 1 := fun i => Nat.le_antisymm (hdim i) (hd i)
    have hfaithful : Function.Injective
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (leftRegularMatrix G)) :=
      (linearIndependent_of_isSemiRegular _ isSemiRegular_leftRegularMatrix).injective
    apply hnoncomm
    apply isMulCommutative_iff.mpr
    intro g h
    apply hfaithful
    change Matrix.toLinAlgEquiv' (leftRegularMatrix G (g * h)) =
      Matrix.toLinAlgEquiv' (leftRegularMatrix G (h * g))
    congr 1
    rw [hreg, hreg]
    congr 2
    change Matrix.blockDiagonal' (fun i => D i (g * h) ⊗ₖ (1 : Matrix _ _ ℂ)) =
      Matrix.blockDiagonal' (fun i => D i (h * g) ⊗ₖ (1 : Matrix _ _ ℂ))
    congr 1
    funext i
    have : Subsingleton (Fin (d i)) := by rw [hone i]; infer_instance
    have hc : D i g * D i h = D i h * D i g := by
      rw [← (Matrix.isDiag_of_subsingleton (D i g)).diagonal_diag,
        ← (Matrix.isDiag_of_subsingleton (D i h)).diagonal_diag]
      exact (Matrix.commute_diagonal _ _).eq
    rw [map_mul, map_mul, hc]

/-- An isometric regular matrix intertwiner exhibits strict single-copy dimension
reduction precisely for noncommutative groups. Mathematical consequence of
SCP10, Section 7, lines 2947–2988. -/
theorem sum_dimensions_lt_card_iff_not_isMulCommutative_of_regular_intertwiner
    {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (hirr : ∀ i, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ) (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    (∑ i, d i) < Fintype.card G ↔ ¬ IsMulCommutative G :=
  (bondDimensions_of_regular_intertwiner d D hd Q hQ hreg).2.2.2.trans
    (exists_dimension_gt_one_iff_not_isMulCommutative_of_regular_intertwiner
      d D hd hirr Q hreg)

end TNLean.PEPS
