/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.SourcePreparation
import QICLean.Analysis.SourceContraction
import Mathlib.Logic.Equiv.Prod

/-! # Finite contraction of source columns

Contracting the outer products of the ket and bra columns gives the product
source matrix between those column matrices. The calculation includes empty
source inventories and arbitrary complex source matrices.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`, lines 279–355
  and 409–434.
-/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace SourceInventory
/-- The literal matrix product over the recorded source positions.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588. -/
def productSourceMatrix (R : SourceInventory P) {K : Fin R.length → Type}
    (X : ∀ i, Matrix (K i) (K i) ℂ) :
    Matrix (∀ i, K i) (∀ i, K i) ℂ := fun a b => ∏ i, X i (a i) (b i)

/-- Contracting the explicit outer products of ket and bra columns equals
multiplication by the literal product source matrix. This finite algebraic
identity does not assert any factorization of a supplied circuit.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 409–434. -/
theorem sourceContraction_columns_eq_mul (R : SourceInventory P)
    {K : Fin R.length → Type} [∀ i, Fintype (K i)] {m n : Type}
    (L : Matrix m (∀ i, K i) ℂ) (M : Matrix n (∀ i, K i) ℂ)
    (X : ∀ i, Matrix (K i) (K i) ℂ) :
    Matrix.sourceContraction (fun x => Matrix.vecMulVec
      (fun r => L r (fun i => (x i).1))
      (fun s => conj (M s (fun i => (x i).2)))) X =
      L * productSourceMatrix R X * Mᴴ := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Fin R.length) K K
  ext r s
  rw [Matrix.sourceContraction_apply_apply]
  change (∑ x : ∀ i : Fin R.length, K i × K i,
    (L r (fun i => (x i).1) * conj (M s (fun i => (x i).2))) *
    ∏ i, X i (x i).1 (x i).2) = _
  rw [← e.symm.sum_comp]
  change (∑ x : ((∀ i, K i) × (∀ i, K i)),
    (L r x.1 * conj (M s x.2)) * ∏ i, X i (x.1 i) (x.2 i)) = _
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, productSourceMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.conjTranspose_apply, starRingEnd_apply]
  exact mul_right_comm _ _ _

end SourceInventory
end TNLean.PEPS.PairEffect
