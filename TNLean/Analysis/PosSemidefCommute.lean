/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Matrix.Order

/-!
# Products of commuting positive-semidefinite matrices

A product of two commuting positive-semidefinite matrices is positive
semidefinite, and so is the ordered product of any list of pairwise commuting
positive-semidefinite matrices.

## Main results

* `Matrix.PosSemidef.mul_of_commute`: the product of two commuting
  positive-semidefinite matrices is positive semidefinite.
* `Matrix.posSemidef_list_prod`: the product of a list of pairwise commuting
  positive-semidefinite matrices is positive semidefinite.
-/

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The product of two commuting positive-semidefinite matrices is positive
semidefinite: writing $A = \sqrt{A}\,\sqrt{A}$, the square root commutes with
$B$ as well, so $A B = \sqrt{A}^{\dagger}\,B\,\sqrt{A}$ is a conjugate of
$B$. -/
theorem PosSemidef.mul_of_commute {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hAB : A * B = B * A) : (A * B).PosSemidef := by
  have hcomm : Commute (CFC.sqrt A) B :=
    Commute.cfcₙ_nnreal ((commute_iff_eq A B).mpr hAB) NNReal.sqrt
  have hpsd : (CFC.sqrt A).PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have key : (CFC.sqrt A)ᴴ * B * CFC.sqrt A = A * B :=
    calc (CFC.sqrt A)ᴴ * B * CFC.sqrt A
        = CFC.sqrt A * B * CFC.sqrt A := by rw [hpsd.isHermitian.eq]
      _ = B * CFC.sqrt A * CFC.sqrt A := by rw [hcomm.eq]
      _ = B * (CFC.sqrt A * CFC.sqrt A) := by rw [mul_assoc]
      _ = B * A := by rw [CFC.sqrt_mul_sqrt_self A hA.nonneg]
      _ = A * B := hAB.symm
  rw [← key]
  exact hB.conjTranspose_mul_mul_same (CFC.sqrt A)

/-- The product of a list of pairwise commuting positive-semidefinite matrices
is positive semidefinite. -/
theorem posSemidef_list_prod {l : List (Matrix n n ℂ)}
    (hpos : ∀ A ∈ l, A.PosSemidef)
    (hcomm : l.Pairwise fun A B => A * B = B * A) : l.prod.PosSemidef := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact PosSemidef.one
  | cons A l ih =>
    rw [List.pairwise_cons] at hcomm
    rw [List.prod_cons]
    have hA : A.PosSemidef := hpos A (by simp)
    have hl : l.prod.PosSemidef :=
      ih (fun B hB => hpos B (List.mem_cons_of_mem A hB)) hcomm.2
    exact hA.mul_of_commute hl (Commute.list_prod_right l A fun C hC => hcomm.1 C hC).eq

end Matrix
