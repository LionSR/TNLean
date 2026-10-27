/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixFactorExchange
import Mathlib.Basic.Complex.Basic

/-! Applications and axiom checks for exchange of the middle matrix factor. -/

open scoped BigOperators Kronecker

/-- info:
'Matrix.reindex_kronecker_middleFactorExchange' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.reindex_kronecker_middleFactorExchange

/-- info:
'Matrix.reindex_sum_kronecker_middleFactorExchange' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.reindex_sum_kronecker_middleFactorExchange

/-- info:
'Matrix.card_exchangedMiddleFamily_index' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.card_exchangedMiddleFamily_index

-- Noncommuting coefficient matrices retain their original multiplication order.
example :
    let R := Matrix (Fin 2) (Fin 2) ℂ
    let M : Matrix (Fin 2 × Unit) (Fin 2 × Unit) R :=
      Matrix.single (0, ()) (1, ()) (Matrix.single 0 1 1)
    let V : Matrix (Fin 2 × Unit) (Fin 2 × Unit) R :=
      Matrix.single (1, ()) (0, ()) (Matrix.single 1 0 1)
    (∑ a₀, ∑ a₁, ∑ b₀, ∑ b₁,
      (Matrix.single a₀ a₁ (1 : R) ⊗ₖ Matrix.operatorBlock M b₀ b₁) ⊗ₖ
        Matrix.exchangedMiddleFactor V a₀ a₁ b₀ b₁)
      ((1, ()), (0, ())) ((0, ()), (1, ())) = Matrix.single 0 0 1 := by
  intro R M V
  rw [← Matrix.reindex_kronecker_middleFactorExchange M V]
  simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  change Matrix.single (0 : Fin 2) 1 (1 : ℂ) * Matrix.single 1 0 1 = Matrix.single 0 0 1
  simp

-- Empty transferred coordinates require no chosen configuration.
example (M : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ)
    (V : Matrix (Fin 0 × Unit) (Fin 0 × Unit) ℂ) :
    (M ⊗ₖ V).reindex Matrix.middleFactorExchangeEquiv Matrix.middleFactorExchangeEquiv = 0 := by
  rw [Matrix.reindex_kronecker_middleFactorExchange]
  simp

example : Fintype.card (Fin 3 × (Fin 2 × Fin 2) × (Fin 3 × Fin 3)) = 108 := by
  rw [Matrix.card_exchangedMiddleFamily_index]
  norm_num
