/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciNIMRepDecomposition

/-!
# Regression tests for unrestricted Fibonacci representations

The four-block example is a sum of two regular representations. It satisfies all the
fusion equations, so indecomposability is essential for the two-block conclusion.
The empty-index example checks that the decomposition itself needs no nonemptiness assumption.
-/

open FibonacciCompression MPOTensor

namespace FibonacciNIMRepDecompositionTest

private def twoRegularCopies (a : Fin 2) (x y : Fin 2 × Fin 2) : ℕ :=
  if x.1 = y.1 then fibNim a x.2 y.2 else 0

private theorem twoRegularCopies_isNIMRep : IsNIMRep fibNim twoRegularCopies := by
  unfold IsNIMRep
  decide

private theorem twoRegularCopies_unit : ∀ x y, twoRegularCopies 0 x y =
    if x = y then 1 else 0 := by
  decide

-- A valid Fibonacci representation can have four blocks.
example : Fintype.card (Fin 2 × Fin 2) = 4 := by decide

example : ∃ σ : (Fin 2 × Fin 2) ≃
    {x // twoRegularCopies 1 x x = 0} × Fin 2, ∀ a x y,
    twoRegularCopies a x y =
      if (σ x).1 = (σ y).1 then fibNim a (σ x).2 (σ y).2 else 0 :=
  exists_equiv_prod_of_isNIMRep_fibNim twoRegularCopies_isNIMRep twoRegularCopies_unit

example : ¬ Matrix.IsIndecomposable (twoRegularCopies 1) := by
  intro h
  have hc := (exists_equiv_of_isIndecomposable_fibNim
    twoRegularCopies_isNIMRep twoRegularCopies_unit h).1
  norm_num at hc

example (T : Fin 0 → Fin 0 → ℕ) :
    ∃ σ : Fin 0 ≃ {x // T x x = 0} × Fin 2, ∀ x y,
      T x y = if (σ x).1 = (σ y).1 then fibFusionMatrix (σ x).2 (σ y).2 else 0 :=
  exists_equiv_prod_of_fibNim_sq T (fun x => Fin.elim0 x)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

-- No symmetry assumption is present in this signature.
example (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y) :
    ∀ x y, T x y = T y x :=
  fibNim_symmetric_of_sq T hsq

example [Nonempty κ] {M : Fin 2 → κ → κ → ℕ}
    (hM : IsNIMRep fibNim M) (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0)
    (hind : Matrix.IsIndecomposable (M 1)) :
    Fintype.card κ = 2 ∧ ∃ σ : κ ≃ Fin 2, ∀ a x y, M a x y = fibNim a (σ x) (σ y) :=
  exists_equiv_of_isIndecomposable_fibNim hM hunit hind

end FibonacciNIMRepDecompositionTest
