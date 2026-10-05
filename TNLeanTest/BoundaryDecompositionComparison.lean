/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryDecompositionComparison

/-! # Exact-decomposition support comparison regressions -/

set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace BoundaryDecompositionComparisonTest

-- The two coordinate spaces can have different finite index types. Their
-- support need not be the identity of the ambient matrix algebra.
example {R m n k : Type*} [Semiring R] [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k]
    (S : Matrix m n R) (H : Matrix n m R)
    (S' : Matrix m k R) (H' : Matrix k m R)
    (hHS : H * S = 1) (hHS' : H' * S' = 1) (hSupport : S * H = S' * H') :
    (H' * S) * (H * S') = 1 ∧ (H * S') * (H' * S) = 1 := by
  obtain ⟨h1, h2, _, _⟩ := Matrix.comparison_of_common_support S H S' H' hHS hHS' hSupport
  exact ⟨h1, h2⟩

example {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d DB r : ℕ} {dim : Fin r → ℕ}
    {B : MPSTensor d DB} {A : ∀ c, MPSTensor d (dim c)}
    {f : ι → Fin r} {g : κ → Fin r}
    {V : ∀ i, Matrix (Fin (dim (f i))) (Fin DB) ℂ}
    {W : ∀ i, Matrix (Fin DB) (Fin (dim (f i))) ℂ}
    {V' : ∀ j, Matrix (Fin (dim (g j))) (Fin DB) ℂ}
    {W' : ∀ j, Matrix (Fin DB) (Fin (dim (g j))) ℂ}
    (h : MPSTensor.IsBiorthogonalDecomposition B (fun i ↦ A (f i)) V W)
    (h' : MPSTensor.IsBiorthogonalDecomposition B (fun j ↦ A (g j)) V' W')
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    (∑ i, W i * V i) = ∑ j, W' j * V' j :=
  h.support_eq_of_wordTupleSpanTop h' hL hSpan

/-- info: 'MPSTensor.IsBiorthogonalDecomposition.support_eq_of_wordTupleSpanTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBiorthogonalDecomposition.support_eq_of_wordTupleSpanTop
/-- info: 'Matrix.comparison_of_common_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.comparison_of_common_support

end BoundaryDecompositionComparisonTest
