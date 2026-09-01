/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommutingStarSubalgebraProduct
import TNLean.QCA.BipartiteSupportAlgebra

/-!
# Canonical coordinates for products of commuting matrix factors

The canonical embeddings of two matrix star-subalgebras into a bipartite matrix algebra commute.
The underlying complex vector space of their algebraic join is the Kronecker-product span of the
two original subspaces.

This coordinate statement is distinct from the abstract full-matrix presentation of a pair of
commuting factors: an arbitrary common ambient matrix algebra has no distinguished bipartite
coordinates.

## Main result

* `Matrix.leftKroneckerEmbed_sup_rightKroneckerEmbed_toSubmodule` identifies the canonical join
  with `Matrix.kroneckerSubmodule`.

## References

* B. Schumacher and R. F. Werner, *Reversible quantum cellular automata*,
  quant-ph/0405174, Proposition `Cscom`, lines 2119--2138.
* D. Gross, V. Nesme, H. Vogts, and R. F. Werner, *Index theory of one-dimensional quantum walks
  and cellular automata*, arXiv:0910.3675v2, lines 1270--1308.
-/

open scoped Kronecker

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

private theorem leftKroneckerEmbed_mul_rightKroneckerEmbed
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    leftKroneckerEmbed (n := n) A * rightKroneckerEmbed (m := m) B = A ⊗ₖ B := by
  rw [leftKroneckerEmbed_apply, rightKroneckerEmbed_apply, ← mul_kronecker_mul,
    mul_one, one_mul]

private theorem rightKroneckerEmbed_mul_leftKroneckerEmbed
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    rightKroneckerEmbed (m := m) B * leftKroneckerEmbed (n := n) A = A ⊗ₖ B := by
  rw [leftKroneckerEmbed_apply, rightKroneckerEmbed_apply, ← mul_kronecker_mul,
    one_mul, mul_one]

private theorem left_right_kronecker_commute
    (S : StarSubalgebra ℂ (Matrix m m ℂ)) (T : StarSubalgebra ℂ (Matrix n n ℂ)) :
    ∀ a : S.map (leftKroneckerEmbed (n := n)),
      ∀ b : T.map (rightKroneckerEmbed (m := m)),
        Commute (a : Matrix (m × n) (m × n) ℂ) (b : Matrix (m × n) (m × n) ℂ) := by
  intro a b
  obtain ⟨A, _, hA⟩ := StarSubalgebra.mem_map.mp a.2
  obtain ⟨B, _, hB⟩ := StarSubalgebra.mem_map.mp b.2
  change (a : Matrix (m × n) (m × n) ℂ) * b = b * a
  rw [← hA, ← hB, leftKroneckerEmbed_mul_rightKroneckerEmbed,
    rightKroneckerEmbed_mul_leftKroneckerEmbed]

private theorem left_right_kronecker_mul_toSubmodule
    (S : StarSubalgebra ℂ (Matrix m m ℂ)) (T : StarSubalgebra ℂ (Matrix n n ℂ)) :
    (S.map (leftKroneckerEmbed (n := n))).toSubmodule *
        (T.map (rightKroneckerEmbed (m := m))).toSubmodule =
      kroneckerSubmodule S.toSubmodule T.toSubmodule := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro X hX Y hY
    obtain ⟨A, hA, hAX⟩ := StarSubalgebra.mem_map.mp hX
    obtain ⟨B, hB, hBY⟩ := StarSubalgebra.mem_map.mp hY
    rw [← hAX, ← hBY, leftKroneckerEmbed_mul_rightKroneckerEmbed]
    exact Submodule.apply_mem_map₂ Matrix.kroneckerBilinear hA hB
  · rw [kroneckerSubmodule, Submodule.map₂_le]
    intro A hA B hB
    change A ⊗ₖ B ∈
      (S.map (leftKroneckerEmbed (n := n))).toSubmodule *
        (T.map (rightKroneckerEmbed (m := m))).toSubmodule
    rw [← leftKroneckerEmbed_mul_rightKroneckerEmbed]
    exact Submodule.mul_mem_mul (StarSubalgebra.mem_map.mpr ⟨A, hA, rfl⟩)
      (StarSubalgebra.mem_map.mpr ⟨B, hB, rfl⟩)

/-- In canonical bipartite coordinates, the join of the left and right embedded factors has
underlying vector space equal to the Kronecker-product span. This is the coordinate identity used
for the commuting support algebras in GNVW, arXiv:0910.3675v2, lines 1270--1308. -/
theorem leftKroneckerEmbed_sup_rightKroneckerEmbed_toSubmodule
    (S : StarSubalgebra ℂ (Matrix m m ℂ)) (T : StarSubalgebra ℂ (Matrix n n ℂ)) :
    (S.map (leftKroneckerEmbed (n := n)) ⊔
        T.map (rightKroneckerEmbed (m := m))).toSubmodule =
      kroneckerSubmodule S.toSubmodule T.toSubmodule := by
  cases isEmpty_or_nonempty m with
  | inl _ =>
      apply Submodule.ext
      intro X
      have hX : X = 0 := Subsingleton.elim _ _
      subst X
      simp
  | inr hm =>
      let _ : Nonempty m := hm
      cases isEmpty_or_nonempty n with
      | inl _ =>
          apply Submodule.ext
          intro X
          have hX : X = 0 := Subsingleton.elim _ _
          subst X
          simp
      | inr hn =>
          let _ : Nonempty n := hn
          rw [StarSubalgebra.sup_toSubmodule_eq_mul _ _ (left_right_kronecker_commute S T)]
          exact left_right_kronecker_mul_toSubmodule S T

end Matrix
