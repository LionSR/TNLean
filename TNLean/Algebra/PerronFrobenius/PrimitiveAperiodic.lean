/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Primitivity from returns of lengths two and three

An irreducible nonnegative finite matrix is primitive if every vertex of its
positive support has closed walks of lengths two and three. The proof chooses
one positive path between each ordered pair, bounds their lengths uniformly,
and pads every path to a common length using the two coprime return lengths.

This is the elementary matrix step used for the active sector trace matrix in
arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines 1451--1471.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem exists_two_mul_add_three_mul (N : ℕ) (hN : 2 ≤ N) :
    ∃ a b : ℕ, N = 2 * a + 3 * b := by
  rcases Nat.even_or_odd N with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, 0, by omega⟩
  · exact ⟨a - 1, 1, by omega⟩

private theorem pow_add_apply_pos_of_pos {T : Matrix n n ℝ}
    (hT : ∀ i j, 0 ≤ T i j) {a b : ℕ} {i j k : n}
    (ha : 0 < (T ^ a) i k) (hb : 0 < (T ^ b) k j) :
    0 < (T ^ (a + b)) i j := by
  rw [pow_add, Matrix.mul_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun l _ ↦
    mul_nonneg (Matrix.pow_apply_nonneg hT a i l)
      (Matrix.pow_apply_nonneg hT b l j))).2
    ⟨k, Finset.mem_univ k, mul_pos ha hb⟩

private theorem diagonal_two_mul_add_three_mul_pos {T : Matrix n n ℝ}
    (hT : ∀ i j, 0 ≤ T i j)
    (h2 : ∀ i, 0 < (T ^ 2) i i) (h3 : ∀ i, 0 < (T ^ 3) i i)
    (a b : ℕ) (i : n) :
    0 < (T ^ (2 * a + 3 * b)) i i := by
  have htwo : ∀ c : ℕ, 0 < (T ^ (2 * c)) i i := by
    intro c
    induction c with
    | zero => simp
    | succ c hc =>
        rw [Nat.mul_succ]
        exact pow_add_apply_pos_of_pos hT hc (h2 i)
  have hthree : ∀ c : ℕ, 0 < (T ^ (3 * c)) i i := by
    intro c
    induction c with
    | zero => simp
    | succ c hc =>
        rw [Nat.mul_succ]
        exact pow_add_apply_pos_of_pos hT hc (h3 i)
  exact pow_add_apply_pos_of_pos hT (htwo a) (hthree b)

/-- An irreducible nonnegative finite matrix with positive length-two and
length-three returns at every index is primitive. -/
theorem IsIrreducible.isPrimitive_of_pow_two_diagonal_pos_of_pow_three_diagonal_pos
    {T : Matrix n n ℝ} (hT : IsIrreducible T)
    (h2 : ∀ i, 0 < (T ^ 2) i i) (h3 : ∀ i, 0 < (T ^ 3) i i) :
    IsPrimitive T := by
  classical
  have hexists : ∀ i j : n, ∃ m : ℕ, 0 < m ∧ 0 < (T ^ m) i j :=
    (isIrreducible_iff_exists_pow_pos hT.nonneg).1 hT
  let m : n × n → ℕ := fun q ↦ Classical.choose (hexists q.1 q.2)
  have hmpos : ∀ i j : n, 0 < (T ^ m (i, j)) i j := fun i j ↦
    (Classical.choose_spec (hexists i j)).2
  let L : ℕ := ∑ q : n × n, m q
  refine ⟨hT.nonneg, 2 * L + 2, by omega, fun i j ↦ ?_⟩
  have hmL : m (i, j) ≤ L := by
    exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le (m q))
      (Finset.mem_univ (i, j))
  let r := 2 * L + 2 - m (i, j)
  have hmr : m (i, j) + r = 2 * L + 2 := by
    dsimp [r]
    exact Nat.add_sub_of_le (by omega)
  have hr : 2 ≤ r := by
    dsimp [r]
    omega
  obtain ⟨a, b, hab⟩ := exists_two_mul_add_three_mul r hr
  have hreturn : 0 < (T ^ r) j j := by
    rw [hab]
    exact diagonal_two_mul_add_three_mul_pos hT.nonneg h2 h3 a b j
  have hpositive : 0 < (T ^ (m (i, j) + r)) i j :=
    pow_add_apply_pos_of_pos hT.nonneg (hmpos i j) hreturn
  rwa [hmr] at hpositive

end Matrix
