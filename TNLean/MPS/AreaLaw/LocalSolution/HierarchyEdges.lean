/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteFinalState

/-!
# The edges of the binary hierarchy

For consecutive supersites numbered from zero, edge `j` joins supersites `j-1`
and `j`. The edge joining the halves of block `k` at level `m+1` is therefore
`(2k+1) 2^m`. Each internal edge occurs exactly once in the hierarchy.
The additional edge closing the periodic chain is treated separately.

This is the grouping of Hastings, arXiv:cond-mat/0508554v3, Section II,
lines 609–628 and 668–720.
-/

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The edge joining the two halves of block `k` at level `m+1`.
Hastings, arXiv:cond-mat/0508554v3, lines 668–685. -/
def hierarchyEdge {A : Type*} (a : ℕ → A) (m k : ℕ) : A :=
  a ((2 * k + 1) * 2 ^ m)

/-- Every internal edge of a block appears exactly once in its hierarchy.
Hastings, arXiv:cond-mat/0508554v3, lines 709–720. -/
theorem hierarchySum_hierarchyEdge {A : Type*} [AddCommMonoid A] (a : ℕ → A)
    (m k : ℕ) :
    hierarchySum (hierarchyEdge a) m k =
      ∑ j ∈ Finset.Ico (k * 2 ^ m + 1) ((k + 1) * 2 ^ m), a j := by
  induction m generalizing k with
  | zero => simp [hierarchySum_zero]
  | succ m ih =>
    rw [hierarchySum_succ, ih, ih]
    have hlo : k * 2 ^ (m + 1) + 1 = 2 * k * 2 ^ m + 1 := by rw [pow_succ]; ring
    have hhi : (k + 1) * 2 ^ (m + 1) = (2 * k + 1 + 1) * 2 ^ m := by rw [pow_succ]; ring
    rw [hlo, hhi, hierarchyEdge, add_comm (a _), ← Finset.sum_Ico_succ_top (by
      have := Nat.one_le_two_pow (n := m)
      nlinarith : 2 * k * 2 ^ m + 1 ≤ (2 * k + 1) * 2 ^ m)]
    exact Finset.sum_Ico_consecutive a
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1) (by
      have := Nat.one_le_two_pow (n := m)
      simp only [add_mul, one_mul]
      omega)

/-- The internal edges, together with edge zero, are the periodic sum.
Hastings, arXiv:cond-mat/0508554v3, lines 626–628 and 709–720. -/
theorem hierarchySum_hierarchyEdge_add_zero {A : Type*} [AddCommMonoid A]
    (a : ℕ → A) (h : ℕ) :
    hierarchySum (hierarchyEdge a) h 0 + a 0 = ∑ j ∈ Finset.range (2 ^ h), a j := by
  rw [hierarchySum_hierarchyEdge]
  simpa only [Nat.zero_mul, zero_add, one_mul, Finset.range_eq_Ico, add_comm] using
    (Finset.sum_eq_sum_Ico_succ_bot (Nat.two_pow_pos h) a).symm

section Support

open Matrix QuantumCircuit

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- A nearest-neighbour edge acts on the parent block containing both its endpoints.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628 and 668–685. -/
theorem hierarchyEdge_mem_supportedOperators (blk : ι → ℕ)
    (a : ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (ha : ∀ j, 0 < j → a j ∈ supportedOperators d {i | blk i + 1 = j ∨ blk i = j})
    (m k : ℕ) : hierarchyEdge a m k ∈ supportedOperators d (levelBlock blk (m + 1) k) := by
  apply supportedOperators_mono (S := {i | blk i + 1 = (2 * k + 1) * 2 ^ m ∨
    blk i = (2 * k + 1) * 2 ^ m}) _ (ha _ (by positivity))
  intro i hi
  change blk i / 2 ^ (m + 1) = k
  apply Nat.div_eq_of_lt_le
  all_goals
    have := Nat.one_le_two_pow (n := m)
    simp only [pow_succ, add_mul, one_mul, mul_assoc, mul_comm] at hi ⊢
    rcases hi with hi | hi <;> omega

end Support

end TNLean.MPS.AreaLaw.LocalSolution
