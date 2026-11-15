/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.NearestNeighborTruncationRank
import TNLean.MPS.AreaLaw.OpenMPS

/-!
# All chain cuts of the actual label truncation

The actual crossing-interval bound is combined with direct endpoint and one-dimensional local
space bounds. Supporting the interaction-label version of ALVV, arXiv:1602.08828v2,
`thm:cluster`, lines 1298–1303 and 1971–2013.

**Local fix (interaction-label cutoff):** the selected operator uses the existing label-path
selector, not the minimal physical support of a word product; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset Matrix SimpleGraph

namespace TNLean.MPS.AreaLaw

open TNLean.Lattice.ClusterExpansion

open Classical in
/-- The actual label-truncated nearest-neighbour operator has rank at most `r² q^r` at every
chain cut, including endpoints, `r = 1`, and local dimension one. No cut rank is supplied.
Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 1971–2013. -/
theorem operatorSchmidtRank_cluster_truncation_all_cuts_le {N q r : ℕ}
    (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ}) (β : ℝ) (k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin (N + 1) ↦ q)
      (leftBlock (N + 1) k) (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β)) ≤
        r ^ 2 * q ^ r := by
  classical
  have hD : 1 ≤ r ^ 2 * q ^ r := Nat.mul_le_mul (one_le_pow₀ hr) (one_le_pow₀ hq)
  by_cases hq1 : q = 1
  · subst q
    apply le_trans ?_ hD
    rw [Matrix.operatorSchmidtRank_eq_rank_realignment]
    exact (Matrix.rank_le_card_height _).trans_eq (by simp)
  · by_cases hk0 : k = 0
    · subst k
      have hempty : leftBlock (N + 1) 0 = ∅ := by ext v; simp [leftBlock]
      apply le_trans ?_ hD
      rw [hempty, Matrix.operatorSchmidtRank_eq_rank_realignment]
      exact (Matrix.rank_le_card_height _).trans_eq (by simp)
    · by_cases hkL : N + 1 ≤ k
      · have huniv : leftBlock (N + 1) k = univ := by
          ext v
          simp only [mem_leftBlock, mem_univ, iff_true]
          exact v.isLt.trans_le hkL
        apply le_trans ?_ hD
        rw [huniv, Matrix.operatorSchmidtRank_eq_rank_realignment]
        exact (Matrix.rank_le_card_width _).trans_eq (by simp)
      · let p : Fin N := ⟨k - 1, by omega⟩
        have hA : leftBlock (N + 1) k =
            {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val} := by
          ext v
          simp only [mem_leftBlock, mem_filter, mem_univ, true_and]
          change v.val < k ↔ v.val ≤ k - 1
          omega
        rw [hA]
        by_cases hr1 : r = 1
        · subst r
          have hb := operatorSchmidtRank_truncatedExp_nearestNeighbor_le_count
            (r := 1) hq h hs p β
          have hb' : operatorSchmidtRank (Entropy.cutOperator
              {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val}
                (truncatedExp (pathGraph N) (fun C ↦ 1 ≤ C.card) h β)) ≤ 1 := by
            simpa using hb
          simpa using hb'.trans hq
        · exact operatorSchmidtRank_truncatedExp_nearestNeighbor_le hq hr h hs p β

end TNLean.MPS.AreaLaw
