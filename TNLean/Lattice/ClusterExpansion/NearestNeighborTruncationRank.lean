/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.NearestNeighborIntervalRank
import TNLean.Lattice.ClusterExpansion.CrossingIntervalCount
import QICLean.Algebra.OperatorSchmidtBounds

/-!
# Operator Schmidt rank of the actual interaction-label truncation

The exact crossing-component identity and the actual physical supports imply a finite cut-rank
bound. Supporting the interaction-label version of ALVV, arXiv:1602.08828v2,
`thm:cluster` and `eq:rho-expansion`, lines 1298–1303 and 1971–2013.

**Local fix (interaction-label cutoff):** this result concerns the existing label-path
truncation, not the selector based on the minimal physical support of a product; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset SimpleGraph Matrix

namespace TNLean.Lattice.ClusterExpansion

open Classical in
/-- The actual nearest-neighbour truncation has operator Schmidt rank bounded by one plus
the proved crossing-interval count times the proved interval rank. No decomposition or rank is
supplied as a hypothesis. Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`,
lines 1298–1303 and 1971–2013. -/
theorem operatorSchmidtRank_truncatedExp_nearestNeighbor_le_count {N q r : ℕ} (hq : 1 ≤ q)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ}) (p : Fin N) (β : ℝ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin (N + 1) ↦ q)
      {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val}
        (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β)) ≤
      1 + (r - 1) ^ 2 * q ^ r := by
  classical
  let A := {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val}
  let R := {v ∈ (univ : Finset (Fin (N + 1))) | p.val < v.val}
  let F := fun B : Finset (Fin N) ↦
    ∑ S ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) S,
      clusterOp h S β
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (Entropy.cutEquiv (fun _ : Fin (N + 1) ↦ q) A)
  have hleft (B : Finset (Fin N)) (hB : ∀ i ∈ B, i.val < p.val) :
      operatorSchmidtRank (φ (F B)) ≤ 1 := by
    exact Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
      (isSupportedOn_retained_nearestNeighbor_left h hs p B hB β) (.inl Finset.Subset.rfl)
  have hright (B : Finset (Fin N)) (hB : ∀ i ∈ B, p.val < i.val) :
      operatorSchmidtRank (φ (F B)) ≤ 1 := by
    have hd : Disjoint R A := by
      exact Finset.disjoint_left.mpr fun v hvR hvA ↦
        (not_lt_of_ge (mem_filter.mp hvA).2) (mem_filter.mp hvR).2
    exact Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
      (isSupportedOn_retained_nearestNeighbor_right h hs p B hB β) (.inr hd)
  have hprod (B D : Finset (Fin N)) (hB : ∀ i ∈ B, i.val < p.val)
      (hD : ∀ i ∈ D, p.val < i.val) : operatorSchmidtRank (φ (F B * F D)) ≤ 1 := by
    rw [map_mul]
    exact (Matrix.operatorSchmidtRank_mul_le _ _).trans
      (Nat.mul_le_mul (hleft B hB) (hright D hD))
  let T := (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
    p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r)
  have hcross (C : Finset (Fin N)) (hCmem : C ∈ T) :
      operatorSchmidtRank (φ (clusterOp h C β *
        (F {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val} *
          F {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}))) ≤ q ^ r := by
    have hc := (mem_filter.mp hCmem).2
    have hpairs := hprod {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val}
      {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}
      (fun i hi ↦ by have := (mem_filter.mp hi).2 p hc.1; omega)
      (fun i hi ↦ by have := (mem_filter.mp hi).2 p hc.1; omega)
    have he := operatorSchmidtRank_clusterOp_nearestNeighbor_le hq h hs hc.2.1 hc.2.2 A β
    change operatorSchmidtRank (φ (clusterOp h C β)) ≤ q ^ r at he
    rw [map_mul]
    simpa only [Nat.mul_one] using (Matrix.operatorSchmidtRank_mul_le _ _).trans
      (Nat.mul_le_mul he hpairs)
  have hdec : truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
      F {j ∈ univ | j.val < p.val} * F {j ∈ univ | p.val < j.val} +
        ∑ C ∈ T, clusterOp h C β *
          (F {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val} *
            F {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}) :=
    truncatedExp_nearestNeighbor_eq_crossing_components h hs p β
  change operatorSchmidtRank (φ (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β)) ≤ _
  rw [hdec, map_add, map_sum]
  refine (Matrix.operatorSchmidtRank_add_le _ _).trans
    ((Nat.add_le_add (hprod _ _ (fun i hi ↦ (mem_filter.mp hi).2)
      (fun i hi ↦ (mem_filter.mp hi).2)) (Matrix.operatorSchmidtRank_sum_le T _)).trans ?_)
  refine (Nat.add_le_add_left (Finset.sum_le_sum hcross) 1).trans ?_
  simpa [T] using Nat.add_le_add_left
    (Nat.mul_le_mul_right (q ^ r) (card_crossing_intervals_le p r)) 1

open Classical in
/-- The actual nearest-neighbour label truncation has operator Schmidt rank at most `r² q^r`
at every interior physical cut. Supporting the corrected interaction-label form of ALVV,
arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 1971–2013. -/
theorem operatorSchmidtRank_truncatedExp_nearestNeighbor_le {N q r : ℕ}
    (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ}) (p : Fin N) (β : ℝ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin (N + 1) ↦ q)
      {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val}
        (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β)) ≤ r ^ 2 * q ^ r := by
  refine (operatorSchmidtRank_truncatedExp_nearestNeighbor_le_count hq h hs p β).trans ?_
  have hr1 : r - 1 + 1 = r := by omega
  have hpow : 1 ≤ q ^ r := one_le_pow₀ hq
  have hsq : 1 + (r - 1) ^ 2 ≤ r ^ 2 := by nlinarith
  calc
    1 + (r - 1) ^ 2 * q ^ r ≤ (1 + (r - 1) ^ 2) * q ^ r := by nlinarith
    _ ≤ r ^ 2 * q ^ r := Nat.mul_le_mul_right _ hsq

end TNLean.Lattice.ClusterExpansion
