/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.NearestNeighborSupport
import QICLean.Entropy.SupportedOperatorSchmidtRank

/-!
# The actual support and operator Schmidt rank of a nearest-neighbour interval

A connected interval of fewer than `r` interaction labels is designated on at most `r` physical
sites. The two-sided support bound therefore controls its actual exact-label coefficient at every
physical cut. Supporting the interaction-label version of ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013.

**Local fix (interaction-label cutoff):** this result counts the existing label components,
not the minimal physical support of a word product; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset SimpleGraph QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice.ClusterExpansion

variable {N : ℕ}

/-- The union of the designated bonds of a connected label interval has at most one more
physical site than interaction labels. Supporting ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013. -/
theorem card_biUnion_nearestNeighbor_le {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) :
    (C.biUnion (fun i ↦ ({i.castSucc, i.succ} : Finset (Fin (N + 1))))).card ≤ C.card + 1 := by
  have hord := ordConnected_of_pathGraph_connected hC
  have hne : C.Nonempty := by
    obtain ⟨p⟩ := hC.nonempty
    exact ⟨p, p.property⟩
  have hsub : C.biUnion (fun i ↦ ({i.castSucc, i.succ} : Finset (Fin (N + 1)))) ⊆
      Icc (C.min' hne).castSucc (C.max' hne).succ := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := mem_biUnion.mp hv
    have hmin : (C.min' hne).val ≤ i.val := C.min'_le i hi
    have hmax : i.val ≤ (C.max' hne).val := C.le_max' i hi
    rw [mem_Icc]
    simp only [mem_insert, mem_singleton] at hvi
    rcases hvi with rfl | rfl <;> simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] <;> omega
  have hlen : C.card = (C.max' hne).val + 1 - (C.min' hne).val :=
    (congrArg Finset.card (eq_Icc_of_ordConnected hord hne)).trans (Fin.card_Icc _ _)
  have hle : (C.min' hne).val ≤ (C.max' hne).val := C.min'_le _ (C.max'_mem hne)
  have hcard : (Icc (C.min' hne).castSucc (C.max' hne).succ).card = C.card + 1 := by
    rw [Fin.card_Icc]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  exact (Finset.card_le_card hsub).trans_eq hcard

/-- The actual exact-label coefficient of an interval with fewer than `r` nearest-neighbour
labels has operator Schmidt rank at most `q ^ r` at every physical cut. Its support is derived
from the actual interactions, and both support-square bounds are used. Supporting ALVV,
arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem operatorSchmidtRank_clusterOp_nearestNeighbor_le {q r : ℕ} (hq : 1 ≤ q)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    {C : Finset (Fin N)} (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected)
    (hshort : C.card < r) (A : Finset (Fin (N + 1))) (β : ℝ) :
    Matrix.operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin (N + 1) ↦ q)
      A (clusterOp h C β)) ≤ q ^ r := by
  have hTC := QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    (clusterOp_mem_supportedOperators
      (fun i ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i)) C β)
  exact (Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_pow_card hq
    (A := A) hTC).trans (Nat.pow_le_pow_right hq
      ((card_biUnion_nearestNeighbor_le hC).trans (Nat.succ_le_of_lt hshort)))

end TNLean.Lattice.ClusterExpansion
