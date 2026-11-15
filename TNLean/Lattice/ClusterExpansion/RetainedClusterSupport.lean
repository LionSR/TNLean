/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterFactorization
import TNLean.Circuit.EntropySupport

/-!
# Physical support of actual retained cluster sums

The finite retained sum on a specified set of interaction labels acts on the union of their
designated supports. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013.
-/

open Finset QuantumCircuit

namespace TNLean.Lattice.ClusterExpansion

open Classical in
/-- The actual retained finite sum acts on the union of the designated supports of its allowed
labels. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem isSupportedOn_sum_retained_clusterOp
    {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] {q : ℕ}
    (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)
    (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ) (acts : κ → Finset σ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : σ ↦ q) (h i) (acts i))
    (B : Finset κ) (β : ℝ) :
    Entropy.IsSupportedOn (n := fun _ : σ ↦ q)
      (∑ A ∈ B.powerset with NoLargeCluster G large A, clusterOp h A β) (B.biUnion acts) := by
  apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
  refine Submodule.sum_mem _ fun A hA ↦ ?_
  apply supportedOperators_mono _ (clusterOp_mem_supportedOperators
    (fun i ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i)) A β)
  exact Finset.coe_subset.mpr (Finset.biUnion_subset_biUnion_of_subset_left acts
    (mem_powerset.mp (mem_filter.mp hA).1))

end TNLean.Lattice.ClusterExpansion
