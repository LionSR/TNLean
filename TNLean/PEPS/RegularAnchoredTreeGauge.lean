/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTreeGaugeTransport
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Tree gauges fixed on an untwisted component

A connected region has a spanning tree whose root-normalized gauge is the
identity on the entire root component of a supplied untwisted subgraph.
Choose a spanning forest of that subgraph and extend it to a spanning tree
of the region. The tree gauge is constant along every forest edge.

This is a noncommutative step toward the complementary contraction in SCP10,
arXiv:1001.3807v3, Lemma 6.14 and Theorem 6.9, lines 1935–1990 and 2199–2214.
Neither the untwisted subgraph nor its boundary connectivity is inferred from
endpoint exclusion here. See `docs/paper-gaps/scp10_anchored_tree_gauge.tex`.
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]

/-- Construct a root-normalized tree gauge that fixes the whole root component
of an untwisted subgraph and removes every internal tree operator. The tree,
forest and gauge are derived internally; no commutativity is required.
Auxiliary noncentral contraction step for SCP10, Lemma 6.14 and Theorem 6.9. -/
theorem exists_regularRegionTreeGauge_fixed_on_untwisted_component
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (U : SimpleGraph {v : V // v ∈ R}) (hU : U ≤ Γ.induce (R : Set V))
    (o : {v : V // v ∈ R}) (u : Edge Γ → G)
    (hu : ∀ {v w : {v : V // v ∈ R}} (h : U.Adj v w),
      regularDirectedTransport u (hU h) = 1) :
    ∃ (T : SimpleGraph {v : V // v ∈ R}) (k : {v : V // v ∈ R} → G),
      T ≤ Γ.induce (R : Set V) ∧ T.IsTree ∧ k o = 1 ∧
        (∀ v, U.Reachable o v → k v = 1) ∧
        ∀ e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R},
          T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩ →
            regularRegionGaugeResidual R k u e = 1 := by
  classical
  obtain ⟨F, hFU, hFacyclic, hFreach⟩ := U.exists_isAcyclic_reachable_eq_le
  obtain ⟨T, hFT, hT, htree⟩ :=
    hR.exists_isTree_le_of_le_of_isAcyclic (hFU.trans hU) hFacyclic
  let k := (regularRegionTreeGauge R T hT htree o u).1
  have hedge {v w : {v : V // v ∈ R}} (h : F.Adj v w) : k w = k v := by
    have hg := regularRegionTreeGauge_directedTransport R T hT htree o u
      (hFT h) (hU (hFU h))
    rw [hu (hFU h)] at hg
    change 1 = k w * (k v)⁻¹ at hg
    have hm := congrArg (fun z : G => z * k v) hg
    simpa only [one_mul, mul_assoc, inv_mul_cancel, mul_one] using hm.symm
  have hwalk {v w : {v : V // v ∈ R}} (p : F.Walk v w) : k w = k v := by
    induction p with
    | nil => rfl
    | cons h p ih => exact ih.trans (hedge h)
  refine ⟨T, k, hT, htree, regularRegionTreeGauge_root R T hT htree o u, ?_, ?_⟩
  · intro v hv
    have hvF : F.Reachable o v := by rw [hFreach]; exact hv
    obtain ⟨p⟩ := hvF
    exact (hwalk p).trans (regularRegionTreeGauge_root R T hT htree o u)
  · intro e he
    exact regularRegionGaugeResidual_eq_one_of_tree R T hT htree o u e he

end TNLean.PEPS
