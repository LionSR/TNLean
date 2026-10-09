/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LiebRobinson.GraphLocalization

/-!
# Exact stabilization of finite graph balls

The graph balls centered at a vertex eventually equal its connected component.
The cutoff is the maximum of the natural distances from that vertex, while
membership in a ball is still measured by extended distance. Thus vertices in
other components never enter the ball, even though their natural distance has
the junk value zero.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 124–139, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This finite graph fact justifies the exact component-support step there; it
uses the supplied graph, including when it is an induced-domain graph.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

namespace QuantumCircuit

variable {ι : Type*} [Fintype ι]

/-- Graph balls increase with their radius. Source: area law,
`09-amplification.tex`, lines 124–132. -/
theorem graphBall_mono (G : SimpleGraph ι) (a : ι) : Monotone (graphBall G a) := by
  intro m n hmn x hx
  apply mem_graphBall.mpr
  exact (mem_graphBall.mp hx).trans (by exact_mod_cast hmn)

/-- A site at infinite distance belongs to no finite graph ball. Source: area
law, `09-amplification.tex`, lines 133–137. -/
theorem notMem_graphBall_of_edist_eq_top {G : SimpleGraph ι} {a y : ι}
    (hy : G.edist a y = ⊤) (n : ℕ) : y ∉ graphBall G a n := by
  intro hmem
  have hdist := mem_graphBall.mp hmem
  rw [hy] at hdist
  exact (not_le_of_gt (ENat.natCast_lt_top n)) hdist

/-- Beyond the maximum finite distance from the anchor, its graph ball is
exactly its reachable set. No connectedness or global-diameter assumption is
needed. Source: area law, `09-amplification.tex`, lines 135–139. -/
theorem coe_graphBall_eq_reachable_of_sup_dist_le (G : SimpleGraph ι) (a : ι)
    {n : ℕ} (hn : Finset.univ.sup (G.dist a) ≤ n) :
    (graphBall G a n : Set ι) = {x | G.Reachable a x} := by
  classical
  ext x
  change x ∈ graphBall G a n ↔ G.Reachable a x
  constructor
  · intro hx
    exact SimpleGraph.reachable_of_edist_ne_top
      (ne_of_lt ((mem_graphBall.mp hx).trans_lt (ENat.natCast_lt_top n)))
  · intro hx
    apply mem_graphBall.mpr
    rw [← hx.coe_dist_eq_edist]
    exact_mod_cast (Finset.le_sup (f := G.dist a) (Finset.mem_univ x)).trans hn

/-- The balls of a finite graph stabilize exactly on the anchor's component.
Source: area law, `09-amplification.tex`, lines 135–139. -/
theorem exists_graphBall_eq_reachable (G : SimpleGraph ι) (a : ι) :
    ∃ N, ∀ n ≥ N, (graphBall G a n : Set ι) = {x | G.Reachable a x} :=
  ⟨Finset.univ.sup (G.dist a), fun _ hn =>
    coe_graphBall_eq_reachable_of_sup_dist_le G a hn⟩

end QuantumCircuit
