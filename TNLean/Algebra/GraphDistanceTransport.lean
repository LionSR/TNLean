/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Extended graph distance under isomorphisms and component inclusion

Mapping a walk by a graph homomorphism preserves its length. Consequently a
homomorphism does not increase extended graph distance, and an isomorphism
preserves it. An ambient walk between vertices of one connected component
remains in that component; inducing the walk preserves its length and gives
equality between the component and ambient extended distances.

The statements allow arbitrary vertex types. In particular, no finite-graph
or decidable-equality assumption is imposed, and infinite distance is retained.
-/

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Mapping walks by a graph homomorphism does not increase extended distance. -/
theorem Hom.edist_le (f : G →g H) (u v : V) :
    H.edist (f u) (f v) ≤ G.edist u v := by
  rw [edist_eq_sInf (G := G)]
  refine le_sInf ?_
  rintro _ ⟨p, rfl⟩
  simpa only [Walk.length_map] using (p.map f).edist_le

/-- A graph isomorphism preserves extended graph distance, including infinite distance. -/
theorem Iso.edist_eq (e : G ≃g H) (u v : V) :
    H.edist (e u) (e v) = G.edist u v := by
  apply le_antisymm (e.toHom.edist_le u v)
  simpa only [RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.symm_apply_apply] using
    e.symm.toHom.edist_le (e u) (e v)

/-- The graph induced on a connected component has the ambient extended distance. -/
theorem ConnectedComponent.edist_eq (C : G.ConnectedComponent) (u v : C) :
    C.toSimpleGraph.edist u v = G.edist u.val v.val := by
  classical
  apply le_antisymm ?_ (C.toSimpleGraph_hom.edist_le u v)
  rw [edist_eq_sInf (G := G)]
  refine le_sInf ?_
  rintro _ ⟨p, rfl⟩
  have hSupp : ∀ x ∈ p.support, x ∈ C.supp := fun x hx ↦
    (C.mem_supp_iff x).mpr
      ((ConnectedComponent.sound (p.takeUntil x hx).reachable).symm.trans u.property)
  have hlen : (p.induce C.supp hSupp).length = p.length := by
    exact (Walk.length_map (Embedding.induce C.supp).toHom
      (p.induce C.supp hSupp)).symm.trans
        (congrArg (fun w : G.Walk u.val v.val ↦ w.length) (p.map_induce hSupp))
  exact (p.induce C.supp hSupp).edist_le.trans_eq
    (congrArg (fun n : ℕ ↦ (n : ℕ∞)) hlen)

end SimpleGraph
