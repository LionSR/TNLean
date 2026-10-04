/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IsoTransport

/-!
# A transported ordered edge and a transported subgraph

A graph isomorphism transports an ordered edge by mapping its endpoints and
sorting them. Pulling any graph back along the inverse isomorphism preserves
adjacency of these endpoints, independently of the sorting. In particular a
non-tree bond remains outside the transported tree.

Auxiliary to SCP10, arXiv:1001.3807, the finite blocking and adjacent-flux
geometries in lines 1765–1920 and 2380–2415.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS
variable {V W : Type*} [LinearOrder V] [LinearOrder W]
variable {Γ : SimpleGraph V} {Γ' : SimpleGraph W}

/-- Equality of native sorted edges is equality of their unordered endpoints.
Auxiliary to SCP10, seam-aware flux movement, lines 2271–2305. -/
theorem Edge.ofAdj_eq_iff_endpoints {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
    {x y a b : V} (hxy : Γ.Adj x y) (hab : Γ.Adj a b) :
    Edge.ofAdj hxy = Edge.ofAdj hab ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  constructor
  · intro h
    rcases Edge.ofAdj_endpoints hxy with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩ <;>
      rcases Edge.ofAdj_endpoints hab with ⟨h₂,h₃⟩ | ⟨h₂,h₃⟩ <;> grind
  · exact Edge.ofAdj_eq_ofAdj hxy hab

/-- A constant endpoint coordinate distinguishes two native edges whenever one
endpoint of the other edge has a different coordinate. Auxiliary to SCP10,
local flux geometries, lines 2271–2305 and 2380–2415. -/
theorem Edge.ofAdj_ne_of_endpoint_coordinates {Y : Type*} {x y a b : V}
    (hxy : Γ.Adj x y) (hab : Γ.Adj a b) (f : V → Y)
    (hc : f a = f b) (hne : f x ≠ f a ∨ f y ≠ f a) :
    Edge.ofAdj hxy ≠ Edge.ofAdj hab := by
  intro heq
  rcases (Edge.ofAdj_eq_iff_endpoints hxy hab).mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne.elim (fun h => h rfl) (fun h => h hc.symm)
  · exact hne.elim (fun h => h hc.symm) (fun h => h rfl)

/-- Adjacency in a transported graph agrees with adjacency of the original
ordered endpoints, even when their order reverses. Auxiliary to SCP10,
finite local blocking and flux geometries, lines 1765–1920 and 2380–2415. -/
theorem Edge.comap_adj_map_iff (φ : Γ ≃g Γ') (T : SimpleGraph V) (e : Edge Γ) :
    (T.comap φ.symm).Adj (Edge.map φ e).1.1 (Edge.map φ e).1.2 ↔ T.Adj e.1.1 e.1.2 := by
  rcases Edge.map_endpoints φ e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp only [SimpleGraph.comap_adj, h₁, h₂, RelIso.symm_apply_apply]
  · simp only [SimpleGraph.comap_adj, h₁, h₂, RelIso.symm_apply_apply, SimpleGraph.adj_comm]

end TNLean.PEPS
