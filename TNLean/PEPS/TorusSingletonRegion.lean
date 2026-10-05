/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusEntropy

/-!
# Single-site cuts of the native square torus

On a square torus whose two periods are at least three, a single vertex has
four distinct crossing bonds, and its complement is connected. These facts
allow the connected regular boundary statements to be applied to every site
without further geometric assumptions.

**Scope restriction (simple torus graph):** Both periods are at least three.
Smaller periodic networks have parallel bonds not represented by the simple
graph; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the square lattice
construction preceding Theorem 6.9, local source lines 1935–1990.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The coordinate rectangle of side lengths one is its single vertex.
Source: SCP10, the rectangular regions at lines 1935–1957. -/
theorem torusContiguousRectangle_one_eq_singleton (v : TorusVertex width height) :
    torusContiguousRectangle v.1.val v.2.val 1 1 = {v} := by
  ext w
  simp only [mem_torusContiguousRectangle, Finset.mem_singleton]
  constructor
  · intro h
    exact Prod.ext (ZMod.val_injective width (by omega))
      (ZMod.val_injective height (by omega))
  · rintro rfl
    omega

/-- The complement of every single vertex of the native torus is connected.
Source: SCP10, the surrounding rectangular stripes at lines 1935–1957. -/
theorem torusGraph_compl_singleton_connected (v : TorusVertex width height) :
    ((torusGraph width height).induce
      ((Finset.univ \ {v} : Finset (TorusVertex width height)) :
        Set (TorusVertex width height))).Connected := by
  rw [← torusContiguousRectangle_one_eq_singleton v]
  exact torusGraph_compl_rectangle_connected _ _ 1 1 Fact.out Fact.out

/-- Every single vertex induces a connected torus subgraph.
Source: SCP10, the one-site instance of the connected-region construction
in Lemma 5.2, lines 1318–1358. -/
theorem torusGraph_singleton_connected (v : TorusVertex width height) :
    ((torusGraph width height).induce
      (({v} : Finset (TorusVertex width height)) : Set (TorusVertex width height))).Connected := by
  rw [← torusContiguousRectangle_one_eq_singleton v]
  exact torusGraph_rectangle_connected _ _ 1 1 (by decide) (by decide)
    (by have := ZMod.val_lt v.1; omega) (by have := ZMod.val_lt v.2; omega)

/-- Every single-site torus cut has exactly four crossing bonds.
Source: SCP10, the one-site boundary in the square-lattice construction,
lines 1935–1990. -/
theorem card_regionBoundaryEdge_torus_singleton (v : TorusVertex width height) :
    Fintype.card {f : Edge (torusGraph width height) // IsRegionBoundaryEdge {v} f} = 4 := by
  classical
  let e : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge {v} f} ≃
      IncidentEdge (torusGraph width height) v :=
    Equiv.subtypeEquivRight (fun f => by
      simp only [IsRegionBoundaryEdge, Finset.mem_singleton]
      have hne := ne_of_lt f.2.1
      have hnot : ¬(f.1.1 = v ∧ f.1.2 = v) :=
        fun h => hne (h.1.trans h.2.symm)
      tauto)
  exact (Fintype.card_congr (e.trans (torusIncidentLegEquiv v).symm)).trans
    (Fintype.card_fin 4)

/-- The native square torus is connected. Source: SCP10, the periodic
square-lattice construction at lines 1935–1990. -/
theorem torusGraph_connected : (torusGraph width height).Connected := by
  classical
  have hmem (v : TorusVertex width height) :
      v ∈ torusContiguousRectangle (width := width) (height := height) 0 0 width height := by
    simp [mem_torusContiguousRectangle, ZMod.val_lt]
  have hconn := torusGraph_rectangle_connected (width := width) (height := height)
    0 0 width height (NeZero.pos width) (NeZero.pos height) (by omega) (by omega)
  exact hconn.map ⟨Subtype.val, fun h => h⟩ (fun v => ⟨⟨v, hmem v⟩, rfl⟩)

end TNLean.PEPS
