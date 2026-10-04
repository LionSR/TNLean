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

/-- The four native legs enumerate the incident edges of a vertex.
Source: SCP10, square-lattice virtual legs in Definition 6.1. -/
def torusIncidentLeg (v : TorusVertex width height) :
    Fin 4 → IncidentEdge (torusGraph width height) v :=
  ![torusTopLeg v, torusRightLeg v, torusDownLeg v, torusLeftLeg v]

/-- No incident torus edge is omitted by the four native legs.
Source: SCP10, square-lattice construction at lines 1935–1990. -/
theorem torusIncidentLeg_surjective (v : TorusVertex width height) :
    Function.Surjective (torusIncidentLeg v) := by
  apply (Function.injective_comp_right_iff_surjective (γ := Bool)).mp
  intro η θ h
  apply torusIncidentCoordinates_injective (G := Bool) v
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

/-- The four native virtual legs are distinct when both periods are at least
three. Source: SCP10, square-lattice construction at lines 1935–1990. -/
theorem torusIncidentLeg_injective (v : TorusVertex width height) :
    Function.Injective (torusIncidentLeg v) := by
  have htr : torusTopLeg v ≠ torusRightLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge v v (congrArg Subtype.val h).symm
  have htl : torusTopLeg v ≠ torusLeftLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge (v.1 - 1, v.2) v (congrArg Subtype.val h).symm
  have hrd : torusRightLeg v ≠ torusDownLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge v (v.1, v.2 - 1) (congrArg Subtype.val h)
  have hdl : torusDownLeg v ≠ torusLeftLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge (v.1 - 1, v.2) (v.1, v.2 - 1)
      (congrArg Subtype.val h).symm
  have htd : torusTopLeg v ≠ torusDownLeg v := by
    intro h
    have hy := congrArg Prod.snd (torusUpEdge_injective (congrArg Subtype.val h))
    exact one_ne_zero (α := ZMod height)
      (add_left_cancel (by simpa only [add_zero] using eq_sub_iff_add_eq.mp hy))
  have hrl : torusRightLeg v ≠ torusLeftLeg v := by
    intro h
    have hx := congrArg Prod.fst (torusRightEdge_injective (congrArg Subtype.val h))
    exact one_ne_zero (α := ZMod width)
      (add_left_cancel (by simpa only [add_zero] using eq_sub_iff_add_eq.mp hx))
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [torusIncidentLeg]

/-- Numbering the four actual incident bonds in top, right, down, left order.
Source: SCP10, square-lattice virtual legs in Definition 6.1. -/
noncomputable def torusIncidentLegEquiv (v : TorusVertex width height) :
    Fin 4 ≃ IncidentEdge (torusGraph width height) v :=
  Equiv.ofBijective (torusIncidentLeg v)
    ⟨torusIncidentLeg_injective v, torusIncidentLeg_surjective v⟩

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
