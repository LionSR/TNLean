/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTranslationInvariant

/-!
# Translation-invariant PEPS on the torus from one four-leg site tensor

The two-dimensional examples of the review (arXiv:2011.12127, Appendix A, "Two dimensions:
PEPS", `Papers/2011.12127/TN-Review-main.tex` lines 2412–2415) each specify a single tensor
`A^i_{αβγδ}` with one physical index `i` and four virtual indices, ordered top, right, down,
left (line 2415), repeated at every site of a square lattice. This file places such a tensor at
every vertex of the discrete torus `torusGraph width height`.

The four legs of a vertex `v = (x, y)` are the up edge of `v` (top), the right edge of `v`
(right), the up edge of `(x, y - 1)` (down), and the right edge of `(x - 1, y)` (left). Every
bond carries the same dimension `D`.

On a torus of width and height at least three the right and up edges of the vertices are
pairwise distinct and exhaust the edge set, so a virtual configuration is the same as two
arrays `hb, vb : TorusVertex width height → Fin D` of horizontal and vertical bond indices
(`torusEdgeEquiv`). The state coefficient becomes the familiar lattice contraction
(`stateCoeff_torusSiteTensor`). On a torus of width two the right edges of `(0, y)` and
`(1, y)` coincide in the simple graph, so the four legs of a vertex are not four distinct
bonds; the bridge is stated for width and height at least three.

## Main definitions

* `TNLean.PEPS.torusDownEdge`, `TNLean.PEPS.torusLeftEdge`: the down and left legs of a vertex.
* `TNLean.PEPS.torusTopLeg`, `torusRightLeg`, `torusDownLeg`, `torusLeftLeg`: the four legs
  as incident edges.
* `TNLean.PEPS.torusSiteTensor`: the torus PEPS of a four-leg site tensor.
* `TNLean.PEPS.torusEdgeEquiv`: edges of the torus are right edges or up edges.

## Main results

* `TNLean.PEPS.stateCoeff_torusSiteTensor_eq_sum_edge`: the coefficient as a sum over edge
  labellings.
* `TNLean.PEPS.stateCoeff_torusSiteTensor`: the coefficient as a sum over horizontal and
  vertical bond arrays.
* `TNLean.PEPS.torusVertex_apply_eq_apply_zero_of_shift`: a function invariant under the unit
  shifts in both directions is constant.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A function on the torus invariant under the unit horizontal and vertical shifts is
constant. -/
theorem torusVertex_apply_eq_apply_zero_of_shift {α : Type*}
    (f : TorusVertex width height → α)
    (h1 : ∀ v : TorusVertex width height, f (v.1 + 1, v.2) = f v)
    (h2 : ∀ v : TorusVertex width height, f (v.1, v.2 + 1) = f v)
    (v : TorusVertex width height) : f v = f 0 := by
  have hx : ∀ (n : ℕ) (y : ZMod height), f ((n : ZMod width), y) = f (0, y) := by
    intro n y
    induction n with
    | zero => simp
    | succ n ih =>
      calc f (((n + 1 : ℕ) : ZMod width), y) = f ((n : ZMod width) + 1, y) := by
            push_cast; rfl
        _ = f ((n : ZMod width), y) := h1 ((n : ZMod width), y)
        _ = f (0, y) := ih
  have hy : ∀ n : ℕ, f (0, (n : ZMod height)) = f 0 := by
    intro n
    induction n with
    | zero => simp; rfl
    | succ n ih =>
      calc f (0, ((n + 1 : ℕ) : ZMod height)) = f (0, (n : ZMod height) + 1) := by
            push_cast; rfl
        _ = f (0, (n : ZMod height)) := h2 (0, (n : ZMod height))
        _ = f 0 := ih
  obtain ⟨x, y⟩ := v
  rw [← ZMod.natCast_zmod_val x, hx, ← ZMod.natCast_zmod_val y, hy]

variable [Fact (1 < width)] [Fact (1 < height)]

/-! ### The four legs of a vertex -/

/-- The down leg of `v = (x, y)`: the up edge of `(x, y - 1)`. -/
def torusDownEdge (v : TorusVertex width height) : Edge (torusGraph width height) :=
  torusUpEdge (v.1, v.2 - 1)

/-- The left leg of `v = (x, y)`: the right edge of `(x - 1, y)`. -/
def torusLeftEdge (v : TorusVertex width height) : Edge (torusGraph width height) :=
  torusRightEdge (v.1 - 1, v.2)

/-- The left leg of the right neighbour of `v` is the right edge of `v`. -/
theorem torusLeftEdge_add_one (v : TorusVertex width height) :
    torusLeftEdge (v.1 + 1, v.2) = torusRightEdge v := by
  simp [torusLeftEdge]

/-- The down leg of the upper neighbour of `v` is the up edge of `v`. -/
theorem torusDownEdge_add_one (v : TorusVertex width height) :
    torusDownEdge (v.1, v.2 + 1) = torusUpEdge v := by
  simp [torusDownEdge]

theorem torusRightEdge_incident (v : TorusVertex width height) :
    (torusRightEdge v).1.1 = v ∨ (torusRightEdge v).1.2 = v := by
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem torusUpEdge_incident (v : TorusVertex width height) :
    (torusUpEdge v).1.1 = v ∨ (torusUpEdge v).1.2 = v := by
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem torusLeftEdge_incident (v : TorusVertex width height) :
    (torusLeftEdge v).1.1 = v ∨ (torusLeftEdge v).1.2 = v := by
  have hv : ((v.1 - 1 + 1, v.2) : TorusVertex width height) = v := by simp
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right (v.1 - 1) v.2) with ⟨_, h⟩ | ⟨h, _⟩
  · exact Or.inr (h.trans hv)
  · exact Or.inl (h.trans hv)

theorem torusDownEdge_incident (v : TorusVertex width height) :
    (torusDownEdge v).1.1 = v ∨ (torusDownEdge v).1.2 = v := by
  have hv : ((v.1, v.2 - 1 + 1) : TorusVertex width height) = v := by simp
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 (v.2 - 1)) with ⟨_, h⟩ | ⟨h, _⟩
  · exact Or.inr (h.trans hv)
  · exact Or.inl (h.trans hv)

/-- The top leg of `v`, its up edge, as an incident edge. -/
def torusTopLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusUpEdge v, torusUpEdge_incident v⟩

/-- The right leg of `v`, its right edge, as an incident edge. -/
def torusRightLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusRightEdge v, torusRightEdge_incident v⟩

/-- The down leg of `v` as an incident edge. -/
def torusDownLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusDownEdge v, torusDownEdge_incident v⟩

/-- The left leg of `v` as an incident edge. -/
def torusLeftLeg (v : TorusVertex width height) : IncidentEdge (torusGraph width height) v :=
  ⟨torusLeftEdge v, torusLeftEdge_incident v⟩

/-! ### The torus PEPS of a site tensor -/

/-- The PEPS on the torus that places the four-leg tensor `a` at every vertex, with bond
dimension `D` on every edge. The virtual arguments of `a` are ordered top, right, down, left,
the ordering convention of the review.

Source: arXiv:2011.12127, Appendix A, "Two dimensions: PEPS",
`Papers/2011.12127/TN-Review-main.tex` line 2415. -/
def torusSiteTensor {D d : ℕ} (a : Fin D → Fin D → Fin D → Fin D → Fin d → ℂ) :
    Tensor (torusGraph width height) d where
  bondDim _ := D
  component v η s :=
    a (η (torusTopLeg v)) (η (torusRightLeg v)) (η (torusDownLeg v)) (η (torusLeftLeg v)) s

/-- Bridge: the coefficient of a torus site-tensor PEPS is a sum over labellings of the edges
by bond indices. -/
theorem stateCoeff_torusSiteTensor_eq_sum_edge {D d : ℕ}
    (a : Fin D → Fin D → Fin D → Fin D → Fin d → ℂ)
    (σ : TorusVertex width height → Fin d) :
    stateCoeff (torusSiteTensor a) σ =
      ∑ η : Edge (torusGraph width height) → Fin D,
        ∏ v, a (η (torusUpEdge v)) (η (torusRightEdge v)) (η (torusDownEdge v))
          (η (torusLeftEdge v)) (σ v) :=
  rfl

/-! ### Edges as right edges and up edges -/

/-- A right edge is horizontal. -/
theorem isHorizontalTorusEdge_torusRightEdge (p : TorusVertex width height) :
    IsHorizontalTorusEdge (torusRightEdge p) := by
  unfold IsHorizontalTorusEdge torusRightEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2]
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

/-- An up edge is vertical. -/
theorem isVerticalTorusEdge_torusUpEdge (p : TorusVertex width height) :
    IsVerticalTorusEdge (torusUpEdge p) := by
  unfold IsVerticalTorusEdge torusUpEdge
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2]
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

/-- In `ZMod n` with `2 < n`, no two elements are each the successor of the other. -/
theorem zmod_not_add_one_eq_and_add_one_eq {n : ℕ} [Fact (2 < n)] (x y : ZMod n) :
    ¬ (x = y + 1 ∧ x + 1 = y) := by
  rintro ⟨h1, h2⟩
  have h : ((2 : ℕ) : ZMod n) = 0 := by
    calc ((2 : ℕ) : ZMod n) = (y + 1 + 1) - y := by push_cast; ring
      _ = 0 := by rw [← h1, h2, sub_self]
  have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 n).mp h)
  exact absurd (Fact.out : 2 < n) (not_lt.mpr this)

/-- On a torus of width at least three, distinct vertices have distinct right edges. -/
theorem torusRightEdge_injective [Fact (2 < width)] :
    Function.Injective (torusRightEdge (width := width) (height := height)) := by
  intro p q h
  have hp := Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2)
  have hq := Edge.ofAdj_endpoints (torusGraph_adj_right q.1 q.2)
  change Edge.ofAdj _ = Edge.ofAdj _ at h
  rw [h] at hp
  rcases hp with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hq with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact (a1.symm.trans b1)
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e1.1, e2.1⟩
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e2.1, e1.1⟩
  · exact (a2.symm.trans b2)

/-- On a torus of height at least three, distinct vertices have distinct up edges. -/
theorem torusUpEdge_injective [Fact (2 < height)] :
    Function.Injective (torusUpEdge (width := width) (height := height)) := by
  intro p q h
  have hp := Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2)
  have hq := Edge.ofAdj_endpoints (torusGraph_adj_up q.1 q.2)
  change Edge.ofAdj _ = Edge.ofAdj _ at h
  rw [h] at hp
  rcases hp with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hq with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact (a1.symm.trans b1)
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e1.2, e2.2⟩
  · exfalso
    have e1 := a1.symm.trans b1
    have e2 := a2.symm.trans b2
    simp only [Prod.mk.injEq] at e1 e2
    exact zmod_not_add_one_eq_and_add_one_eq _ _ ⟨e2.2, e1.2⟩
  · exact (a2.symm.trans b2)

/-- No right edge is an up edge. -/
theorem torusRightEdge_ne_torusUpEdge (p q : TorusVertex width height) :
    torusRightEdge p ≠ torusUpEdge q := fun h =>
  torusEdge_not_horizontal_and_vertical (torusUpEdge q)
    ⟨h ▸ isHorizontalTorusEdge_torusRightEdge p, isVerticalTorusEdge_torusUpEdge q⟩

variable [Fact (2 < width)] [Fact (2 < height)]

/-- On a torus of width and height at least three, the edges are exactly the right edges and
the up edges of the vertices, each counted once. -/
noncomputable def torusEdgeEquiv :
    TorusVertex width height ⊕ TorusVertex width height ≃ Edge (torusGraph width height) :=
  Equiv.ofBijective (Sum.elim torusRightEdge torusUpEdge) <| by
    refine ⟨?_, fun e => ?_⟩
    · rintro (p | p) (q | q) h
      · exact congrArg Sum.inl (torusRightEdge_injective h)
      · exact absurd h (torusRightEdge_ne_torusUpEdge p q)
      · exact absurd h.symm (torusRightEdge_ne_torusUpEdge q p)
      · exact congrArg Sum.inr (torusUpEdge_injective h)
    · rcases torusEdge_horizontal_or_vertical e with he | he
      · obtain ⟨p, rfl⟩ := isHorizontalTorusEdge_eq_rightEdge he
        exact ⟨Sum.inl p, rfl⟩
      · obtain ⟨p, rfl⟩ := isVerticalTorusEdge_eq_upEdge he
        exact ⟨Sum.inr p, rfl⟩

/-- Bridge: on a torus of width and height at least three, the coefficient of a torus
site-tensor PEPS is the lattice contraction over a horizontal bond array `hb` (the index on
the right edge of each vertex) and a vertical bond array `vb` (the index on the up edge of
each vertex). The tensor at `v = (x, y)` reads `vb v` on top, `hb v` on the right,
`vb (x, y - 1)` below, and `hb (x - 1, y)` on the left.

Source: arXiv:2011.12127, Appendix A, "Two dimensions: PEPS",
`Papers/2011.12127/TN-Review-main.tex` line 2415. -/
theorem stateCoeff_torusSiteTensor {D d : ℕ}
    (a : Fin D → Fin D → Fin D → Fin D → Fin d → ℂ)
    (σ : TorusVertex width height → Fin d) :
    stateCoeff (torusSiteTensor a) σ =
      ∑ hb : TorusVertex width height → Fin D, ∑ vb : TorusVertex width height → Fin D,
        ∏ v, a (vb v) (hb v) (vb (v.1, v.2 - 1)) (hb (v.1 - 1, v.2)) (σ v) := by
  rw [stateCoeff_torusSiteTensor_eq_sum_edge, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    ((Equiv.arrowCongr torusEdgeEquiv.symm (Equiv.refl _)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)) _ _ (fun η => rfl)

end PEPS
end TNLean
