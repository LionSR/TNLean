/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.Torus.TorusTranslationInvariant

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
bonds; the bridge is stated for width and height at least three. The resulting restriction
on the cluster and CZX examples is documented in
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

The four legs (`torusTopLeg`, `torusRightLeg`, `torusDownLeg`, `torusLeftLeg`) and the
edge equivalence `torusEdgeEquiv` are torus geometry, recorded in
`TNLean/PEPS/Graph/Torus/TorusLatticeGraph.lean`.

## Main definitions

* `TNLean.PEPS.torusSiteTensor`: the torus PEPS of a four-leg site tensor.

## Main results

* `TNLean.PEPS.stateCoeff_torusSiteTensor_eq_sum_edge`: the coefficient as a sum over edge
  labellings.
* `TNLean.PEPS.stateCoeff_torusSiteTensor`: the coefficient as a sum over horizontal and
  vertical bond arrays.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open ManyBody (Edge)

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Reindexing a product over the torus by the unit horizontal shift: a product of factors
joining each site to its left neighbour equals the product of the same factors joining each
site to its right neighbour. -/
theorem prod_torus_sub_fst {M : Type*} [CommMonoid M]
    (f : TorusVertex width height → TorusVertex width height → M) :
    ∏ v, f v (v.1 - 1, v.2) = ∏ v, f (v.1 + 1, v.2) v :=
  (Fintype.prod_equiv (Equiv.addRight ((1, 0) : TorusVertex width height)) _ _ fun u => by
    simp only [Equiv.coe_addRight,
      show u + (1, 0) = (u.1 + 1, u.2) from Prod.ext rfl (add_zero _),
      add_sub_cancel_right]).symm

/-- Reindexing a product over the torus by the unit vertical shift: a product of factors
joining each site to its lower neighbour equals the product of the same factors joining each
site to its upper neighbour. -/
theorem prod_torus_sub_snd {M : Type*} [CommMonoid M]
    (f : TorusVertex width height → TorusVertex width height → M) :
    ∏ v, f v (v.1, v.2 - 1) = ∏ v, f (v.1, v.2 + 1) v :=
  (Fintype.prod_equiv (Equiv.addRight ((0, 1) : TorusVertex width height)) _ _ fun u => by
    simp only [Equiv.coe_addRight,
      show u + (0, 1) = (u.1, u.2 + 1) from Prod.ext (add_zero _) rfl,
      add_sub_cancel_right]).symm

variable [Fact (1 < width)] [Fact (1 < height)]

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

variable [Fact (2 < width)] [Fact (2 < height)]

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
