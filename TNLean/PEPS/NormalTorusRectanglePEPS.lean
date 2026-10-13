/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRectangleRegion
import TNLean.PEPS.NormalSquareInjectivity

/-!
# Normal PEPS tensors on the torus with injective rectangles

Theorem 3 of arXiv:1804.04964 concerns two normal PEPS tensors on the torus such that every
contiguous `2 × 3` and `3 × 2` region is injective.  This file states that tensor hypothesis,
`IsNormalTorusRectanglePEPS`, and derives from it the union closure of injective regions (the
source's Lemma `injective_union`).  It sits below both the existence statement of Theorem 3
and its uniqueness clause, so that both state the same tensor hypothesis.

**Local fix (nonzero virtual spaces):** the source treats the virtual bond spaces as nonzero
(arXiv:1804.04964, lines 582 and 1037 of `Papers/1804.04964/paper_normal.tex`) without listing
this among the hypotheses of Theorem 3.  Injectivity does not imply it: zero-dimensional bonds
can make every relevant local domain empty, so injectivity holds vacuously.  The structure
`IsNormalTorusRectanglePEPS` carries the convention as the field `bondDim_pos`.  Documented in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, Lemma `injective_union` and
  Theorem 3, lines 1322--1471 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- A normal PEPS tensor on the torus in the setting of Theorem 3: every contiguous `2 × 3`
and `3 × 2` rectangle is injective, and every virtual bond space is nonzero.  The rectangle
fields are the region-family hypothesis `NormalTorusRectangleInjectivityHypotheses` read for
the injective regions of the tensor.

The field `bondDim_pos` is the nonzero virtual-space convention of the module docstring.

Source: arXiv:1804.04964, Section 3, Theorem 3, lines 1453--1454 of
`Papers/1804.04964/paper_normal.tex` ("two normal 2D PEPS tensors such that every `2 × 3`
and `3 × 2` region is injective"), with normality as defined at line 1318. -/
structure IsNormalTorusRectanglePEPS (A : Tensor (torusGraph width height) d) : Prop
    extends NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A) where
  /-- Every virtual bond space is nonzero: the source's bond spaces are nonzero throughout
  (arXiv:1804.04964, lines 582 and 1037 of `Papers/1804.04964/paper_normal.tex`); the
  convention is recorded in `docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
  bondDim_pos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e

/-- The union closure of injective regions of a normal torus tensor, from its nonzero
bonds (the source's Lemma `injective_union`, lines 1322--1404 of
`Papers/1804.04964/paper_normal.tex`). -/
theorem IsNormalTorusRectanglePEPS.unionClosure {A : Tensor (torusGraph width height) d}
    (hA : IsNormalTorusRectanglePEPS A) :
    RegionInjectivityUnionClosure (regionInjectivityDataOf (G := torusGraph width height) A) :=
  regionInjectivityUnionClosure_of_overlap A hA.bondDim_pos

end PEPS
end TNLean
