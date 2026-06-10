import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap6
import TNLean.PEPS.RegionBlock.UnionClosure
import TNLean.PEPS.NormalEdgeComplementCover
import TNLean.PEPS.SquareLatticeGraph

/-!
# Square-lattice region injectivity from the overlapping union lemma

Theorem 3 of arXiv:1804.04964 assumes that every contiguous `2×3` and `3×2`
region of a normal square-lattice PEPS is injective, and then states that the
displayed regions `R`, `S`, and `T` are injective "by repeatedly applying the
union lemma".  This file supplies the faithful tensor-level route to that
conclusion.

The overlapping union-of-injective-regions lemma
`regionBlockedTensorInjective_union_overlap` shows that for two blocked-region
injective regions with positive bond dimensions, their union is injective, with
no disjointness assumption.  Its finite iteration over a nonempty family,
`regionBlockedTensorInjective_biUnion_overlap`, is the overlapping analogue of
the disjoint iteration `regionBlockedTensorInjective_biUnion_disjoint`.

The abstract region-injectivity framework of `TNLean.PEPS.InjectiveRegion`
carries the displayed-region derivations parametrically over the union-closure
hypothesis `RegionInjectivityUnionClosure`.  Here that hypothesis is discharged
faithfully: the concrete region-injectivity predicate of a PEPS tensor with
positive bond dimensions satisfies union closure *because the union of two
injective regions is injective* (`regionInjectivityUnionClosure_of_overlap`),
not because every region is injective.  Feeding this faithful provider into the
existing parametric chain gives injectivity of the displayed regions `R` and
`S` from rectangular injectivity and positive bond dimensions alone, with no
single-vertex injectivity hypothesis.

The displayed local-window region `T` at the origin has no exact cover by
contiguous `2×3` and `3×2` rectangles (the point-forcing obstruction
`not_normalSquareRegionT_rectangleCover_at_origin`), so its injectivity is not
derivable from rectangular covers in this local model; the faithful provider is
nonetheless threaded through the conditional `T`-cover assembly so that, once a
source-faithful cover is supplied, the full blocking-region structure follows
from rectangular injectivity and positivity alone.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma `injective_union` and Theorem 3, lines 1322--1443 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The finite overlapping union -/

/-- **The finite union of injective regions is injective.** For a nonempty finite
family of regions whose blocked tensors are each injective, and with every virtual
bond dimension positive, the blocked tensor of their union is injective.

This is the finite iteration of the overlapping union lemma
`regionBlockedTensorInjective_union_overlap`.  Unlike the disjoint iteration
`regionBlockedTensorInjective_biUnion_disjoint`, it needs no disjointness on the
family: the binary overlapping lemma carries through directly.  It is the
"repeatedly applying the union lemma" step used in the source proof, where the
displayed regions are presented as unions of overlapping injective rectangles.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and the examples
following it, lines 1322--1430 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_biUnion_overlap {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (R : ι → Finset V)
    (hR : ∀ i ∈ s, RegionBlockedTensorInjective (G := G) A (R i))
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) :
    RegionBlockedTensorInjective (G := G) A (s.biUnion R) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hR i (by simp)
  | cons i t hi _ ih =>
      rw [Finset.cons_eq_insert, Finset.biUnion_insert]
      exact regionBlockedTensorInjective_union_overlap
        (hR i (by simp)) (ih fun j hj => hR j (by simp [hj])) hpos

/-! ### The faithful union-closure provider -/

/-- **The faithful union-closure provider.** The concrete region-injectivity
predicate of a PEPS tensor with positive bond dimensions satisfies the
union-closure assertion of the source injective-union lemma: the union of two
injective regions is injective.

The union-closure field is discharged by the overlapping union lemma
`regionBlockedTensorInjective_union_overlap`, which uses the injectivity of both
argument regions.  This is the source-faithful provider of
`RegionInjectivityUnionClosure`: it derives injectivity of the union from
injectivity of the two regions, in contrast with the vertex-injective
`regionInjectivityUnionClosure_of_isVertexInjective`, which discharges the same
field from the stronger hypothesis that every region is injective.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines
1322--1404 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInjectivityUnionClosure_of_overlap (A : Tensor G d)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    RegionInjectivityUnionClosure (regionInjectivityDataOf (G := G) A) where
  union_injective hR hS :=
    regionBlockedTensorInjective_union_overlap hR hS hpos

end PEPS
end TNLean

/-! ### Faithful injectivity of the displayed square-lattice regions -/

namespace TNLean
namespace PEPS

variable {width height : ℕ}
variable {G : SimpleGraph (SquareLatticeVertex width height)} [DecidableRel G.Adj]
variable {A : Tensor G d}

/-- **Region `R` is injective from rectangular injectivity alone.** If a normal
square-lattice PEPS tensor has positive bond dimensions and every contiguous
`2×3` and `3×2` rectangle is blocked-tensor injective, then the displayed
region `R` is blocked-tensor injective.

This is the faithful square-lattice instance of the source claim that `R` is a
union of smaller injective rectangles, with the union closure discharged by the
overlapping union lemma rather than by single-vertex injectivity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_normalSquareRegionR
    (h : NormalSquareLatticeRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := G) A))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    RegionBlockedTensorInjective (G := G) A
      (normalSquareRegionR xStart yStart) :=
  h.regionR_injective_of_union (regionInjectivityUnionClosure_of_overlap A hpos) hx hy

/-- **Region `S` is injective from rectangular injectivity alone.** If a normal
square-lattice PEPS tensor has positive bond dimensions and every contiguous
`2×3` and `3×2` rectangle is blocked-tensor injective, then the displayed
region `S` is blocked-tensor injective.

This is the faithful square-lattice instance of the source claim that `S` is a
union of smaller injective rectangles, with the union closure discharged by the
overlapping union lemma rather than by single-vertex injectivity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_normalSquareRegionS
    (h : NormalSquareLatticeRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := G) A))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    RegionBlockedTensorInjective (G := G) A
      (normalSquareRegionS xStart yStart) :=
  h.regionS_injective_of_union (regionInjectivityUnionClosure_of_overlap A hpos) hx hy

/-- **Region `T` is injective from rectangular injectivity and a supplied cover.**
If a normal square-lattice PEPS tensor has positive bond dimensions, every
contiguous `2×3` and `3×2` rectangle is blocked-tensor injective, and the
displayed region `T` has a cover by such rectangles, then `T` is blocked-tensor
injective.

**Scope restriction (T-cover):** A rectangular cover of the displayed
`T`-region is supplied as a hypothesis.  The displayed origin-window `T` has no
such cover (`not_normalSquareRegionT_rectangleCover_at_origin`), so this
conditional result is not the source's local-window `T` argument; the
source-faithful finite-geometry route is recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".  The union closure is discharged by the overlapping
union lemma rather than by single-vertex injectivity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1443 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_normalSquareRegionT
    (h : NormalSquareLatticeRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := G) A))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    {xStart yStart : ℕ}
    (cover : NormalSquareRegionTRectangleCover (width := width) (height := height)
      xStart yStart) :
    RegionBlockedTensorInjective (G := G) A
      (normalSquareRegionT xStart yStart) :=
  h.regionT_injective_of_cover (regionInjectivityUnionClosure_of_overlap A hpos) cover

/-- **The full square-lattice blocking-region structure from rectangular
injectivity and a supplied `T`-cover.** If a normal square-lattice PEPS tensor
of size at least `7×7` has positive bond dimensions, every contiguous `2×3` and
`3×2` rectangle is blocked-tensor injective, and the displayed region `T` at the
origin has a rectangular cover, then the abstract blocking-region structure of
Theorem 3 holds for the concrete region-injectivity predicate.

The union closure used to assemble `R`, `S`, and `T` is the faithful overlapping
union provider, so the only hypotheses beyond rectangular injectivity and size
are the positive bond dimensions and the supplied `T`-cover.

**Scope restriction (T-cover):** see
`regionBlockedTensorInjective_normalSquareRegionT`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def normalSquareBlockingRegions_of_overlap
    (h : NormalSquareLatticeRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := G) A))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hWidth : 7 ≤ width) (hHeight : 7 ≤ height)
    (cover : NormalSquareRegionTRectangleCover (width := width) (height := height) 0 0) :
    NormalSquareBlockingRegions (regionInjectivityDataOf (G := G) A) :=
  normalSquareBlockingRegions_of_TCover h (regionInjectivityUnionClosure_of_overlap A hpos)
    hWidth hHeight cover

end PEPS
end TNLean
