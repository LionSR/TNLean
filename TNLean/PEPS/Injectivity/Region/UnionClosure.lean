/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Graph.Region.InjectiveRegion
import TNLean.PEPS.Injectivity.Region.RegionKernelDescent
import TNLean.PEPS.Injectivity.Region.OverlapUnion

/-!
# Concrete region-injectivity union closure

The abstract region-injectivity framework of `TNLean.PEPS.InjectiveRegion`
records a predicate `RegionInjectivityData` assigning injectivity to finite
vertex regions, together with the union-closure hypothesis
`RegionInjectivityUnionClosure` that the union of two injective regions is
injective. This file instantiates that framework concretely for a PEPS tensor
with positive bond dimensions.

The concrete predicate sends a region `R` to injectivity of the blocked-region
tensor family, `RegionBlockedTensorInjective A R`. It is union closed whenever
every bond dimension is positive (`regionInjectivityUnionClosure_of_overlap`),
by the overlapping union lemma `regionBlockedTensorInjective_union_overlap`.
For a vertex-injective tensor the kernel-descent result
`regionBlockedTensorInjective_of_isVertexInjective` of
`TNLean.PEPS.RegionBlock.KernelDescent` shows that *every* finite region is
injective once `A` is vertex-injective and every bond dimension is positive.
The union-closure hypothesis is therefore discharged directly: for the concrete
predicate, `R ∪ S` is injective regardless of the injectivity of `R` and `S`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, lines 205--250, 1205--1210, and 1322--1404](https://arxiv.org/abs/1804.04964)
-/

open ManyBody (Edge)

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The concrete region-injectivity predicate of a PEPS tensor: a finite region
`R` is injective when its blocked-region tensor family is linearly independent.

Source: arXiv:1804.04964, Section 3, lines 1322--1404 of
`Papers/1804.04964/paper_normal.tex`. -/
def regionInjectivityDataOf (A : Tensor G d) : RegionInjectivityData V where
  IsInjective R := RegionBlockedTensorInjective (G := G) A R

@[simp] theorem regionInjectivityDataOf_isInjective (A : Tensor G d) (R : Finset V) :
    (regionInjectivityDataOf (G := G) A).IsInjective R =
      RegionBlockedTensorInjective (G := G) A R := rfl

/-- The concrete region-injectivity predicate of a vertex-injective PEPS tensor
satisfies union closure: the union of two injective regions is injective.

The proof discharges the union-closure hypothesis directly from the
kernel-descent result that every finite region is injective; the injectivity of
the two argument regions is not needed.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404 of `Papers/1804.04964/paper_normal.tex`, with the positive-bond
hypothesis recorded in `docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
theorem regionInjectivityUnionClosure_of_isVertexInjective (A : Tensor G d)
    (hA : IsVertexInjective A) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    RegionInjectivityUnionClosure (regionInjectivityDataOf (G := G) A) where
  union_injective {R S} _ _ :=
    regionBlockedTensorInjective_of_isVertexInjective (G := G) A (R ∪ S) hA hpos

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
