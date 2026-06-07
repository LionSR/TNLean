import TNLean.PEPS.RegionBlock.KernelDescent
import TNLean.PEPS.SingletonRegion

/-!
# Concrete region-injectivity union closure for vertex-injective PEPS

The abstract region-injectivity framework of `TNLean.PEPS.InjectiveRegion`
records a predicate `RegionInjectivityData` assigning injectivity to finite
vertex regions, together with the union-closure hypothesis
`RegionInjectivityUnionClosure` that the union of two injective regions is
injective. This file instantiates that framework concretely for a
vertex-injective PEPS tensor.

The concrete predicate sends a region `R` to injectivity of the blocked-region
tensor family, `RegionBlockedTensorInjective A R`. The kernel-descent result
`regionBlockedTensorInjective_of_isVertexInjective` of
`TNLean.PEPS.RegionBlock.KernelDescent` shows that *every* finite region is
injective once `A` is vertex-injective and every bond dimension is positive.
The union-closure hypothesis is therefore discharged directly: for the concrete
predicate, `R ∪ S` is injective regardless of the injectivity of `R` and `S`.
The same input also supplies the singleton comparison of
`TNLean.PEPS.SingletonRegion`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, lines 205--250, 1205--1210, and 1322--1404](https://arxiv.org/abs/1804.04964)
-/

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

/-- The conditional union of two injective regions is injective, for a
vertex-injective PEPS tensor with positive bond dimensions.

The conclusion is the source statement `inj(R) ∧ inj(S) ⟹ inj(R ∪ S)`. Under
vertex injectivity it holds unconditionally on the two region hypotheses,
because every finite region is injective; the hypotheses are kept so the
statement matches the source implication.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1322--1404 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_union_of_isVertexInjective (A : Tensor G d)
    (hA : IsVertexInjective A) (hpos : ∀ e : Edge G, 0 < A.bondDim e) {R S : Finset V}
    (_hR : RegionBlockedTensorInjective (G := G) A R)
    (_hS : RegionBlockedTensorInjective (G := G) A S) :
    RegionBlockedTensorInjective (G := G) A (R ∪ S) :=
  regionBlockedTensorInjective_of_isVertexInjective (G := G) A (R ∪ S) hA hpos

/-- The singleton comparison for the concrete region-injectivity predicate of a
vertex-injective PEPS tensor: injectivity of a singleton blocked tensor implies
injectivity of the corresponding singleton region.

For the concrete predicate the conclusion `regionInjectivityDataOf A` injective
on `{v}` is exactly the kernel-descent result at the region `{v}`, so the
hypothesis on the singleton tensor is not needed.

Source: arXiv:1804.04964, Section 3, lines 981--1009 and 1322--1404 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem singletonRegionInjectivityComparison_of_isVertexInjective (A : Tensor G d)
    (hA : IsVertexInjective A) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    SingletonRegionInjectivityComparison (G := G) (d := d)
      (regionInjectivityDataOf (G := G) A) A where
  singleton_region_injective v _ :=
    regionBlockedTensorInjective_of_isVertexInjective (G := G) A {v} hA hpos

end PEPS
end TNLean
