import TNLean.PEPS.RegionBlock.ThreeBlockTransfer
import TNLean.PEPS.EdgeMiddlePhysical.Basic

/-!
# The coarse three-site tensor for the normal PEPS theorem

The normal PEPS proof blocks a neighbourhood of each edge into three injective
regions and then applies the injective three-site comparison to that blocking.
The injective comparison machinery (`TNLean.PEPS.InsertionAlgebra`,
`TNLean.PEPS.InsertionRealization`, `TNLean.PEPS.EdgeMiddlePhysical`) operates
on a single-vertex three-site chain: its endpoint injectivity is
`Function.Injective (localTensorMap A v)`, single-vertex linear independence.
A normal tensor need not be vertex injective, so the comparison cannot be run on
the original tensor at the edge endpoints.

The source argument never uses the single vertex. After blocking, the three
sites of the chain are the **blocks**: the red region around one endpoint, the
blue region around the other, and the complement. The "component family" of each
super-site is the blocked-region weight family, which is injective by the normal
blocking hypothesis. This file builds the blocked chain as an honest `Tensor` on
a three-vertex complete graph, so that the proven single-vertex three-site
comparison applies verbatim to the super-sites.

The three coarse vertices are `r`, `b`, `c`. The coarse edges are `r-b` (the
original distinguished edge), `r-c` (the red-to-complement crossing bonds bundled
into one), and `b-c` (the blue-to-complement crossing bonds bundled into one).
The coarse physical dimension is the uniform padded dimension `d ^ (card V)`,
large enough to carry every region's physical configuration through a fixed
surjection.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1449--1500 (the blocking) and lines 254--583 (the injective
  three-site comparison applied to the blocked chain)](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The coarse three-vertex graph

The coarse graph is the complete graph on `Fin 3`. Its vertices are `0` (red
super-site `r`), `1` (blue super-site `b`), and `2` (complement super-site `c`).
Its three edges are `0-1`, `0-2`, and `1-2`. -/

/-- The coarse three-vertex graph: the complete graph on `Fin 3`. -/
abbrev coarseGraph : SimpleGraph (Fin 3) := ⊤

instance : DecidableRel (coarseGraph).Adj := fun a b => by
  unfold coarseGraph; simp only [SimpleGraph.top_adj]; infer_instance

/-- The coarse `r-b` edge `0-1`: the image of the original distinguished edge. -/
def coarseEdgeRB : Edge coarseGraph :=
  ⟨(0, 1), by constructor <;> simp [coarseGraph]⟩

/-- The coarse `r-c` edge `0-2`: the bundled red-to-complement crossing bonds. -/
def coarseEdgeRC : Edge coarseGraph :=
  ⟨(0, 2), by constructor <;> simp [coarseGraph]⟩

/-- The coarse `b-c` edge `1-2`: the bundled blue-to-complement crossing bonds. -/
def coarseEdgeBC : Edge coarseGraph :=
  ⟨(1, 2), by constructor <;> simp [coarseGraph]⟩

end PEPS
end TNLean
