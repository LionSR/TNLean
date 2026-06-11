import TNLean.PEPS.TorusRectangleRegion
import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.RegionBlock.Basic

/-!
# The corner comparison region of the torus Fundamental Theorem

The final comparison of the normal PEPS Fundamental Theorem on the torus runs over a region `R`
and the one-site-larger region `S = R ∪ {v}` (arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1544--1571 of `Papers/1804.04964/paper_normal.tex`).  This file builds the reference
instance of that pair from the source's rectangular-injectivity hypotheses: the **corner
region** is a `3 × 3` coordinate square minus its lower-left corner, so that

* the corner region is the union of a `2 × 3` and a `3 × 2` rectangle, hence injective;
* inserting the corner vertex completes the square, a `3 × 3` rectangle, hence injective;
* both complements decompose into coordinate bands (and one corner rectangle), all of source
  shape, hence injective by union closure; and
* both regions have a boundary edge.

Every torus vertex is a translate of the corner vertex, so transporting this single reference
pair along the translations supplies the comparison pair at every site.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1571
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### The corner square, corner region, and corner vertex -/

/-- The `3 × 3` coordinate square at offset `(2, 2)`. -/
def cornerSquare : Finset (TorusVertex width height) :=
  torusContiguousRectangle 2 2 3 3

/-- The corner region: the `3 × 3` square at `(2, 2)` minus its lower-left corner, presented as
the union of a `2 × 3` rectangle and a `3 × 2` rectangle. -/
def cornerRegion : Finset (TorusVertex width height) :=
  torusContiguousRectangle 3 2 2 3 ∪ torusContiguousRectangle 2 3 3 2

/-- The corner vertex `(2, 2)`, the lower-left corner of the corner square. -/
def cornerVertex : TorusVertex width height :=
  (((2 : ℕ) : ZMod width), ((2 : ℕ) : ZMod height))

/-- Membership in the corner region, in coordinate values. -/
theorem mem_cornerRegion (v : TorusVertex width height) :
    v ∈ cornerRegion ↔
      (3 ≤ v.1.val ∧ v.1.val < 5 ∧ 2 ≤ v.2.val ∧ v.2.val < 5) ∨
        (2 ≤ v.1.val ∧ v.1.val < 5 ∧ 3 ≤ v.2.val ∧ v.2.val < 5) := by
  simp only [cornerRegion, Finset.mem_union, mem_torusContiguousRectangle]

/-- A vertex is the corner vertex exactly when its coordinate values are `(2, 2)`. -/
theorem eq_cornerVertex_iff (hw : 7 ≤ width) (hh : 7 ≤ height)
    (v : TorusVertex width height) :
    v = cornerVertex ↔ v.1.val = 2 ∧ v.2.val = 2 := by
  constructor
  · rintro rfl
    exact ⟨ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext (ZMod.val_injective width ?_) (ZMod.val_injective height ?_)
    · rw [h1]
      exact (ZMod.val_cast_of_lt (by omega : (2 : ℕ) < width)).symm
    · rw [h2]
      exact (ZMod.val_cast_of_lt (by omega : (2 : ℕ) < height)).symm

/-- The corner vertex lies outside the corner region. -/
theorem cornerVertex_notMem_cornerRegion (hw : 7 ≤ width) (hh : 7 ≤ height) :
    (cornerVertex : TorusVertex width height) ∉ cornerRegion := by
  rw [mem_cornerRegion]
  have h1 : (cornerVertex : TorusVertex width height).1.val = 2 :=
    ZMod.val_cast_of_lt (by omega)
  have h2 : (cornerVertex : TorusVertex width height).2.val = 2 :=
    ZMod.val_cast_of_lt (by omega)
  omega

/-- Inserting the corner vertex into the corner region completes the corner square. -/
theorem insert_cornerVertex_cornerRegion (hw : 7 ≤ width) (hh : 7 ≤ height) :
    insert (cornerVertex : TorusVertex width height) cornerRegion = cornerSquare := by
  ext v
  rw [Finset.mem_insert, mem_cornerRegion, eq_cornerVertex_iff hw hh,
    cornerSquare, mem_torusContiguousRectangle]
  omega

/-! ### The band decompositions of the complements -/

/-- The complement of the corner square is the union of four coordinate bands. -/
theorem compl_cornerSquare_eq_bands (hw : 7 ≤ width) (hh : 7 ≤ height) :
    Finset.univ \ (cornerSquare : Finset (TorusVertex width height)) =
      torusContiguousRectangle 0 0 2 height ∪
        (torusContiguousRectangle 5 0 (width - 5) height ∪
          (torusContiguousRectangle 2 0 3 2 ∪ torusContiguousRectangle 2 5 3 (height - 5))) := by
  ext v
  have hx := ZMod.val_lt v.1
  have hy := ZMod.val_lt v.2
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    cornerSquare, mem_torusContiguousRectangle]
  omega

/-- The complement of the corner region is the union of the four bands and the corner
rectangle covering the corner vertex. -/
theorem compl_cornerRegion_eq_bands (hw : 7 ≤ width) (hh : 7 ≤ height) :
    Finset.univ \ (cornerRegion : Finset (TorusVertex width height)) =
      torusContiguousRectangle 0 1 3 2 ∪
        (torusContiguousRectangle 0 0 2 height ∪
          (torusContiguousRectangle 5 0 (width - 5) height ∪
            (torusContiguousRectangle 2 0 3 2 ∪
              torusContiguousRectangle 2 5 3 (height - 5)))) := by
  ext v
  have hx := ZMod.val_lt v.1
  have hy := ZMod.val_lt v.2
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, mem_cornerRegion,
    mem_torusContiguousRectangle]
  omega

/-! ### Injectivity of the corner regions and their complements -/

namespace NormalTorusRectangleInjectivityHypotheses

variable {κ : RegionInjectivityData (TorusVertex width height)}

/-- The corner region is injective: it is the union of a `2 × 3` and a `3 × 2` source
rectangle.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem cornerRegion_injective (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hw : 7 ≤ width) (hh : 7 ≤ height) :
    κ.IsInjective (cornerRegion : Finset (TorusVertex width height)) :=
  hUnion.union_injective (h.rect23_injective (by omega) (by omega))
    (h.rect32_injective (by omega) (by omega))

/-- The corner square is injective: it is a `3 × 3` rectangle.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem cornerSquare_injective (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hw : 7 ≤ width) (hh : 7 ≤ height) :
    κ.IsInjective (cornerSquare : Finset (TorusVertex width height)) :=
  h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)

/-- The complement of the corner square is injective: it is the union of four coordinate
bands, each of source shape.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem compl_cornerSquare_injective (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hw : 7 ≤ width) (hh : 7 ≤ height) :
    κ.IsInjective (Finset.univ \ (cornerSquare : Finset (TorusVertex width height))) := by
  rw [compl_cornerSquare_eq_bands hw hh]
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  exact hUnion.union_injective
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))

/-- The complement of the corner region is injective: it is the union of the four bands and a
`3 × 2` corner rectangle.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem compl_cornerRegion_injective (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hw : 7 ≤ width) (hh : 7 ≤ height) :
    κ.IsInjective (Finset.univ \ (cornerRegion : Finset (TorusVertex width height))) := by
  rw [compl_cornerRegion_eq_bands hw hh]
  refine hUnion.union_injective
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  exact hUnion.union_injective
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))

end NormalTorusRectangleInjectivityHypotheses

/-! ### Boundary edges of the corner regions -/

section BoundaryEdges

variable [Fact (1 < width)] [Fact (1 < height)]

/-- The up edge of the corner vertex is a boundary edge of the corner region: the corner
vertex lies outside, its upper neighbour `(2, 3)` inside. -/
theorem isRegionBoundaryEdge_cornerRegion (hw : 7 ≤ width) (hh : 7 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height) cornerRegion
      (torusUpEdge (cornerVertex : TorusVertex width height)) := by
  have hout : (cornerVertex : TorusVertex width height) ∉ cornerRegion :=
    cornerVertex_notMem_cornerRegion hw hh
  have hin : ((cornerVertex : TorusVertex width height).1,
      (cornerVertex : TorusVertex width height).2 + 1) ∈ cornerRegion := by
    rw [mem_cornerRegion]
    have h1 : ((cornerVertex : TorusVertex width height).1).val = 2 :=
      ZMod.val_cast_of_lt (by omega)
    have h2 : ((cornerVertex : TorusVertex width height).2 + 1).val = 3 := by
      rw [show (cornerVertex : TorusVertex width height).2 + 1 = ((3 : ℕ) : ZMod height) by
        rw [cornerVertex]; push_cast; ring]
      exact ZMod.val_cast_of_lt (by omega)
    dsimp only
    omega
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up
      (cornerVertex : TorusVertex width height).1
      (cornerVertex : TorusVertex width height).2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [show (torusUpEdge (cornerVertex : TorusVertex width height)).1.1 =
        ((cornerVertex : TorusVertex width height).1,
          (cornerVertex : TorusVertex width height).2) from h1, Prod.mk.eta]
      exact hout
    · rw [show (torusUpEdge (cornerVertex : TorusVertex width height)).1.2 =
        ((cornerVertex : TorusVertex width height).1,
          (cornerVertex : TorusVertex width height).2 + 1) from h2]
      exact hin
  · refine Or.inl ⟨?_, ?_⟩
    · rw [show (torusUpEdge (cornerVertex : TorusVertex width height)).1.1 =
        ((cornerVertex : TorusVertex width height).1,
          (cornerVertex : TorusVertex width height).2 + 1) from h1]
      exact hin
    · rw [show (torusUpEdge (cornerVertex : TorusVertex width height)).1.2 =
        ((cornerVertex : TorusVertex width height).1,
          (cornerVertex : TorusVertex width height).2) from h2, Prod.mk.eta]
      exact hout

/-- The vertex `(2, 1)` directly below the corner vertex. -/
def belowCornerVertex : TorusVertex width height :=
  (((2 : ℕ) : ZMod width), ((1 : ℕ) : ZMod height))

/-- The up edge of `(2, 1)` is a boundary edge of the corner square: `(2, 1)` lies outside,
its upper neighbour `(2, 2)` inside. -/
theorem isRegionBoundaryEdge_cornerSquare (hw : 7 ≤ width) (hh : 7 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height) cornerSquare
      (torusUpEdge (belowCornerVertex : TorusVertex width height)) := by
  have hout : (belowCornerVertex : TorusVertex width height) ∉ cornerSquare := by
    rw [cornerSquare, mem_torusContiguousRectangle]
    have h2 : ((belowCornerVertex : TorusVertex width height).2).val = 1 :=
      ZMod.val_cast_of_lt (by omega)
    omega
  have hin : ((belowCornerVertex : TorusVertex width height).1,
      (belowCornerVertex : TorusVertex width height).2 + 1) ∈ cornerSquare := by
    rw [cornerSquare, mem_torusContiguousRectangle]
    have h1 : ((belowCornerVertex : TorusVertex width height).1).val = 2 :=
      ZMod.val_cast_of_lt (by omega)
    have h2 : ((belowCornerVertex : TorusVertex width height).2 + 1).val = 2 := by
      rw [show (belowCornerVertex : TorusVertex width height).2 + 1 =
          ((2 : ℕ) : ZMod height) by
        rw [belowCornerVertex]; push_cast; ring]
      exact ZMod.val_cast_of_lt (by omega)
    dsimp only
    omega
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up
      (belowCornerVertex : TorusVertex width height).1
      (belowCornerVertex : TorusVertex width height).2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [show (torusUpEdge (belowCornerVertex : TorusVertex width height)).1.1 =
        ((belowCornerVertex : TorusVertex width height).1,
          (belowCornerVertex : TorusVertex width height).2) from h1, Prod.mk.eta]
      exact hout
    · rw [show (torusUpEdge (belowCornerVertex : TorusVertex width height)).1.2 =
        ((belowCornerVertex : TorusVertex width height).1,
          (belowCornerVertex : TorusVertex width height).2 + 1) from h2]
      exact hin
  · refine Or.inl ⟨?_, ?_⟩
    · rw [show (torusUpEdge (belowCornerVertex : TorusVertex width height)).1.1 =
        ((belowCornerVertex : TorusVertex width height).1,
          (belowCornerVertex : TorusVertex width height).2 + 1) from h1]
      exact hin
    · rw [show (torusUpEdge (belowCornerVertex : TorusVertex width height)).1.2 =
        ((belowCornerVertex : TorusVertex width height).1,
          (belowCornerVertex : TorusVertex width height).2) from h2, Prod.mk.eta]
      exact hout

end BoundaryEdges

end PEPS
end TNLean
