import TNLean.PEPS.InjectiveRegion
import TNLean.PEPS.TorusLatticeGraph

/-!
# Contiguous coordinate rectangles on the discrete torus

The translationally invariant normal PEPS theorem (arXiv:1804.04964, Section 3, proof of
Theorem 3) assumes that every contiguous $2\times3$ and $3\times2$ block of the lattice is
injective.  On the discrete torus the contiguous block at coordinate origin `(xStart, yStart)`
with side lengths `(xLen, yLen)` is the set of vertices whose coordinate values lie in the
half-open coordinate intervals `[xStart, xStart + xLen)` and `[yStart, yStart + yLen)`, read
through the value embedding `ZMod.val`.  When the offsets and lengths avoid wraparound
(`xStart + xLen ≤ width`, `yStart + yLen ≤ height`), this is exactly the contiguous block; the
full-coordinate band (length `width` or `height`) is the whole coordinate range, which the value
embedding covers without wraparound.

These torus rectangles are the wraparound-avoiding analogue of the open-lattice contiguous
rectangles of `TNLean/PEPS/NormalBlocking.lean`, and the rectangular-injectivity hypotheses and
sliding-window tiling lemmas below are the torus ports of
`TNLean/PEPS/NormalRectangleTiling.lean`.  The reference edge of the normal PEPS construction sits
at the coordinate origin, so the construction's regions span only a few cells and stay clear of the
wraparound seam.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### The torus contiguous rectangle -/

/-- A contiguous coordinate rectangle on the discrete torus: the vertices whose coordinate values
lie in the half-open coordinate intervals `[xStart, xStart + xLen)` and `[yStart, yStart + yLen)`.

When the offsets and lengths avoid wraparound (`xStart + xLen ≤ width`, `yStart + yLen ≤ height`)
this is the contiguous block at `(xStart, yStart)`; a full-coordinate band (length `width` or
`height`) is the whole coordinate range, which the value embedding covers without wraparound.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusContiguousRectangle (xStart yStart xLen yLen : ℕ) :
    Finset (TorusVertex width height) :=
  Finset.univ.filter fun v =>
    xStart ≤ v.1.val ∧ v.1.val < xStart + xLen ∧
      yStart ≤ v.2.val ∧ v.2.val < yStart + yLen

@[simp] theorem mem_torusContiguousRectangle (xStart yStart xLen yLen : ℕ)
    (v : TorusVertex width height) :
    v ∈ torusContiguousRectangle xStart yStart xLen yLen ↔
      xStart ≤ v.1.val ∧ v.1.val < xStart + xLen ∧
        yStart ≤ v.2.val ∧ v.2.val < yStart + yLen := by
  simp [torusContiguousRectangle]

/-! ### Contiguous-rectangle shape predicates -/

/-- Contiguous torus rectangles of width two and height three.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the theorem assumes injectivity for contiguous
$2\times3$ rectangular blocks. -/
def IsTwoByThreeContiguousTorusRectangle
    (R : Finset (TorusVertex width height)) : Prop :=
  ∃ xStart yStart : ℕ,
    xStart + 2 ≤ width ∧ yStart + 3 ≤ height ∧
      R = torusContiguousRectangle xStart yStart 2 3

/-- Contiguous torus rectangles of width three and height two.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the theorem assumes injectivity for contiguous
$3\times2$ rectangular blocks. -/
def IsThreeByTwoContiguousTorusRectangle
    (R : Finset (TorusVertex width height)) : Prop :=
  ∃ xStart yStart : ℕ,
    xStart + 3 ≤ width ∧ yStart + 2 ≤ height ∧
      R = torusContiguousRectangle xStart yStart 3 2

/-- A bounded contiguous torus rectangle of width two and height three has the $2\times3$ source
shape.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoByThreeContiguousTorusRectangle_of_bounds
    {xStart yStart : ℕ} (hx : xStart + 2 ≤ width) (hy : yStart + 3 ≤ height) :
    IsTwoByThreeContiguousTorusRectangle
      (torusContiguousRectangle xStart yStart 2 3 : Finset (TorusVertex width height)) :=
  ⟨xStart, yStart, hx, hy, rfl⟩

/-- A bounded contiguous torus rectangle of width three and height two has the $3\times2$ source
shape.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isThreeByTwoContiguousTorusRectangle_of_bounds
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 2 ≤ height) :
    IsThreeByTwoContiguousTorusRectangle
      (torusContiguousRectangle xStart yStart 3 2 : Finset (TorusVertex width height)) :=
  ⟨xStart, yStart, hx, hy, rfl⟩

/-! ### The torus rectangular-injectivity hypotheses -/

/-- The coordinate rectangular-injectivity hypotheses on the discrete torus: every contiguous
$2\times3$ and $3\times2$ block is injective.  This is the torus specialization of the abstract
region-injectivity hypotheses to the vertex set `TorusVertex width height`, matching the
open-lattice `NormalSquareLatticeRectangleInjectivityHypotheses`.

Source: arXiv:1804.04964, Section 3, Theorem 3 and proof, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
structure NormalTorusRectangleInjectivityHypotheses
    (κ : RegionInjectivityData (TorusVertex width height)) where
  /-- Every contiguous $2\times3$ coordinate rectangle is injective. -/
  twoByThree_injective :
    ∀ R : Finset (TorusVertex width height),
      IsTwoByThreeContiguousTorusRectangle R → κ.IsInjective R
  /-- Every contiguous $3\times2$ coordinate rectangle is injective. -/
  threeByTwo_injective :
    ∀ R : Finset (TorusVertex width height),
      IsThreeByTwoContiguousTorusRectangle R → κ.IsInjective R

namespace NormalTorusRectangleInjectivityHypotheses

variable {κ : RegionInjectivityData (TorusVertex width height)}

/-- A bounded contiguous $2\times3$ coordinate rectangle is injective under the torus rectangular
injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, Theorem 3 and proof, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem rect23_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 2 ≤ width) (hy : yStart + 3 ≤ height) :
    κ.IsInjective
      (torusContiguousRectangle xStart yStart 2 3 : Finset (TorusVertex width height)) :=
  h.twoByThree_injective _ (isTwoByThreeContiguousTorusRectangle_of_bounds hx hy)

/-- A bounded contiguous $3\times2$ coordinate rectangle is injective under the torus rectangular
injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, Theorem 3 and proof, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem rect32_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 2 ≤ height) :
    κ.IsInjective
      (torusContiguousRectangle xStart yStart 3 2 : Finset (TorusVertex width height)) :=
  h.threeByTwo_injective _ (isThreeByTwoContiguousTorusRectangle_of_bounds hx hy)

/-! ### Sliding-window tiling injectivity -/

/-- A wide-or-tall contiguous torus rectangle is the union of contiguous source $2\times3$
rectangles sliding over it.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1322--1430 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem contiguousRectangle_eq_biUnion_two_by_three
    (xStart yStart xLen yLen : ℕ) (hx : 2 ≤ xLen) (hy : 3 ≤ yLen) :
    (torusContiguousRectangle xStart yStart xLen yLen : Finset (TorusVertex width height)) =
      (Finset.range (xLen - 1) ×ˢ Finset.range (yLen - 2)).biUnion
        (fun p => torusContiguousRectangle (xStart + p.1) (yStart + p.2) 2 3) := by
  ext v
  simp only [mem_torusContiguousRectangle, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    refine ⟨(min (v.1.val - xStart) (xLen - 2), min (v.2.val - yStart) (yLen - 3)), ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · rintro ⟨⟨a, b⟩, ⟨_, _⟩, hv⟩
    omega

/-- A wide-or-tall contiguous torus rectangle is injective.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem wideRectangle_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart xLen yLen : ℕ}
    (hx : 2 ≤ xLen) (hy : 3 ≤ yLen)
    (hxw : xStart + xLen ≤ width) (hyh : yStart + yLen ≤ height) :
    κ.IsInjective
      (torusContiguousRectangle xStart yStart xLen yLen : Finset (TorusVertex width height)) := by
  rw [contiguousRectangle_eq_biUnion_two_by_three xStart yStart xLen yLen hx hy]
  refine hUnion.biUnion_injective ?_ _ ?_
  · exact ⟨(0, 0), by simp [Finset.mem_product, Finset.mem_range]; omega⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, Finset.mem_range] at hab
    exact h.rect23_injective (by omega) (by omega)

/-- A wide-and-short contiguous torus rectangle is the union of contiguous source $3\times2$
rectangles sliding over it.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1322--1430 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem contiguousRectangle_eq_biUnion_three_by_two
    (xStart yStart xLen yLen : ℕ) (hx : 3 ≤ xLen) (hy : 2 ≤ yLen) :
    (torusContiguousRectangle xStart yStart xLen yLen : Finset (TorusVertex width height)) =
      (Finset.range (xLen - 2) ×ˢ Finset.range (yLen - 1)).biUnion
        (fun p => torusContiguousRectangle (xStart + p.1) (yStart + p.2) 3 2) := by
  ext v
  simp only [mem_torusContiguousRectangle, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    refine ⟨(min (v.1.val - xStart) (xLen - 3), min (v.2.val - yStart) (yLen - 2)), ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · rintro ⟨⟨a, b⟩, ⟨_, _⟩, hv⟩
    omega

/-- A wide-and-short contiguous torus rectangle is injective.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1452 of `Papers/1804.04964/paper_normal.tex`. -/
theorem shortRectangle_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart xLen yLen : ℕ}
    (hx : 3 ≤ xLen) (hy : 2 ≤ yLen)
    (hxw : xStart + xLen ≤ width) (hyh : yStart + yLen ≤ height) :
    κ.IsInjective
      (torusContiguousRectangle xStart yStart xLen yLen : Finset (TorusVertex width height)) := by
  rw [contiguousRectangle_eq_biUnion_three_by_two xStart yStart xLen yLen hx hy]
  refine hUnion.biUnion_injective ?_ _ ?_
  · exact ⟨(0, 0), by simp [Finset.mem_product, Finset.mem_range]; omega⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, Finset.mem_range] at hab
    exact h.rect32_injective (by omega) (by omega)

end NormalTorusRectangleInjectivityHypotheses

end PEPS
end TNLean
