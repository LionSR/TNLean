import TNLean.PEPS.TorusRectangleRegion

/-!
# The horizontal and vertical edge-blocking regions on the discrete torus

The normal PEPS edge blocking around a horizontal edge partitions the torus into the removed
vertical edge block (the red region, a contiguous $2\times3$ rectangle), the removed horizontal
edge block (the blue region, a contiguous $3\times2$ rectangle), and the complement of these two
removed blocks (the complementary region).  This file records those three regions on the torus,
their membership characterizations, and the rectangular cover of the complementary region by four
surrounding bands and two fillers.

The blocking is anchored at the coordinate offset `(xStart, yStart)`: the red block sits at
`(xStart, yStart + 2)` and the blue block at `(xStart + 2, yStart + 1)`, so the only
nearest-neighbour pair with one endpoint in each is the edge from `(xStart + 1, yStart + 2)` to
`(xStart + 2, yStart + 2)`.  The vertical analogue is the rotated picture, anchored so its single
crossing is the edge from `(xStart + 2, yStart + 1)` to `(xStart + 2, yStart + 2)`.

No region wraps the seam: the surrounding bands are full coordinate ranges in one direction, which
the value embedding covers without wraparound, and the removed blocks and fillers fit inside the
coordinate window `[xStart - 1, xStart + 5) × [yStart - 1, yStart + 5)`.  The window may touch the
seam on the right and top (`xStart + 5 = width`, `yStart + 5 = height`), where the corresponding
band is empty; this seam-touching anchor is what realizes the blocking on every torus with the
source's sizes `n, m ≥ 7`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### Horizontal edge-blocking regions -/

/-- The red block (removed vertical edge block) of the horizontal torus edge blocking: the
contiguous $2\times3$ rectangle at `(xStart, yStart + 2)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusHorizontalEdgeRed (xStart yStart : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle xStart (yStart + 2) 2 3

/-- The blue block (removed horizontal edge block) of the horizontal torus edge blocking: the
contiguous $3\times2$ rectangle at `(xStart + 2, yStart + 1)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusHorizontalEdgeBlue (xStart yStart : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle (xStart + 2) (yStart + 1) 3 2

/-- The complementary block of the horizontal torus edge blocking: the complement of the two
removed blocks.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusHorizontalEdgeComplement (xStart yStart : ℕ) : Finset (TorusVertex width height) :=
  Finset.univ \ (torusHorizontalEdgeRed xStart yStart ∪ torusHorizontalEdgeBlue xStart yStart)

@[simp] theorem mem_torusHorizontalEdgeRed (xStart yStart : ℕ) (v : TorusVertex width height) :
    v ∈ torusHorizontalEdgeRed xStart yStart ↔
      xStart ≤ v.1.val ∧ v.1.val < xStart + 2 ∧
        yStart + 2 ≤ v.2.val ∧ v.2.val < yStart + 5 := by
  simp only [torusHorizontalEdgeRed, mem_torusContiguousRectangle, show yStart + 2 + 3 = yStart + 5
    from by omega]

@[simp] theorem mem_torusHorizontalEdgeBlue (xStart yStart : ℕ) (v : TorusVertex width height) :
    v ∈ torusHorizontalEdgeBlue xStart yStart ↔
      xStart + 2 ≤ v.1.val ∧ v.1.val < xStart + 5 ∧
        yStart + 1 ≤ v.2.val ∧ v.2.val < yStart + 3 := by
  simp only [torusHorizontalEdgeBlue, mem_torusContiguousRectangle,
    show xStart + 2 + 3 = xStart + 5 from by omega, show yStart + 1 + 2 = yStart + 3 from by omega]

@[simp] theorem mem_torusHorizontalEdgeComplement (xStart yStart : ℕ)
    (v : TorusVertex width height) :
    v ∈ torusHorizontalEdgeComplement xStart yStart ↔
      v ∉ torusHorizontalEdgeRed xStart yStart ∧ v ∉ torusHorizontalEdgeBlue xStart yStart := by
  simp only [torusHorizontalEdgeComplement, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, not_or]

/-! ### Partition by the three horizontal regions -/

/-- The horizontal red and blue blocks are disjoint: the removed vertical and horizontal edge
blocks meet only along the distinguished edge, so no vertex lies in both.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusHorizontalEdgeRed_disjoint_blue (xStart yStart : ℕ) :
    Disjoint (torusHorizontalEdgeRed (width := width) (height := height) xStart yStart)
      (torusHorizontalEdgeBlue xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hRed hBlue
  rw [mem_torusHorizontalEdgeRed] at hRed
  rw [mem_torusHorizontalEdgeBlue] at hBlue
  omega

/-- The horizontal red block is disjoint from the complement. -/
theorem torusHorizontalEdgeRed_disjoint_complement (xStart yStart : ℕ) :
    Disjoint (torusHorizontalEdgeRed (width := width) (height := height) xStart yStart)
      (torusHorizontalEdgeComplement xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hRed hCompl
  rw [mem_torusHorizontalEdgeComplement] at hCompl
  exact hCompl.1 hRed

/-- The horizontal blue block is disjoint from the complement. -/
theorem torusHorizontalEdgeBlue_disjoint_complement (xStart yStart : ℕ) :
    Disjoint (torusHorizontalEdgeBlue (width := width) (height := height) xStart yStart)
      (torusHorizontalEdgeComplement xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hBlue hCompl
  rw [mem_torusHorizontalEdgeComplement] at hCompl
  exact hCompl.2 hBlue

/-- The three horizontal regions cover the torus.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusHorizontalEdge_cover_univ (xStart yStart : ℕ) :
    torusHorizontalEdgeRed (width := width) (height := height) xStart yStart ∪
        torusHorizontalEdgeBlue xStart yStart ∪ torusHorizontalEdgeComplement xStart yStart =
      Finset.univ := by
  ext v
  simp only [Finset.mem_union, mem_torusHorizontalEdgeComplement, Finset.mem_univ, iff_true]
  by_cases hRed : v ∈ torusHorizontalEdgeRed xStart yStart
  · exact Or.inl (Or.inl hRed)
  · by_cases hBlue : v ∈ torusHorizontalEdgeBlue xStart yStart
    · exact Or.inl (Or.inr hBlue)
    · exact Or.inr ⟨hRed, hBlue⟩

/-! ### The horizontal complementary cover -/

/-- The six rectangular pieces covering the horizontal edge-complement block on the torus: four
surrounding bands and two fillers.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusHorizontalEdgeComplementPiece (xStart yStart : ℕ) :
    Fin 6 → Finset (TorusVertex width height)
  | 0 => torusContiguousRectangle 0 0 width (yStart + 1)
  | 1 => torusContiguousRectangle 0 (yStart + 5) width (height - (yStart + 5))
  | 2 => torusContiguousRectangle 0 (yStart + 1) xStart 4
  | 3 => torusContiguousRectangle (xStart + 5) (yStart + 1) (width - (xStart + 5)) 4
  | 4 => torusContiguousRectangle xStart (yStart - 1) 2 3
  | 5 => torusContiguousRectangle (xStart + 2) (yStart + 3) 3 2

/-- The horizontal edge-complement block on the torus is the union of its six covering pieces, for
an offset with one row of margin below and the removed blocks inside the coordinate ranges; the
pieces on the seam side may be empty.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusHorizontalEdgeComplement_eq_biUnion_pieces {xStart yStart : ℕ}
    (hy0 : 1 ≤ yStart) (hxw : xStart + 5 ≤ width) (hyh : yStart + 5 ≤ height) :
    torusHorizontalEdgeComplement (width := width) (height := height) xStart yStart =
      (Finset.univ : Finset (Fin 6)).biUnion
        (torusHorizontalEdgeComplementPiece xStart yStart) := by
  ext v
  have hvx : v.1.val < width := v.1.val_lt
  have hvy : v.2.val < height := v.2.val_lt
  simp only [mem_torusHorizontalEdgeComplement, mem_torusHorizontalEdgeRed,
    mem_torusHorizontalEdgeBlue, Finset.mem_biUnion, Finset.mem_univ, true_and, not_and, not_lt]
  constructor
  · intro hv
    obtain ⟨hRed, hBlue⟩ := hv
    by_cases hb : v.2.val < yStart + 1
    · exact ⟨0, by simp [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    by_cases ht : yStart + 5 ≤ v.2.val
    · exact ⟨1, by simp [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    by_cases hl : v.1.val < xStart
    · exact ⟨2, by simp [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    by_cases hr : xStart + 5 ≤ v.1.val
    · exact ⟨3, by simp [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    -- inside the bounding box of the hole; the two fillers cover the non-hole cells
    by_cases hf1 : v.1.val < xStart + 2
    · exact ⟨4, by simp [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    · exact ⟨5, by simp [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;>
      · simp only [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle] at hi
        refine ⟨fun _ _ _ => by omega, fun _ _ _ => by omega⟩

namespace NormalTorusRectangleInjectivityHypotheses

variable {κ : RegionInjectivityData (TorusVertex width height)}

/-- The horizontal red block (removed vertical edge block) is injective under the torus
rectangular injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1405--1444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalEdgeRed_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 2 ≤ width) (hy : yStart + 5 ≤ height) :
    κ.IsInjective (torusHorizontalEdgeRed (width := width) (height := height) xStart yStart) :=
  h.rect23_injective hx (by omega)

/-- The horizontal blue block (removed horizontal edge block) is injective under the torus
rectangular injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1405--1444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalEdgeBlue_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 3 ≤ height) :
    κ.IsInjective (torusHorizontalEdgeBlue (width := width) (height := height) xStart yStart) :=
  h.rect32_injective (by omega) (by omega)

/-- **The horizontal edge-complement block on the torus is injective.**

The complementary block is the union of four surrounding bands and two filler rectangles, each a
contiguous torus rectangle; rectangular injectivity together with the union-of-injective-regions
lemma proves it injective.  Below and to the left the removed L-shape keeps a margin of at least
two columns (`2 ≤ xStart`) and at least two rows (`1 ≤ yStart`, the filler dipping one further row
down); above and to the right the margin is either zero — the blocking touches the seam, the band
is empty — or at least two, so each nonempty band is a source-shaped rectangle.  The seam-touching
choice `xStart + 5 = width`, `yStart + 5 = height` realizes the blocking on every torus with the
source's sizes `n, m ≥ 7`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalEdgeComplement_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ} (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    κ.IsInjective
      (torusHorizontalEdgeComplement (width := width) (height := height) xStart yStart) := by
  rw [torusHorizontalEdgeComplement_eq_biUnion_pieces (by omega) (by omega) (by omega)]
  refine hUnion.biUnion_injective_of_nonempty _
    ⟨0, Finset.mem_univ _, ⟨((0 : ZMod width), (0 : ZMod height)), by
      simp only [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle, ZMod.val_zero]
      omega⟩⟩ ?_
  intro i _ hne
  fin_cases i
  · -- bottom band: width × (yStart + 1), short rectangle (width ≥ 3, yStart + 1 ≥ 2)
    exact h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- top band: width × (height - (yStart + 5)), short rectangle when nonempty
    obtain ⟨v, hv⟩ := hne
    simp only [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle] at hv
    exact h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- left band: xStart × 4, wide rectangle (xStart ≥ 2, 4 ≥ 3)
    exact h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- right band: (width - (xStart + 5)) × 4, wide rectangle when nonempty
    obtain ⟨v, hv⟩ := hne
    simp only [torusHorizontalEdgeComplementPiece, mem_torusContiguousRectangle] at hv
    exact h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- first filler: 2 × 3
    exact h.rect23_injective (by omega) (by omega)
  · -- second filler: 3 × 2
    exact h.rect32_injective (by omega) (by omega)

end NormalTorusRectangleInjectivityHypotheses

/-! ### Vertical edge-blocking regions

The rotated picture: the red block (removed horizontal edge block) is the contiguous $3\times2$
rectangle at `(xStart + 2, yStart)`, the blue block (removed vertical edge block) is the contiguous
$2\times3$ rectangle at `(xStart + 1, yStart + 2)`, and the only nearest-neighbour pair with one
endpoint in each is the edge from `(xStart + 2, yStart + 1)` to `(xStart + 2, yStart + 2)`. -/

/-- The red block (removed horizontal edge block) of the vertical torus edge blocking: the
contiguous $3\times2$ rectangle at `(xStart + 2, yStart)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusVerticalEdgeRed (xStart yStart : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle (xStart + 2) yStart 3 2

/-- The blue block (removed vertical edge block) of the vertical torus edge blocking: the
contiguous $2\times3$ rectangle at `(xStart + 1, yStart + 2)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusVerticalEdgeBlue (xStart yStart : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle (xStart + 1) (yStart + 2) 2 3

/-- The complementary block of the vertical torus edge blocking: the complement of the two removed
blocks.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusVerticalEdgeComplement (xStart yStart : ℕ) : Finset (TorusVertex width height) :=
  Finset.univ \ (torusVerticalEdgeRed xStart yStart ∪ torusVerticalEdgeBlue xStart yStart)

@[simp] theorem mem_torusVerticalEdgeRed (xStart yStart : ℕ) (v : TorusVertex width height) :
    v ∈ torusVerticalEdgeRed xStart yStart ↔
      xStart + 2 ≤ v.1.val ∧ v.1.val < xStart + 5 ∧
        yStart ≤ v.2.val ∧ v.2.val < yStart + 2 := by
  simp only [torusVerticalEdgeRed, mem_torusContiguousRectangle,
    show xStart + 2 + 3 = xStart + 5 from by omega]

@[simp] theorem mem_torusVerticalEdgeBlue (xStart yStart : ℕ) (v : TorusVertex width height) :
    v ∈ torusVerticalEdgeBlue xStart yStart ↔
      xStart + 1 ≤ v.1.val ∧ v.1.val < xStart + 3 ∧
        yStart + 2 ≤ v.2.val ∧ v.2.val < yStart + 5 := by
  simp only [torusVerticalEdgeBlue, mem_torusContiguousRectangle,
    show xStart + 1 + 2 = xStart + 3 from by omega, show yStart + 2 + 3 = yStart + 5 from by omega]

@[simp] theorem mem_torusVerticalEdgeComplement (xStart yStart : ℕ)
    (v : TorusVertex width height) :
    v ∈ torusVerticalEdgeComplement xStart yStart ↔
      v ∉ torusVerticalEdgeRed xStart yStart ∧ v ∉ torusVerticalEdgeBlue xStart yStart := by
  simp only [torusVerticalEdgeComplement, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, not_or]

/-! ### Partition by the three vertical regions -/

/-- The vertical red and blue blocks are disjoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusVerticalEdgeRed_disjoint_blue (xStart yStart : ℕ) :
    Disjoint (torusVerticalEdgeRed (width := width) (height := height) xStart yStart)
      (torusVerticalEdgeBlue xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hRed hBlue
  rw [mem_torusVerticalEdgeRed] at hRed
  rw [mem_torusVerticalEdgeBlue] at hBlue
  omega

/-- The vertical red block is disjoint from the complement. -/
theorem torusVerticalEdgeRed_disjoint_complement (xStart yStart : ℕ) :
    Disjoint (torusVerticalEdgeRed (width := width) (height := height) xStart yStart)
      (torusVerticalEdgeComplement xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hRed hCompl
  rw [mem_torusVerticalEdgeComplement] at hCompl
  exact hCompl.1 hRed

/-- The vertical blue block is disjoint from the complement. -/
theorem torusVerticalEdgeBlue_disjoint_complement (xStart yStart : ℕ) :
    Disjoint (torusVerticalEdgeBlue (width := width) (height := height) xStart yStart)
      (torusVerticalEdgeComplement xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hBlue hCompl
  rw [mem_torusVerticalEdgeComplement] at hCompl
  exact hCompl.2 hBlue

/-- The three vertical regions cover the torus.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusVerticalEdge_cover_univ (xStart yStart : ℕ) :
    torusVerticalEdgeRed (width := width) (height := height) xStart yStart ∪
        torusVerticalEdgeBlue xStart yStart ∪ torusVerticalEdgeComplement xStart yStart =
      Finset.univ := by
  ext v
  simp only [Finset.mem_union, mem_torusVerticalEdgeComplement, Finset.mem_univ, iff_true]
  by_cases hRed : v ∈ torusVerticalEdgeRed xStart yStart
  · exact Or.inl (Or.inl hRed)
  · by_cases hBlue : v ∈ torusVerticalEdgeBlue xStart yStart
    · exact Or.inl (Or.inr hBlue)
    · exact Or.inr ⟨hRed, hBlue⟩

/-! ### The vertical complementary cover -/

/-- The six rectangular pieces covering the vertical edge-complement block on the torus: four
surrounding bands and two filler $2\times3$ rectangles.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusVerticalEdgeComplementPiece (xStart yStart : ℕ) :
    Fin 6 → Finset (TorusVertex width height)
  | 0 => torusContiguousRectangle 0 0 width yStart
  | 1 => torusContiguousRectangle 0 (yStart + 5) width (height - (yStart + 5))
  | 2 => torusContiguousRectangle 0 0 (xStart + 1) height
  | 3 => torusContiguousRectangle (xStart + 5) 0 (width - (xStart + 5)) height
  | 4 => torusContiguousRectangle xStart (yStart - 1) 2 3
  | 5 => torusContiguousRectangle (xStart + 3) (yStart + 2) 2 3

/-- The vertical edge-complement block on the torus is the union of its six covering pieces.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusVerticalEdgeComplement_eq_biUnion_pieces {xStart yStart : ℕ}
    (hy0 : 1 ≤ yStart) (hxw : xStart + 5 ≤ width) (hyh : yStart + 5 ≤ height) :
    torusVerticalEdgeComplement (width := width) (height := height) xStart yStart =
      (Finset.univ : Finset (Fin 6)).biUnion
        (torusVerticalEdgeComplementPiece xStart yStart) := by
  ext v
  have hvx : v.1.val < width := v.1.val_lt
  have hvy : v.2.val < height := v.2.val_lt
  simp only [mem_torusVerticalEdgeComplement, mem_torusVerticalEdgeRed,
    mem_torusVerticalEdgeBlue, Finset.mem_biUnion, Finset.mem_univ, true_and, not_and, not_lt]
  constructor
  · intro hv
    obtain ⟨hRed, hBlue⟩ := hv
    by_cases hb : v.2.val < yStart
    · exact ⟨0, by simp [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    by_cases ht : yStart + 5 ≤ v.2.val
    · exact ⟨1, by simp [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    by_cases hl : v.1.val < xStart + 1
    · exact ⟨2, by simp [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    by_cases hr : xStart + 5 ≤ v.1.val
    · exact ⟨3, by simp [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    -- inside the bounding box of the rotated hole; the two fillers cover the non-hole cells
    by_cases hf1 : v.2.val < yStart + 2
    · exact ⟨4, by simp [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
    · exact ⟨5, by simp [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle]; omega⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;>
      · simp only [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle] at hi
        refine ⟨fun _ _ _ => by omega, fun _ _ _ => by omega⟩

namespace NormalTorusRectangleInjectivityHypotheses

variable {κ : RegionInjectivityData (TorusVertex width height)}

/-- The vertical red block (removed horizontal edge block) is injective under the torus rectangular
injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1405--1444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem verticalEdgeRed_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 2 ≤ height) :
    κ.IsInjective (torusVerticalEdgeRed (width := width) (height := height) xStart yStart) :=
  h.rect32_injective (by omega) hy

/-- The vertical blue block (removed vertical edge block) is injective under the torus rectangular
injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1405--1444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem verticalEdgeBlue_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 5 ≤ height) :
    κ.IsInjective (torusVerticalEdgeBlue (width := width) (height := height) xStart yStart) :=
  h.rect23_injective (by omega) (by omega)

/-- **The vertical edge-complement block on the torus is injective.**

The rotated counterpart of `horizontalEdgeComplement_injective`: the complementary block is the
union of four surrounding bands and two filler rectangles, each a contiguous torus rectangle.
Below and to the left the rotated removed L-shape keeps a margin of at least two rows
(`2 ≤ yStart`) and at least two columns (`1 ≤ xStart`, counting the L-shape's own free column);
above and to the right the margin is either zero — the blocking touches the seam, the band is
empty — or at least two.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem verticalEdgeComplement_injective
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ} (hx0 : 1 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    κ.IsInjective
      (torusVerticalEdgeComplement (width := width) (height := height) xStart yStart) := by
  rw [torusVerticalEdgeComplement_eq_biUnion_pieces (by omega) (by omega) (by omega)]
  refine hUnion.biUnion_injective_of_nonempty _
    ⟨2, Finset.mem_univ _, ⟨((0 : ZMod width), (0 : ZMod height)), by
      simp only [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle, ZMod.val_zero]
      omega⟩⟩ ?_
  intro i _ hne
  fin_cases i
  · -- bottom band: width × yStart, short rectangle (width ≥ 3, yStart ≥ 2)
    exact h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- top band: width × (height - (yStart + 5)), short rectangle when nonempty
    obtain ⟨v, hv⟩ := hne
    simp only [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle] at hv
    exact h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- left band: (xStart + 1) × height, wide rectangle (xStart + 1 ≥ 2, height ≥ 3)
    exact h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- right band: (width - (xStart + 5)) × height, wide rectangle when nonempty
    obtain ⟨v, hv⟩ := hne
    simp only [torusVerticalEdgeComplementPiece, mem_torusContiguousRectangle] at hv
    exact h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
  · -- first filler: 2 × 3
    exact h.rect23_injective (by omega) (by omega)
  · -- second filler: 2 × 3
    exact h.rect23_injective (by omega) (by omega)

end NormalTorusRectangleInjectivityHypotheses

end PEPS
end TNLean
