import TNLean.PEPS.NormalBlocking

/-!
# Rectangular covers in the normal PEPS proof

This file records the parametric rectangular-cover structure and the
conditional injectivity criteria for the local displayed \(T\)-region and the
finite-lattice edge-complementary block \(A_3\) in the square-lattice normal
PEPS proof.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma lem:injective_union and Theorem 3]
-/

namespace TNLean
namespace PEPS

/-- A finite rectangular cover of a square-lattice region.

Each member of the cover is required to be one of the source-paper contiguous
\(2\times3\) or \(3\times2\) rectangles. Such a cover is a sufficient coordinate
condition for the union-of-injective-regions lemma to prove injectivity of the
target region.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
structure SquareLatticeRectangleCover {width height : ℕ}
    (target : Finset (SquareLatticeVertex width height)) where
  /-- The finite index set labelling the rectangular pieces. -/
  Index : Type*
  /-- The finite family of pieces used in the cover. -/
  regions : Finset Index
  /-- The cover is nonempty, so finite union closure applies. -/
  nonempty : regions.Nonempty
  /-- The rectangular piece indexed by `i`. -/
  region : Index → Finset (SquareLatticeVertex width height)
  /-- Every piece is one of the two rectangular shapes assumed injective. -/
  rectangular :
    ∀ i ∈ regions,
      IsTwoByThreeContiguousSquareLatticeRectangle (region i) ∨
        IsThreeByTwoContiguousSquareLatticeRectangle (region i)
  /-- The rectangular pieces cover exactly the target region. -/
  cover : regions.biUnion region = target

/-- A point-forcing obstruction to an exact rectangular cover.

If a point \(p\) belongs to the target, every source-paper \(2\times3\)
rectangle containing \(p\) also contains a point \(q_{23}\) outside the target,
and every source-paper \(3\times2\) rectangle containing \(p\) also contains a
point \(q_{32}\) outside the target, then no exact rectangular cover of the
target exists.

Source context: arXiv:1804.04964, Section 3, Lemma lem:injective_union and
proof of Theorem 3, lines 1322--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem not_squareLatticeRectangleCover_of_forced_points {width height : ℕ}
    {target : Finset (SquareLatticeVertex width height)}
    {p q23 q32 : SquareLatticeVertex width height}
    (hp : p ∈ target)
    (h23 :
      ∀ xStart yStart : ℕ,
        p ∈ (squareLatticeContiguousRectangle xStart yStart 2 3 :
          Finset (SquareLatticeVertex width height)) →
        q23 ∈ (squareLatticeContiguousRectangle xStart yStart 2 3 :
          Finset (SquareLatticeVertex width height)))
    (hq23 : q23 ∉ target)
    (h32 :
      ∀ xStart yStart : ℕ,
        p ∈ (squareLatticeContiguousRectangle xStart yStart 3 2 :
          Finset (SquareLatticeVertex width height)) →
        q32 ∈ (squareLatticeContiguousRectangle xStart yStart 3 2 :
          Finset (SquareLatticeVertex width height)))
    (hq32 : q32 ∉ target) :
    ¬ Nonempty (SquareLatticeRectangleCover target) := by
  rintro ⟨cover⟩
  have hpUnion : p ∈ cover.regions.biUnion cover.region := by
    rw [cover.cover]
    exact hp
  rcases Finset.mem_biUnion.mp hpUnion with ⟨i, hi, hpi⟩
  rcases cover.rectangular i hi with hRect | hRect
  · rcases hRect with ⟨xStart, yStart, _hx, _hy, hRegion⟩
    have hpRect :
        p ∈ (squareLatticeContiguousRectangle xStart yStart 2 3 :
          Finset (SquareLatticeVertex width height)) := by
      simpa [hRegion] using hpi
    have hqRegion : q23 ∈ cover.region i := by
      simpa [hRegion] using h23 xStart yStart hpRect
    have hqUnion : q23 ∈ cover.regions.biUnion cover.region :=
      Finset.mem_biUnion.mpr ⟨i, hi, hqRegion⟩
    exact hq23 (by rwa [cover.cover] at hqUnion)
  · rcases hRect with ⟨xStart, yStart, _hx, _hy, hRegion⟩
    have hpRect :
        p ∈ (squareLatticeContiguousRectangle xStart yStart 3 2 :
          Finset (SquareLatticeVertex width height)) := by
      simpa [hRegion] using hpi
    have hqRegion : q32 ∈ cover.region i := by
      simpa [hRegion] using h32 xStart yStart hpRect
    have hqUnion : q32 ∈ cover.regions.biUnion cover.region :=
      Finset.mem_biUnion.mpr ⟨i, hi, hqRegion⟩
    exact hq32 (by rwa [cover.cover] at hqUnion)

/-- A finite rectangular cover of the displayed local \(T\)-region.

Each member of the cover is required to be one of the source-paper contiguous
\(2\times3\) or \(3\times2\) rectangles. Such a cover is a sufficient
coordinate condition for the union-of-injective-regions lemma to prove
injectivity of \(T\).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1444
of `Papers/1804.04964/paper_normal.tex`. -/
abbrev NormalSquareRegionTRectangleCover {width height : ℕ} (xStart yStart : ℕ) :=
  SquareLatticeRectangleCover
    (normalSquareRegionT (width := width) (height := height) xStart yStart)

/-- A finite rectangular cover of the edge-complementary block \(A_3\).

Each member of the cover is required to be one of the source-paper contiguous
\(2\times3\) or \(3\times2\) rectangles. Such a cover is a sufficient
coordinate condition for the union-of-injective-regions lemma to prove
injectivity of the finite-lattice complementary block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
abbrev NormalSquareEdgeComplementRectangleCover {width height : ℕ} (xStart yStart : ℕ) :=
  SquareLatticeRectangleCover
    (normalSquareEdgeComplementRegion (width := width) (height := height) xStart yStart)

/-- The current origin-based local-window model for \(T\) has no rectangular
cover by contained source-paper \(2\times3\) and \(3\times2\) rectangles.

This is a diagnostic statement about the present coordinate model
`normalSquareRegionT`, not a claim about the source theorem.  The source says
that \(T\) is injective for sufficiently large PEPS; this lemma records that
the present local-window complement is not yet the source rectangular cover
needed to prove that sentence.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1430--1444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareRegionT_rectangleCover_at_origin {width height : ℕ}
    (hx : 5 ≤ width) (hy : 6 ≤ height) :
    ¬ Nonempty
      (NormalSquareRegionTRectangleCover (width := width) (height := height)
        0 0) := by
  let p : SquareLatticeVertex width height :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  let q23 : SquareLatticeVertex width height :=
    (⟨0, by omega⟩, ⟨2, by omega⟩)
  let q32 : SquareLatticeVertex width height :=
    (⟨2, by omega⟩, ⟨1, by omega⟩)
  exact not_squareLatticeRectangleCover_of_forced_points (p := p)
    (q23 := q23) (q32 := q32)
    (by simp [p])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q23] at hpRect ⊢
      omega)
    (by simp [q23])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q32] at hpRect ⊢
      omega)
    (by simp [q32])

/-- The current normalized \(5\times6\) local-window model for \(T\) has no
rectangular cover by contained source-paper \(2\times3\) and \(3\times2\)
rectangles.

This is the normalized form of
`not_normalSquareRegionT_rectangleCover_at_origin`.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1430--1444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareRegionT_rectangleCover_five_by_six :
    ¬ Nonempty (NormalSquareRegionTRectangleCover (width := 5) (height := 6) 0 0) := by
  exact not_normalSquareRegionT_rectangleCover_at_origin (by decide) (by decide)

/-- The current origin-based horizontal edge-complement model has no
rectangular cover by contained source-paper \(2\times3\) and \(3\times2\)
rectangles.

This is a diagnostic statement about the present
`NormalSquareEdgeComplementRectangleCover` criterion, not a claim about the
source theorem's injectivity assertion for \(A_3\). It records that this cover
criterion is not yet the source construction of the complementary block.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareEdgeComplementRectangleCover_at_origin {width height : ℕ}
    (hx : 5 ≤ width) (hy : 7 ≤ height) :
    ¬ Nonempty
      (NormalSquareEdgeComplementRectangleCover (width := width) (height := height)
        0 0) := by
  let p : SquareLatticeVertex width height :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  let q23 : SquareLatticeVertex width height :=
    (⟨0, by omega⟩, ⟨2, by omega⟩)
  let q32 : SquareLatticeVertex width height :=
    (⟨2, by omega⟩, ⟨1, by omega⟩)
  exact not_squareLatticeRectangleCover_of_forced_points (p := p)
    (q23 := q23) (q32 := q32)
    (by simp [p])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q23] at hpRect ⊢
      omega)
    (by simp [q23])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q32] at hpRect ⊢
      omega)
    (by simp [q32])

/-- The current normalized \(5\times7\) horizontal edge-complement model has
no rectangular cover by contained source-paper \(2\times3\) and \(3\times2\)
rectangles.

This is the normalized form of
`not_normalSquareEdgeComplementRectangleCover_at_origin`.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareEdgeComplementRectangleCover_five_by_seven :
    ¬ Nonempty
      (NormalSquareEdgeComplementRectangleCover (width := 5) (height := 7) 0 0) := by
  exact not_normalSquareEdgeComplementRectangleCover_at_origin (by decide) (by decide)

/-- In the normalized horizontal-edge \(5\times7\) frame, the finite-lattice
edge-complementary block is the local \(T\)-region together with two top-collar
contiguous \(3\times2\) rectangles.

This is the concrete set identity behind the passage from the local \(T\)
picture to the \(A_3\) block in the proof of Theorem 3.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1499
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_eq_T_union_topCollar :
    (normalSquareEdgeComplementRegion (width := 5) (height := 7) 0 0) =
      (normalSquareRegionT (width := 5) (height := 7) 0 0) ∪
        squareLatticeContiguousRectangle 0 5 3 2 ∪
          (squareLatticeContiguousRectangle 2 5 3 2 :
            Finset (SquareLatticeVertex 5 7)) := by
  ext v
  simp only [Finset.mem_union, mem_normalSquareEdgeComplementRegion, mem_normalSquareRegionT,
    mem_normalSquareRegionTHole, mem_squareLatticeContiguousRectangle]
  omega

/-- A rectangular cover of the local \(T\)-region extends to a rectangular
cover of the normalized horizontal-edge \(5\times7\) complementary block by
adding the two top-collar \(3\times2\) rectangles.

**Scope restriction (T-cover):** This construction remains conditional on a
rectangular cover of the displayed local \(T\)-region. The source comparison,
the exact-cover obstruction, and the elimination plan are recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".

This is the rectangular-cover form of the top-collar decomposition of the
edge-complementary block. It separates this finite-lattice collar step from
the remaining task of constructing a rectangular cover of the local
\(T\)-region.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1499
of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def normalSquareEdgeComplementRectangleCoverOfT
    (cover : NormalSquareRegionTRectangleCover (width := 5) (height := 7) 0 0) :
    NormalSquareEdgeComplementRectangleCover (width := 5) (height := 7) 0 0 where
  Index := Sum {i // i ∈ cover.regions} (Fin 2)
  regions := Finset.univ
  nonempty := Finset.univ_nonempty
  region
    | Sum.inl i => cover.region i.1
    | Sum.inr 0 => squareLatticeContiguousRectangle 0 5 3 2
    | Sum.inr 1 => squareLatticeContiguousRectangle 2 5 3 2
  rectangular := by
    intro i _
    rcases i with i | j
    · exact cover.rectangular i.1 i.2
    · fin_cases j
      · exact Or.inr ⟨0, 5, by omega, by omega, rfl⟩
      · exact Or.inr ⟨2, 5, by omega, by omega, rfl⟩
  cover := by
    rw [normalSquareEdgeComplementRegion_eq_T_union_topCollar]
    ext v
    have hT :
        (∃ a ∈ cover.regions, v ∈ cover.region a) ↔
          v ∈ (normalSquareRegionT (width := 5) (height := 7) 0 0) := by
      constructor
      · intro hv
        rw [← cover.cover]
        exact Finset.mem_biUnion.mpr hv
      · intro hv
        have hvCover : v ∈ cover.regions.biUnion cover.region := by
          rw [cover.cover]
          exact hv
        exact Finset.mem_biUnion.mp hvCover
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨i | j, hv⟩
      · exact Or.inl (Or.inl (hT.mp ⟨i.1, i.2, hv⟩))
      · fin_cases j
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
    · rintro ((hvT | hvTopLeft) | hvTopRight)
      · rcases hT.mpr hvT with ⟨i, hi, hvi⟩
        exact ⟨Sum.inl ⟨i, hi⟩, hvi⟩
      · exact ⟨Sum.inr 0, hvTopLeft⟩
      · exact ⟨Sum.inr 1, hvTopRight⟩

/-- In the normalized vertical-edge \(7\times5\) frame, the finite-lattice
edge-complementary block is the local \(T\)-region together with two right-collar
contiguous \(2\times3\) rectangles.

This is the vertical-edge counterpart of
`normalSquareEdgeComplementRegion_eq_T_union_topCollar`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_eq_T_union_rightCollar :
    (normalSquareEdgeComplementRegion (width := 7) (height := 5) 0 0) =
      (normalSquareRegionT (width := 7) (height := 5) 0 0) ∪
        squareLatticeContiguousRectangle 5 0 2 3 ∪
          (squareLatticeContiguousRectangle 5 2 2 3 :
            Finset (SquareLatticeVertex 7 5)) := by
  ext v
  simp only [Finset.mem_union, mem_normalSquareEdgeComplementRegion, mem_normalSquareRegionT,
    mem_normalSquareRegionTHole, mem_squareLatticeContiguousRectangle]
  omega

/-- The removed blocks in the rotated local \(T\)-region for a vertical edge.

This is the \(7\times5\) counterpart of the red and blue blocks in the source
edge-blocking picture.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalRegionTHole {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle (xStart + 2) yStart 3 2 ∪
    squareLatticeContiguousRectangle (xStart + 1) (yStart + 2) 2 3

/-- The rotated local \(T\)-region used for the normalized vertical edge.

It is the complement, inside a \(6\times5\) local window, of the two blocks
adjacent to the vertical edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalRegionT {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle xStart yStart 6 5 \
    normalSquareVerticalRegionTHole xStart yStart

@[simp] theorem mem_normalSquareVerticalRegionTHole {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareVerticalRegionTHole xStart yStart ↔
      v ∈ squareLatticeContiguousRectangle (xStart + 2) yStart 3 2 ∨
        v ∈ squareLatticeContiguousRectangle (xStart + 1) (yStart + 2) 2 3 := by
  simp [normalSquareVerticalRegionTHole]

@[simp] theorem mem_normalSquareVerticalRegionT {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareVerticalRegionT xStart yStart ↔
      v ∈ squareLatticeContiguousRectangle xStart yStart 6 5 ∧
        v ∉ normalSquareVerticalRegionTHole xStart yStart := by
  simp [normalSquareVerticalRegionT]

/-- A finite rectangular cover of the rotated vertical local \(T\)-region.

This is the \(7\times5\) counterpart of `NormalSquareRegionTRectangleCover`
used for the normalized vertical-edge construction.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500
of `Papers/1804.04964/paper_normal.tex`. -/
abbrev NormalSquareVerticalRegionTRectangleCover {width height : ℕ}
    (xStart yStart : ℕ) :=
  SquareLatticeRectangleCover
    (normalSquareVerticalRegionT (width := width) (height := height) xStart yStart)

/-- The actual normalized vertical edge-complementary block.

This is the \(7\times5\) counterpart of
`normalSquareEdgeComplementRegion` for the rotated vertical edge blocking.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareVerticalEdgeComplementRegion {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  regionComplement
    (squareLatticeContiguousRectangle (xStart + 2) yStart 3 2 ∪
      (squareLatticeContiguousRectangle (xStart + 1) (yStart + 2) 2 3 :
        Finset (SquareLatticeVertex width height)))

/-- A finite rectangular cover of the actual normalized vertical
edge-complementary block.

This is the \(7\times5\) counterpart of
`NormalSquareEdgeComplementRectangleCover` for the rotated vertical edge
blocking.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500
of `Papers/1804.04964/paper_normal.tex`. -/
abbrev NormalSquareVerticalEdgeComplementRectangleCover {width height : ℕ}
    (xStart yStart : ℕ) :=
  SquareLatticeRectangleCover
    (normalSquareVerticalEdgeComplementRegion (width := width) (height := height)
      xStart yStart)

/-- The current origin-based rotated local-window model for \(T\) has no
rectangular cover by contained source-paper \(2\times3\) and
\(3\times2\) rectangles.

This is the vertical-edge counterpart of
`not_normalSquareRegionT_rectangleCover_at_origin`. It is a diagnostic
statement about the present rotated local-window model, not a claim about the
source theorem.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareVerticalRegionT_rectangleCover_at_origin {width height : ℕ}
    (hx : 6 ≤ width) (hy : 5 ≤ height) :
    ¬ Nonempty
      (NormalSquareVerticalRegionTRectangleCover (width := width) (height := height)
        0 0) := by
  let p : SquareLatticeVertex width height :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  let q23 : SquareLatticeVertex width height :=
    (⟨1, by omega⟩, ⟨2, by omega⟩)
  let q32 : SquareLatticeVertex width height :=
    (⟨2, by omega⟩, ⟨1, by omega⟩)
  exact not_squareLatticeRectangleCover_of_forced_points (p := p)
    (q23 := q23) (q32 := q32)
    (by simp [p])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q23] at hpRect ⊢
      omega)
    (by simp [q23])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q32] at hpRect ⊢
      omega)
    (by simp [q32])

/-- The current normalized \(6\times5\) rotated local-window model for \(T\)
has no rectangular cover by contained source-paper \(2\times3\) and
\(3\times2\) rectangles.

This is the normalized form of
`not_normalSquareVerticalRegionT_rectangleCover_at_origin`.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareVerticalRegionT_rectangleCover_six_by_five :
    ¬ Nonempty
      (NormalSquareVerticalRegionTRectangleCover (width := 6) (height := 5) 0 0) := by
  exact not_normalSquareVerticalRegionT_rectangleCover_at_origin (by decide) (by decide)

/-- The current origin-based vertical edge-complement model has no rectangular
cover by contained source-paper \(2\times3\) and \(3\times2\) rectangles.

This is a diagnostic statement about the present
`NormalSquareVerticalEdgeComplementRectangleCover` criterion, not a claim
about the source theorem's injectivity assertion for the vertical counterpart
of \(A_3\).

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareVerticalEdgeComplementRectangleCover_at_origin {width height : ℕ}
    (hx : 7 ≤ width) (hy : 5 ≤ height) :
    ¬ Nonempty
      (NormalSquareVerticalEdgeComplementRectangleCover
        (width := width) (height := height) 0 0) := by
  let p : SquareLatticeVertex width height := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let q23 : SquareLatticeVertex width height := (⟨1, by omega⟩, ⟨2, by omega⟩)
  let q32 : SquareLatticeVertex width height := (⟨2, by omega⟩, ⟨1, by omega⟩)
  exact not_squareLatticeRectangleCover_of_forced_points (p := p)
    (q23 := q23) (q32 := q32)
    (by simp [p, normalSquareVerticalEdgeComplementRegion])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q23] at hpRect ⊢
      omega)
    (by simp [q23, normalSquareVerticalEdgeComplementRegion])
    (by
      intro xRect yRect hpRect
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q32] at hpRect ⊢
      omega)
    (by simp [q32, normalSquareVerticalEdgeComplementRegion])

/-- The current normalized vertical edge-complement model has no rectangular
cover by contained source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the normalized form of
`not_normalSquareVerticalEdgeComplementRectangleCover_at_origin`.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1475--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareVerticalEdgeComplementRectangleCover_seven_by_five :
    ¬ Nonempty
      (NormalSquareVerticalEdgeComplementRectangleCover (width := 7) (height := 5) 0 0) := by
  exact not_normalSquareVerticalEdgeComplementRectangleCover_at_origin (by decide) (by decide)

/-- In the normalized vertical-edge \(7\times5\) frame, the complement of the
rotated red and blue edge blocks is the rotated local \(T\)-region together
with two right-collar contiguous \(2\times3\) rectangles.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalEdgeComplement_eq_verticalT_union_rightCollar :
    (normalSquareVerticalEdgeComplementRegion (width := 7) (height := 5) 0 0) =
      (normalSquareVerticalRegionT (width := 7) (height := 5) 0 0) ∪
        squareLatticeContiguousRectangle 5 0 2 3 ∪
          (squareLatticeContiguousRectangle 5 2 2 3 :
            Finset (SquareLatticeVertex 7 5)) := by
  ext v
  simp only [normalSquareVerticalEdgeComplementRegion, Finset.mem_union, mem_regionComplement,
    mem_normalSquareVerticalRegionT, mem_normalSquareVerticalRegionTHole,
    mem_squareLatticeContiguousRectangle]
  omega

/-- A rectangular cover of the rotated local \(T\)-region extends to a
rectangular cover of the normalized vertical-edge complementary block by adding
the two right-collar \(2\times3\) rectangles.

**Scope restriction (T-cover):** This construction remains conditional on a
rectangular cover of the rotated local \(T\)-region. The source comparison, the
exact-cover obstruction, and the elimination plan are recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".

This is the rotated counterpart of
`normalSquareEdgeComplementRectangleCoverOfT`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500
of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def normalSquareVerticalEdgeComplementRectangleCoverOfVerticalT
    (cover : NormalSquareVerticalRegionTRectangleCover (width := 7) (height := 5) 0 0) :
    NormalSquareVerticalEdgeComplementRectangleCover (width := 7) (height := 5) 0 0 where
  Index := Sum {i // i ∈ cover.regions} (Fin 2)
  regions := Finset.univ
  nonempty := Finset.univ_nonempty
  region
    | Sum.inl i => cover.region i.1
    | Sum.inr 0 => squareLatticeContiguousRectangle 5 0 2 3
    | Sum.inr 1 => squareLatticeContiguousRectangle 5 2 2 3
  rectangular := by
    intro i _
    rcases i with i | j
    · exact cover.rectangular i.1 i.2
    · fin_cases j
      · exact Or.inl ⟨5, 0, by omega, by omega, rfl⟩
      · exact Or.inl ⟨5, 2, by omega, by omega, rfl⟩
  cover := by
    rw [normalSquareVerticalEdgeComplement_eq_verticalT_union_rightCollar]
    ext v
    have hT :
        (∃ a ∈ cover.regions, v ∈ cover.region a) ↔
          v ∈ (normalSquareVerticalRegionT (width := 7) (height := 5) 0 0) := by
      constructor
      · intro hv
        rw [← cover.cover]
        exact Finset.mem_biUnion.mpr hv
      · intro hv
        have hvCover : v ∈ cover.regions.biUnion cover.region := by
          rw [cover.cover]
          exact hv
        exact Finset.mem_biUnion.mp hvCover
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨i | j, hv⟩
      · exact Or.inl (Or.inl (hT.mp ⟨i.1, i.2, hv⟩))
      · fin_cases j
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
    · rintro ((hvT | hvRightLower) | hvRightUpper)
      · rcases hT.mpr hvT with ⟨i, hi, hvi⟩
        exact ⟨Sum.inl ⟨i, hi⟩, hvi⟩
      · exact ⟨Sum.inr 0, hvRightLower⟩
      · exact ⟨Sum.inr 1, hvRightUpper⟩

namespace NormalSquareLatticeRectangleInjectivityHypotheses

variable {width height : ℕ}
variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-- A square-lattice region is injective once it is covered by source-paper
\(2\times3\) and \(3\times2\) rectangles.

This is the common conditional step for the local \(T\)-region and for the
edge-complementary block \(A_3\). It states that rectangular injectivity plus
the union-of-injective-regions lemma proves injectivity once the coordinate
cover is supplied.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem injective_of_rectangleCover
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {target : Finset (SquareLatticeVertex width height)}
    (cover : SquareLatticeRectangleCover target) :
    κ.IsInjective target := by
  rw [← cover.cover]
  exact hUnion.biUnion_injective cover.nonempty cover.region fun i hi ↦ by
    rcases cover.rectangular i hi with hRect | hRect
    · exact h.twoByThree_injective _ hRect
    · exact h.threeByTwo_injective _ hRect

/-- The displayed local \(T\)-region is injective once it is covered by
source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the formal conditional step for the source sentence that \(T\) is
injective when the PEPS is large enough. It does not construct the cover; it
states that rectangular injectivity plus the union-of-injective-regions lemma
proves injectivity once the coordinate cover is supplied.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionT_injective_of_cover
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ}
    (cover : NormalSquareRegionTRectangleCover (width := width) (height := height)
      xStart yStart) :
    κ.IsInjective (normalSquareRegionT xStart yStart) :=
  h.injective_of_rectangleCover hUnion cover

/-- The rotated vertical local \(T\)-region is injective once it is covered by
source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the vertical counterpart of `regionT_injective_of_cover`. It does not
construct the cover; it records the conditional passage from a source-sized
rectangular cover to injectivity.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem verticalT_inj_of_cover
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ}
    (cover : NormalSquareVerticalRegionTRectangleCover
      (width := width) (height := height) xStart yStart) :
    κ.IsInjective (normalSquareVerticalRegionT xStart yStart) :=
  h.injective_of_rectangleCover hUnion cover

/-- The finite-lattice edge-complementary block is injective once it is covered
by source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the formal conditional step for the block denoted \(A_3\) in the proof
of Theorem 3. It does not construct the cover; it states that rectangular
injectivity plus the union-of-injective-regions lemma proves injectivity after
the coordinate cover is supplied.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem edgeComplement_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ}
    (cover : NormalSquareEdgeComplementRectangleCover (width := width) (height := height)
      xStart yStart) :
    κ.IsInjective (normalSquareEdgeComplementRegion xStart yStart) :=
  h.injective_of_rectangleCover hUnion cover

/-- The vertical finite-lattice edge-complementary block is injective once it
is covered by source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the rotated counterpart of `edgeComplement_injective`.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem verticalEdgeComplement_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ}
    (cover : NormalSquareVerticalEdgeComplementRectangleCover
      (width := width) (height := height) xStart yStart) :
    κ.IsInjective (normalSquareVerticalEdgeComplementRegion xStart yStart) :=
  h.injective_of_rectangleCover hUnion cover

/-- In the normalized horizontal-edge \(5\times7\) frame, a rectangular cover
of the local \(T\)-region proves injectivity of the edge-complementary block.

The proof first adjoins the two top-collar rectangles to the \(T\)-cover, then
applies the general rectangular-cover criterion.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem edgeComplement_injective_of_T_cover
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (cover : NormalSquareRegionTRectangleCover (width := 5) (height := 7) 0 0) :
    κ.IsInjective (normalSquareEdgeComplementRegion (width := 5) (height := 7) 0 0) :=
  h.edgeComplement_injective hUnion (normalSquareEdgeComplementRectangleCoverOfT cover)

/-- In the normalized horizontal-edge \(5\times7\) frame, the edge-complementary
block is injective if the local \(T\)-region is injective.

The two additional top-collar regions are contiguous \(3\times2\) rectangles,
so rectangular injectivity and the union-of-injective-regions lemma add them to
the local \(T\)-region.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem topCollar_injective
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareRegionT (width := 5) (height := 7) 0 0)) :
    κ.IsInjective (normalSquareEdgeComplementRegion (width := 5) (height := 7) 0 0) := by
  rw [normalSquareEdgeComplementRegion_eq_T_union_topCollar]
  exact hUnion.union_injective
    (hUnion.union_injective hT (h.rect32_injective (by omega) (by omega)))
    (h.rect32_injective (by omega) (by omega))

/-- In a \(7\times5\) ambient rectangle, the horizontal-frame
edge-complementary block is injective if the horizontal local \(T\)-region is
injective.

The two additional right-collar regions are contiguous \(2\times3\) rectangles,
so rectangular injectivity and the union-of-injective-regions lemma add them to
the local \(T\)-region.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem rightCollar_injective
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareRegionT (width := 7) (height := 5) 0 0)) :
    κ.IsInjective (normalSquareEdgeComplementRegion (width := 7) (height := 5) 0 0) := by
  rw [normalSquareEdgeComplementRegion_eq_T_union_rightCollar]
  exact hUnion.union_injective
    (hUnion.union_injective hT (h.rect23_injective (by omega) (by omega)))
    (h.rect23_injective (by omega) (by omega))

/-- In the normalized vertical-edge \(7\times5\) frame, the actual complement
of the rotated red and blue edge blocks is injective if the rotated local
\(T\)-region is injective.

The two additional right-collar regions are contiguous \(2\times3\)
rectangles.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem verticalComp_injective
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareVerticalRegionT (width := 7) (height := 5) 0 0)) :
    κ.IsInjective
      (normalSquareVerticalEdgeComplementRegion (width := 7) (height := 5) 0 0) := by
  rw [normalSquareVerticalEdgeComplement_eq_verticalT_union_rightCollar]
  exact hUnion.union_injective
    (hUnion.union_injective hT (h.rect23_injective (by omega) (by omega)))
    (h.rect23_injective (by omega) (by omega))

/-- In the normalized vertical-edge \(7\times5\) frame, a rectangular cover of
the rotated local \(T\)-region implies injectivity of the actual complement of
the rotated red and blue edge blocks.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem verticalComp_inj_of_cover
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (cover : NormalSquareVerticalRegionTRectangleCover
      (width := 7) (height := 5) 0 0) :
    κ.IsInjective
      (normalSquareVerticalEdgeComplementRegion (width := 7) (height := 5) 0 0) :=
  h.verticalEdgeComplement_injective hUnion
    (normalSquareVerticalEdgeComplementRectangleCoverOfVerticalT cover)

end NormalSquareLatticeRectangleInjectivityHypotheses

/-- Rectangular injectivity, union closure, and a rectangular cover of the
displayed \(T\)-region supply the abstract square-lattice blocking-region
structure.

**Scope restriction (T-cover):** This conditional result assumes a
rectangular cover of the displayed \(T\)-region at the origin. The source
comparison, the exact-cover obstruction, and the elimination plan are recorded
in `docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining
mathematical obligations".

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareBlockingRegions_of_TCover {width height : ℕ}
    {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hWidth : 7 ≤ width) (hHeight : 7 ≤ height)
    (cover : NormalSquareRegionTRectangleCover (width := width) (height := height)
      0 0) :
    NormalSquareBlockingRegions κ where
  width := width
  height := height
  seven_le_width := hWidth
  seven_le_height := hHeight
  card_eq_width_mul_height := by
    simp [SquareLatticeVertex]
  rectangles := h.toRectangular
  regionR := normalSquareRegionR 0 0
  regionS := normalSquareRegionS 0 0
  regionT := normalSquareRegionT 0 0
  regionR_injective := h.regionR_injective_of_union hUnion (by omega) (by omega)
  regionS_injective := h.regionS_injective_of_union hUnion (by omega) (by omega)
  regionT_injective := h.regionT_injective_of_cover hUnion cover

end PEPS
end TNLean
