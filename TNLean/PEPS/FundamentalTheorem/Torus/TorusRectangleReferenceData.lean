/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Torus.TorusEdgeBlockingCrossing
import TNLean.PEPS.Injectivity.Region.NormalEdgeBlockingData
import TNLean.PEPS.Graph.Torus.TorusLatticeGraph
import TNLean.PEPS.FundamentalTheorem.Normal.NormalEdgeGaugeFamily

/-!
# The faithful torus reference blocking datum from rectangle injectivity

For a torus tensor whose contiguous $2\times3$ and $3\times2$ blocks are injective (the source's own
blocking hypotheses) and whose region injectivity is union closed, the distinguished horizontal and
vertical reference edges carry a one-edge blocking datum: the red block is the removed source
rectangle, the blue block is the other removed source rectangle, and the complementary block is the
union of four surrounding bands and two fillers.  All three are injective by rectangular injectivity
and the union-of-injective-regions lemma, they partition the torus, and their single red-to-blue
crossing is the reference edge.

This is the source-faithful reference blocking datum the translation-invariant gauge family
consumes: the injectivity inputs are exactly the source's
rectangular-injectivity hypotheses, with no single-vertex injectivity.  The reference edge keeps a
margin of at least two columns and rows below and to the left, while above and to the right the
blocking either touches the seam or keeps a margin of at least two; the seam-touching anchor
`(width - 5, height - 5)` realizes the blocking on every torus with the source's sizes
`n, m ≥ 7` (arXiv:1804.04964, Theorem 3).

It also contains the following results.

* `TNLean.PEPS.exists_regionEdgeGauge_torus`, `TNLean.PEPS.exists_regionEdgeGauge_torus_coeff`: the
  per-edge gauge at a torus edge from one-edge blocking data.
* `TNLean.PEPS.exists_horizontalReferenceEdgeGauge_coeff`,
  `TNLean.PEPS.exists_verticalReferenceEdgeGauge_coeff`: the per-edge gauge at the torus reference
  edges from rectangle injectivity.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open ManyBody (Edge)

section TorusRectangleReferenceData

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### The faithful horizontal reference blocking datum -/

/-- **Faithful horizontal reference blocking datum on the torus.**

For a torus tensor `A` whose region-injectivity predicate satisfies the rectangular-injectivity
hypotheses and union closure, the distinguished horizontal reference edge carries the one-edge
blocking datum whose red block is the removed vertical edge block, blue block the removed horizontal
edge block, and complementary block the rest of the torus.  All three are injective by rectangular
injectivity and the union-of-injective-regions lemma; they partition the torus; the edge's left
endpoint lies in red and its right endpoint in blue.

The offset `(xStart, yStart)` must keep at least two columns and one row of margin below and to
the left, while above and to the right the removed blocks either touch the seam
(`xStart + 5 = width`, `yStart + 5 = height`) or keep a margin of at least two.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusHorizontalRectangleBlockingDatum
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    NormalEdgeBlockingData κ (torusGraph width height)
      (torusHorizontalReferenceEdge xStart yStart) where
  red := torusHorizontalEdgeRed xStart yStart
  blue := torusHorizontalEdgeBlue xStart yStart
  complement := torusHorizontalEdgeComplement xStart yStart
  left_mem_red := by
    obtain ⟨hr11, hr12, _, _⟩ :=
      horizontalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusHorizontalEdgeRed]; omega
  right_mem_blue := by
    obtain ⟨_, _, hr21, hr22⟩ :=
      horizontalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusHorizontalEdgeBlue]; omega
  red_injective := h.horizontalEdgeRed_injective (by omega) (by omega)
  blue_injective := h.horizontalEdgeBlue_injective (by omega) (by omega)
  complement_injective := h.horizontalEdgeComplement_injective hUnion hx0 hy0 hxw hyh
  red_disjoint_blue := torusHorizontalEdgeRed_disjoint_blue xStart yStart
  red_disjoint_complement := torusHorizontalEdgeRed_disjoint_complement xStart yStart
  blue_disjoint_complement := torusHorizontalEdgeBlue_disjoint_complement xStart yStart
  cover_univ := torusHorizontalEdge_cover_univ xStart yStart

@[simp] theorem torusHorizontalRectangleBlockingDatum_red
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).red =
      torusHorizontalEdgeRed xStart yStart := rfl

@[simp] theorem torusHorizontalRectangleBlockingDatum_blue
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).blue =
      torusHorizontalEdgeBlue xStart yStart := rfl

/-- The red-to-blue crossings of the faithful horizontal reference datum are exactly the
distinguished horizontal reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusHorizontalRectangleBlockingDatum
    (A : Tensor (torusGraph width height) d)
    {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUnion : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).red
        (torusHorizontalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).blue g ↔
      g = torusHorizontalReferenceEdge xStart yStart := by
  rw [torusHorizontalRectangleBlockingDatum_red, torusHorizontalRectangleBlockingDatum_blue]
  exact isCrossingEdge_torusHorizontalEdge A (by omega) (by omega) (by omega) g

/-! ### The faithful vertical reference blocking datum -/

/-- **Faithful vertical reference blocking datum on the torus.**

The vertical counterpart of `torusHorizontalRectangleBlockingDatum` at the distinguished vertical
reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def torusVerticalRectangleBlockingDatum
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 1 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    NormalEdgeBlockingData κ (torusGraph width height)
      (torusVerticalReferenceEdge xStart yStart) where
  red := torusVerticalEdgeRed xStart yStart
  blue := torusVerticalEdgeBlue xStart yStart
  complement := torusVerticalEdgeComplement xStart yStart
  left_mem_red := by
    obtain ⟨hr11, hr12, _, _⟩ :=
      verticalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusVerticalEdgeRed]; omega
  right_mem_blue := by
    obtain ⟨_, _, hr21, hr22⟩ :=
      verticalReferenceEdge_val (width := width) (height := height)
        (xStart := xStart) (yStart := yStart) (by omega) (by omega)
    rw [mem_torusVerticalEdgeBlue]; omega
  red_injective := h.verticalEdgeRed_injective (by omega) (by omega)
  blue_injective := h.verticalEdgeBlue_injective (by omega) (by omega)
  complement_injective := h.verticalEdgeComplement_injective hUnion hx0 hy0 hxw hyh
  red_disjoint_blue := torusVerticalEdgeRed_disjoint_blue xStart yStart
  red_disjoint_complement := torusVerticalEdgeRed_disjoint_complement xStart yStart
  blue_disjoint_complement := torusVerticalEdgeBlue_disjoint_complement xStart yStart
  cover_univ := torusVerticalEdge_cover_univ xStart yStart

@[simp] theorem torusVerticalRectangleBlockingDatum_red
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 1 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).red =
      torusVerticalEdgeRed xStart yStart := rfl

@[simp] theorem torusVerticalRectangleBlockingDatum_blue
    {κ : RegionInjectivityData (TorusVertex width height)} {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx0 : 1 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height) :
    (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).blue =
      torusVerticalEdgeBlue xStart yStart := rfl

/-- The red-to-blue crossings of the faithful vertical reference datum are exactly the
distinguished vertical reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusVerticalRectangleBlockingDatum
    (A : Tensor (torusGraph width height) d)
    {xStart yStart : ℕ}
    (h : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUnion : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hx0 : 1 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).red
        (torusVerticalRectangleBlockingDatum h hUnion hx0 hy0 hxw hyh).blue g ↔
      g = torusVerticalReferenceEdge xStart yStart := by
  rw [torusVerticalRectangleBlockingDatum_red, torusVerticalRectangleBlockingDatum_blue]
  exact isCrossingEdge_torusVerticalEdge A (by omega) (by omega) (by omega) g

end PEPS
end TNLean

end TorusRectangleReferenceData

section TorusEdgeGauge

/-!
## The per-edge gauge at a torus edge from one-edge blocking data

Two normal PEPS on the discrete torus, related by `SameState` and matched bond dimensions, with
one-edge blocking data sharing the three blocks at an edge `e` and the single red-to-blue
crossing, have on `e` the per-edge gauge: the bond dimensions coincide and the forward
region-insertion transfer is conjugation by an invertible matrix
(`exists_regionEdgeGauge_torus`).  This is the graph-polymorphic coherent-frame gauge interface
`exists_regionEdgeGauge_of_blockingData` specialized to the torus; the torus carries the
required `Fintype`, `LinearOrder`, and `DecidableRel` instances, so the interface applies
verbatim.

The reference datum at each orientation class's distinguished edge is built directly from the
rectangular injectivity hypotheses (`TNLean/PEPS/TorusRectangleReferenceData.lean`), so this
gauge is available at every edge.

### References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines
  254--586 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The per-edge gauge at a torus edge.**

Two normal PEPS `A` and `B` on the torus with one-edge blocking data `DA`, `DB` sharing the
three blocks at `e`, matched bond dimensions, the same state, positive bonds, the single
red-to-blue crossing on `e`, and `B`'s red and host injectivities, have the per-edge gauge on
`e`: the bond dimensions of `A` and `B` on `e` coincide and the forward region-insertion
transfer is conjugation by an invertible gauge matrix `Z`.

This is `exists_regionEdgeGauge_of_blockingData` (the coherent-frame interface, stated over a
general `Fintype`/`LinearOrder` vertex set) specialized to the torus; no single-vertex
injectivity is used.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_torus
    {A B : Tensor (torusGraph width height) d} {e : Edge (torusGraph width height)}
    (DA : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e)
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) B)
      (torusGraph width height) e)
    (hred : DA.red = DB.red) (hblue : DA.blue = DB.blue)
    (hcompl : DA.complement = DB.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hsingle : ∀ g : Edge (torusGraph width height),
      IsCrossingEdge (G := torusGraph width height) A DA.red DA.blue g ↔ g = e)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red)
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ DA.red)) :
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ)
        (fwd : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ),
        ∀ M, fwd M =
            (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  obtain ⟨_, _, _, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData DA DB hred hblue hcompl hbond hAB hd hposA hposB
      hsingle hRB hCB
  exact ⟨hEdge, Z, _, hZ⟩

/-- **The per-edge gauge at a torus edge, with its coefficient identity.**

The same conclusion as `exists_regionEdgeGauge_torus`, but exposing the region-insertion
coefficient identity that the gauge conjugation realizes: on the single boundary edge
`f = ⟨e, _⟩` of the red block, inserting `M` into `A` and contracting matches inserting the
gauge conjugation `Z · (reindex M) · Z⁻¹` into `B`.  This is the defining identity of the
forward region-insertion transfer (`RegionInsertionTransfer.fwd_coeff`), specialized through
`Z`'s realization of that transfer.

The coefficient identity is the load-bearing extra output over `exists_regionEdgeGauge_torus`:
together with the determinacy of the region-insertion transfer map
(`regionInsertedCoeff_transferMap_unique`), it turns the geometric covariance of the per-edge
transfer maps under translation into the conjugation covariance the orientation-uniform
selection consumes.

No single-vertex injectivity is used; the injectivity inputs are the blocked-region
injectivities of the data and `B`'s red and host injectivities.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_torus_coeff
    {A B : Tensor (torusGraph width height) d} {e : Edge (torusGraph width height)}
    (DA : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e)
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) B)
      (torusGraph width height) e)
    (hred : DA.red = DB.red) (hblue : DA.blue = DB.blue)
    (hcompl : DA.complement = DB.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hsingle : ∀ g : Edge (torusGraph width height),
      IsCrossingEdge (G := torusGraph width height) A DA.red DA.blue g ↔ g = e)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red)
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ DA.red)) :
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ),
        ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
          (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) DA.red)
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \ DA.red)),
          regionInsertedCoeff (G := torusGraph width height) A DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e hsingle) M
              σ τ =
            regionInsertedCoeff (G := torusGraph width height) B DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e hsingle)
              ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
                  Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                  ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))
              σ τ := by
  obtain ⟨htransferAB, htransferBA, hmul, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData DA DB hred hblue hcompl hbond hAB hd hposA hposB
      hsingle hRB hCB
  refine ⟨hEdge, Z, fun M σ τ => ?_⟩
  -- The forward transfer of the region-insertion datum realizes the conjugation `conj_Z`
  -- (`hZ`) and satisfies the coefficient identity (`fwd_coeff`); rewriting along `hZ` gives the
  -- coefficient identity for the conjugation map.
  have hfwd := (regionInsertionTransfer_of_coeffTransfer A B DA.red
    (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e hsingle)
    hRB hCB hAB hposB hbond htransferAB htransferBA hmul).fwd_coeff M σ τ
  rw [hZ M] at hfwd
  exact hfwd

end PEPS
end TNLean

end TorusEdgeGauge

section TorusRectangleGauge

/-!
## The per-edge gauge at the torus reference edges from rectangle injectivity

Two normal PEPS on the discrete torus, related by `SameState` with matched bond dimensions and both
satisfying the rectangular-injectivity hypotheses with union closure, carry on the distinguished
horizontal and vertical reference edges the per-edge gauge of the edge blocking: the bond
dimensions coincide and the forward region-insertion transfer is conjugation by an invertible
matrix, together with the region-insertion coefficient identity the conjugation realizes.

This is `exists_regionEdgeGauge_torus_coeff` fed the faithful rectangle-injectivity reference datum
of `TNLean/PEPS/TorusRectangleReferenceData.lean`, in place of the vertex-injective singleton
datum.  The injectivity inputs are the rectangular-injectivity hypotheses for both tensors plus
union closure for the second tensor's host block; no single-vertex injectivity is used.

### References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The per-edge gauge at the torus horizontal reference edge from rectangle injectivity.**

For two torus tensors `A`, `B` with the same state, matched bond dimensions, positive bonds, and
both satisfying the rectangular-injectivity hypotheses with union closure, the distinguished
horizontal reference edge carries the per-edge gauge: the bond dimensions coincide and the forward
region-insertion transfer is conjugation by an invertible gauge matrix, realizing the
region-insertion coefficient identity.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_horizontalReferenceEdgeGauge_coeff
    {A B : Tensor (torusGraph width height) d} {xStart yStart : ℕ}
    (hA : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    let e := torusHorizontalReferenceEdge xStart yStart
    let DA := torusHorizontalRectangleBlockingDatum hA hUA hx0 hy0 hxw hyh
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ),
        ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
          (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) DA.red)
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \ DA.red)),
          regionInsertedCoeff (G := torusGraph width height) A DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e
                (fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hA hUA hx0 hy0
                  hxw hyh g)) M σ τ =
            regionInsertedCoeff (G := torusGraph width height) B DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e
                (fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hA hUA hx0 hy0
                  hxw hyh g))
              ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
                  Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                  ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))
              σ τ := by
  intro e DA
  -- The datum for `B` over the same regions.
  let DB := torusHorizontalRectangleBlockingDatum hB hUB hx0 hy0 hxw hyh
  -- The two data share the three regions, since the regions are tensor independent.
  have hsingle := fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hA hUA hx0 hy0
    hxw hyh g
  -- `B`'s red and host blocks are blocked-tensor injective.
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red :=
    hB.horizontalEdgeRed_injective (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
  have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ DA.red) :=
    regionBlockedTensorInjective_host DB hUB
  exact exists_regionEdgeGauge_torus_coeff DA DB rfl rfl rfl hbond hAB hd hposA hposB hsingle
    hRB hCB

/-- **The per-edge gauge at the torus vertical reference edge from rectangle injectivity.**

The vertical counterpart of `exists_horizontalReferenceEdgeGauge_coeff`: for two torus tensors `A`,
`B` with the same state, matched bond dimensions, positive bonds, and both satisfying the
rectangular-injectivity hypotheses with union closure, the distinguished vertical reference edge
carries the per-edge gauge realizing the region-insertion coefficient identity.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_verticalReferenceEdgeGauge_coeff
    {A B : Tensor (torusGraph width height) d} {xStart yStart : ℕ}
    (hA : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hx0 : 1 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 = width ∨ xStart + 7 ≤ width)
    (hyh : yStart + 5 = height ∨ yStart + 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    let e := torusVerticalReferenceEdge xStart yStart
    let DA := torusVerticalRectangleBlockingDatum hA hUA hx0 hy0 hxw hyh
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ),
        ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
          (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) DA.red)
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \ DA.red)),
          regionInsertedCoeff (G := torusGraph width height) A DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e
                (fun g => isCrossingEdge_torusVerticalRectangleBlockingDatum A hA hUA hx0 hy0
                  hxw hyh g)) M σ τ =
            regionInsertedCoeff (G := torusGraph width height) B DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e
                (fun g => isCrossingEdge_torusVerticalRectangleBlockingDatum A hA hUA hx0 hy0
                  hxw hyh g))
              ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
                  Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                  ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))
              σ τ := by
  intro e DA
  let DB := torusVerticalRectangleBlockingDatum hB hUB hx0 hy0 hxw hyh
  have hsingle := fun g => isCrossingEdge_torusVerticalRectangleBlockingDatum A hA hUA hx0 hy0
    hxw hyh g
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red :=
    hB.verticalEdgeRed_injective (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
  have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ DA.red) :=
    regionBlockedTensorInjective_host DB hUB
  exact exists_regionEdgeGauge_torus_coeff DA DB rfl rfl rfl hbond hAB hd hposA hposB hsingle
    hRB hCB

end PEPS
end TNLean

end TorusRectangleGauge
