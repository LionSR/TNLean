/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Normal.NormalEdgeGaugeFamily
import TNLean.PEPS.FundamentalTheorem.Normal.RegionInsertion.ProportionalityFromAbsorbed

/-!
# The per-edge coefficient identity and absorbing gauge at interior square-lattice edges

This file upgrades the per-edge gauge of the open square lattice
(`exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge` and its vertical counterpart) to
the two stronger per-edge outputs the torus assembly consumes:

* the **coefficient-identity form** (the analogue of `exists_regionEdgeGauge_torus_coeff`): on
  the distinguished edge of a translated interior blocking frame, the bond dimensions of the two
  tensors coincide and an invertible gauge `Z` realizes the conjugation-form region-insertion
  coefficient identity at the red block;
* the **absorbing-gauge form**: an invertible matrix `Ze` on the distinguished edge such that any
  per-edge gauge family taking the value `Ze` there satisfies the bare-edge absorbed equality at
  that edge --- inserting `N` on the first tensor's edge matches inserting the reindexed `N` on
  the gauge-absorbed second tensor's edge, for every global physical configuration.

The conversion from the coefficient identity to the bare-edge absorbed equality is the
graph-generic `edgeAbsorbed_of_conjIdentity`; the gauge engine is the graph-generic coherent
frame interface `exists_regionEdgeGauge_of_blockingData` fed the cover-free interior blocking
data.  No single-vertex injectivity is used anywhere: the injectivity inputs are the rectangular
injectivity hypotheses of the two tensors and union closure.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`, where Lemma `inj_isomorph` is applied around every lattice
edge and the resulting gauges are incorporated into the second tensor.

It also contains the following results.

* `TNLean.PEPS.exists_absorbingGauge_of_normalSquareInteriorEdgeDatum`,
  `TNLean.PEPS.exists_normalSquareInteriorAbsorbedGaugeFamily`: the interior absorbed gauge family
  on the open square lattice.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

section NormalSquareEdgeCoeff

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph)

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ}

open scoped Classical in
/-- **The per-edge gauge at a translated horizontal interior edge, with its coefficient
identity.**

The same inputs as `exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge`, but exposing
the region-insertion coefficient identity the gauge conjugation realizes: on the single boundary
edge of the red block of the translated horizontal interior frame, inserting `M` into `A` and
contracting matches inserting the gauge conjugation `Z · (reindex M) · Z⁻¹` into `B`.  This is
the square-lattice analogue of `exists_regionEdgeGauge_torus_coeff`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph` applied at a horizontal lattice edge,
lines 1449--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge_coeff
    (A B : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g) :
    let e := normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega)
    let hsingle := fun g => isCrossingEdge_normalSquareHorizontalTranslatedEdge
      (width := width) (height := height) A (xStart := xStart) (yStart := yStart)
      (by omega) (by omega) g
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ),
        ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
          (σ : RegionPhysicalConfig (V := SquareLatticeVertex width height) (d := d)
            (normalSquareHorizontalTranslatedEdgeRed xStart yStart))
          (τ : RegionPhysicalConfig (V := SquareLatticeVertex width height) (d := d)
            (Finset.univ \ normalSquareHorizontalTranslatedEdgeRed xStart yStart)),
          regionInsertedCoeff (G := squareLatticeGraph width height) A
              (normalSquareHorizontalTranslatedEdgeRed xStart yStart)
              (singleBoundaryEdge (G := squareLatticeGraph width height) A
                (normalSquareHorizontalTranslatedEdgeRed xStart yStart)
                (normalSquareHorizontalTranslatedEdgeBlue xStart yStart) e hsingle) M σ τ =
            regionInsertedCoeff (G := squareLatticeGraph width height) B
              (normalSquareHorizontalTranslatedEdgeRed xStart yStart)
              (singleBoundaryEdge (G := squareLatticeGraph width height) A
                (normalSquareHorizontalTranslatedEdgeRed xStart yStart)
                (normalSquareHorizontalTranslatedEdgeBlue xStart yStart) e hsingle)
              ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
                  Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                  ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))
              σ τ := by
  have hUA := regionInjectivityUnionClosure_of_overlap A hposA
  have hUB := regionInjectivityUnionClosure_of_overlap B hposB
  intro e hsingle
  let DA := normalSquareHorizontalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf A) hA hUA hx0 hy0 hxw hyh
  let DB := normalSquareHorizontalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf B) hB hUB hx0 hy0 hxw hyh
  have hred : DA.red = DB.red := rfl
  have hblue : DA.blue = DB.blue := rfl
  have hcompl : DA.complement = DB.complement := rfl
  have hRB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B DA.red :=
    regionBlockedTensorInjective_red DB
  have hCB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (Finset.univ \ DA.red) := regionBlockedTensorInjective_host DB hUB
  obtain ⟨htransferAB, htransferBA, hmul, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData (A := A) (B := B) (e := e) DA DB
      hred hblue hcompl hbond hAB hd hposA hposB hsingle hRB hCB
  refine ⟨hEdge, Z, fun M σ τ => ?_⟩
  have hfwd := (regionInsertionTransfer_of_coeffTransfer A B DA.red
    (singleBoundaryEdge (G := squareLatticeGraph width height) A DA.red DA.blue e hsingle)
    hRB hCB hAB hposB hbond htransferAB htransferBA hmul).fwd_coeff M σ τ
  rw [hZ M] at hfwd
  exact hfwd

open scoped Classical in
/-- **The per-edge gauge at a translated vertical interior edge, with its coefficient
identity.**

The rotated counterpart of
`exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge_coeff`: on the single boundary edge
of the red block of the translated vertical interior frame, an invertible gauge `Z` realizes the
conjugation-form region-insertion coefficient identity.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph` applied at a vertical lattice edge,
lines 1449--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_normalSquareVerticalTranslatedEdge_coeff
    (A B : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g) :
    let e := normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega)
    let hsingle := fun g => isCrossingEdge_normalSquareVerticalTranslatedEdge
      (width := width) (height := height) A (xStart := xStart) (yStart := yStart)
      (by omega) (by omega) g
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ),
        ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
          (σ : RegionPhysicalConfig (V := SquareLatticeVertex width height) (d := d)
            (normalSquareVerticalTranslatedEdgeRed xStart yStart))
          (τ : RegionPhysicalConfig (V := SquareLatticeVertex width height) (d := d)
            (Finset.univ \ normalSquareVerticalTranslatedEdgeRed xStart yStart)),
          regionInsertedCoeff (G := squareLatticeGraph width height) A
              (normalSquareVerticalTranslatedEdgeRed xStart yStart)
              (singleBoundaryEdge (G := squareLatticeGraph width height) A
                (normalSquareVerticalTranslatedEdgeRed xStart yStart)
                (normalSquareVerticalTranslatedEdgeBlue xStart yStart) e hsingle) M σ τ =
            regionInsertedCoeff (G := squareLatticeGraph width height) B
              (normalSquareVerticalTranslatedEdgeRed xStart yStart)
              (singleBoundaryEdge (G := squareLatticeGraph width height) A
                (normalSquareVerticalTranslatedEdgeRed xStart yStart)
                (normalSquareVerticalTranslatedEdgeBlue xStart yStart) e hsingle)
              ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
                  Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                  ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))
              σ τ := by
  have hUA := regionInjectivityUnionClosure_of_overlap A hposA
  have hUB := regionInjectivityUnionClosure_of_overlap B hposB
  intro e hsingle
  let DA := normalSquareVerticalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf A) hA hUA hx0 hy0 hxw hyh
  let DB := normalSquareVerticalTranslatedEdge_blockingDatum_interior
      (κ := regionInjectivityDataOf B) hB hUB hx0 hy0 hxw hyh
  have hred : DA.red = DB.red := rfl
  have hblue : DA.blue = DB.blue := rfl
  have hcompl : DA.complement = DB.complement := rfl
  have hRB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B DA.red :=
    regionBlockedTensorInjective_red DB
  have hCB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (Finset.univ \ DA.red) := regionBlockedTensorInjective_host DB hUB
  obtain ⟨htransferAB, htransferBA, hmul, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData (A := A) (B := B) (e := e) DA DB
      hred hblue hcompl hbond hAB hd hposA hposB hsingle hRB hCB
  refine ⟨hEdge, Z, fun M σ τ => ?_⟩
  have hfwd := (regionInsertionTransfer_of_coeffTransfer A B DA.red
    (singleBoundaryEdge (G := squareLatticeGraph width height) A DA.red DA.blue e hsingle)
    hRB hCB hAB hposB hbond htransferAB htransferBA hmul).fwd_coeff M σ τ
  rw [hZ M] at hfwd
  exact hfwd

/-! ### The absorbing gauge at an interior edge

Feeding the coefficient identity to the graph-generic conversion
`edgeAbsorbed_of_conjIdentity` yields, at each translated interior edge, an invertible matrix
whose placement in any per-edge gauge family realizes the bare-edge absorbed equality at that
edge.  Because the bare-edge identity at an edge depends only on the family's value there, the
absorbing gauges of distinct edges can be assembled into one family edge by edge. -/

open scoped Classical in
/-- **The absorbing gauge at a translated horizontal interior edge.**

There is an invertible matrix `Ze` on the distinguished horizontal edge of the translated
interior frame such that every per-edge gauge family `X` with `X e = Ze` satisfies the bare-edge
absorbed equality at `e` against `applyGauge B X`: inserting `N` on `A`'s edge `e` matches
inserting the reindexed `N` on `applyGauge B X`'s edge `e`, for every global physical
configuration.

`Ze` is the orientation-adapted absorbing gauge of the per-edge engine gauge at `e`
(`absorbedBoundaryGauge`); the conversion is `edgeAbsorbed_of_conjIdentity` fed the coefficient
identity of `exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge_coeff`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_absorbingGauge_normalSquareHorizontalTranslatedEdge
    (A B : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g) :
    let e := normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega)
    ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
      ∀ X : (g : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim g)) ℂ,
        X e = Ze →
        ∀ (σ : SquareLatticeVertex width height → Fin d)
          (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
            edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  intro e
  obtain ⟨hEdge, Z, hid⟩ :=
    exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge_coeff A B hA hB
      hx0 hy0 hxw hyh hbond hAB hd hposA hposB
  have hEeq : hEdge = congr_fun hbond e := Subsingleton.elim _ _
  subst hEeq
  set f := singleBoundaryEdge (G := squareLatticeGraph width height) A
    (normalSquareHorizontalTranslatedEdgeRed xStart yStart)
    (normalSquareHorizontalTranslatedEdgeBlue xStart yStart) e
    (fun g => isCrossingEdge_normalSquareHorizontalTranslatedEdge
      (width := width) (height := height) A (xStart := xStart) (yStart := yStart)
      (by omega) (by omega) g) with hfdef
  refine ⟨absorbedBoundaryGauge (G := squareLatticeGraph width height) B
    (normalSquareHorizontalTranslatedEdgeRed xStart yStart) f Z, fun X hXe σ N => ?_⟩
  exact edgeAbsorbed_of_conjIdentity A B
    (normalSquareHorizontalTranslatedEdgeRed xStart yStart) f hbond Z X hXe hposA
    (fun M σ' τ' => hid M σ' τ') σ N

open scoped Classical in
/-- **The absorbing gauge at a translated vertical interior edge.**

The rotated counterpart of `exists_absorbingGauge_normalSquareHorizontalTranslatedEdge`: an
invertible matrix `Ze` on the distinguished vertical edge of the translated interior frame such
that every per-edge gauge family taking the value `Ze` there satisfies the bare-edge absorbed
equality at that edge against the gauge-absorbed second tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_absorbingGauge_normalSquareVerticalTranslatedEdge
    (A B : Tensor (squareLatticeGraph width height) d) {xStart yStart : ℕ}
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 8 ≤ width) (hyh : yStart + 8 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g) :
    let e := normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega)
    ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
      ∀ X : (g : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim g)) ℂ,
        X e = Ze →
        ∀ (σ : SquareLatticeVertex width height → Fin d)
          (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
            edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  intro e
  obtain ⟨hEdge, Z, hid⟩ :=
    exists_regionEdgeGauge_normalSquareVerticalTranslatedEdge_coeff A B hA hB
      hx0 hy0 hxw hyh hbond hAB hd hposA hposB
  have hEeq : hEdge = congr_fun hbond e := Subsingleton.elim _ _
  subst hEeq
  set f := singleBoundaryEdge (G := squareLatticeGraph width height) A
    (normalSquareVerticalTranslatedEdgeRed xStart yStart)
    (normalSquareVerticalTranslatedEdgeBlue xStart yStart) e
    (fun g => isCrossingEdge_normalSquareVerticalTranslatedEdge
      (width := width) (height := height) A (xStart := xStart) (yStart := yStart)
      (by omega) (by omega) g) with hfdef
  refine ⟨absorbedBoundaryGauge (G := squareLatticeGraph width height) B
    (normalSquareVerticalTranslatedEdgeRed xStart yStart) f Z, fun X hXe σ N => ?_⟩
  exact edgeAbsorbed_of_conjIdentity A B
    (normalSquareVerticalTranslatedEdgeRed xStart yStart) f hbond Z X hXe hposA
    (fun M σ' τ' => hid M σ' τ') σ N

end PEPS
end TNLean

end NormalSquareEdgeCoeff

section NormalSquareInteriorAbsorbedFamily

/-!
## The interior absorbed gauge family on the open square lattice

This file assembles the per-edge absorbing gauges of the interior edges of the finite open
square lattice into a single per-edge gauge family `X` carrying the bare-edge absorbed equality

> `edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ (reindex N)`

at every edge with interior margins (`NormalSquareInteriorEdgeDatum`).  This is the open-lattice
counterpart of the torus family `exists_torusCovariantAbsorbedGaugeFamily`, restricted to the
edges the open blocking geometry reaches: the bare-edge identity at an edge depends only on the
family's value there, so the absorbing gauges of distinct interior edges combine edge by edge
with no compatibility conditions.

Unlike the torus, the open lattice carries no translations, so the family is *chosen* at each
interior edge rather than transported from one reference witness per orientation class; no
covariance between the gauges at distinct edges is asserted.  Edges without interior margins
(those near the lattice boundary) receive the identity gauge and carry no absorbed equality;
that boundary geometry is the residual open part recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining mathematical
obligations".

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`.

### References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open ManyBody (Edge SquareLatticeVertex horizontalSquareLatticeEdge_eq_rightEdge squareLatticeGraph
  verticalSquareLatticeEdge_eq_upEdge)

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ}

/-- **The absorbing gauge at an edge with interior margins.**

An edge of the open square lattice carrying the cover-free interior datum --- horizontal or
vertical with the corresponding interior margins --- admits an invertible matrix `Ze` such that
every per-edge gauge family `X` with `X e = Ze` satisfies the bare-edge absorbed equality at `e`
against `applyGauge B X`.

The horizontal and vertical cases are
`exists_absorbingGauge_normalSquareHorizontalTranslatedEdge` and its vertical counterpart,
reached by rewriting the edge as the distinguished edge of the translated interior frame at
offset `(x-1, y-2)` (horizontal) or `(x-2, y-1)` (vertical).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_absorbingGauge_of_normalSquareInteriorEdgeDatum
    (A B : Tensor (squareLatticeGraph width height) d)
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g)
    (e : Edge (squareLatticeGraph width height))
    (he : NormalSquareInteriorEdgeDatum e) :
    ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
      ∀ X : (g : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim g)) ℂ,
        X e = Ze →
        ∀ (σ : SquareLatticeVertex width height → Fin d)
          (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
            edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  rcases he with ⟨hEdge, hMargins⟩ | ⟨hEdge, hMargins⟩
  · -- Horizontal interior edge: the translated frame at `(x-1, y-2)`.
    obtain ⟨hx3, hx7, hy4, hy6⟩ := hMargins
    have heq : e = normalSquareHorizontalTranslatedEdge
        (e.1.1.1.1 - 1) (e.1.1.2.1 - 2) (by omega) (by omega) := by
      rw [normalSquareHorizontalTranslatedEdge_sub_eq_rightEdge
        (by omega) (by omega) (by omega) (by omega)]
      exact horizontalSquareLatticeEdge_eq_rightEdge e hEdge
    rw [heq]
    exact exists_absorbingGauge_normalSquareHorizontalTranslatedEdge A B hA hB
      (by omega) (by omega) (by omega) (by omega) hbond hAB hd hposA hposB
  · -- Vertical interior edge: the translated frame at `(x-2, y-1)`.
    obtain ⟨hx4, hx6, hy3, hy7⟩ := hMargins
    have heq : e = normalSquareVerticalTranslatedEdge
        (e.1.1.1.1 - 2) (e.1.1.2.1 - 1) (by omega) (by omega) := by
      rw [normalSquareVerticalTranslatedEdge_sub_eq_upEdge
        (by omega) (by omega) (by omega) (by omega)]
      exact verticalSquareLatticeEdge_eq_upEdge e hEdge
    rw [heq]
    exact exists_absorbingGauge_normalSquareVerticalTranslatedEdge A B hA hB
      (by omega) (by omega) (by omega) (by omega) hbond hAB hd hposA hposB

/-- **The interior absorbed gauge family on the open square lattice.**

For two tensors on the open square lattice with the rectangular-injectivity hypotheses,
matched bond dimensions, the same state, and positive bonds, there is a per-edge gauge
family `X` over the second tensor's bonds satisfying the bare-edge absorbed equality against
`applyGauge B X` at every edge with interior margins: inserting `N` on `A`'s edge `e` matches
inserting the reindexed `N` on `applyGauge B X`'s edge `e`, for every global physical
configuration and every matrix.

The family is built edge by edge: each interior edge receives its own absorbing gauge
(`exists_absorbingGauge_of_normalSquareInteriorEdgeDatum`), and edges without interior margins
receive the identity.  Because the bare-edge identity at an edge constrains only the family's
value there, no compatibility between the choices is needed.  No covariance between the gauges
of distinct edges is asserted; the translation-invariant reduction to one horizontal and one
vertical matrix has no carrier on the open lattice, which carries no translations.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_normalSquareInteriorAbsorbedGaugeFamily
    (A B : Tensor (squareLatticeGraph width height) d)
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g) :
    ∃ X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ,
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareInteriorEdgeDatum e →
        ∀ (σ : SquareLatticeVertex width height → Fin d)
          (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
            edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  classical
  -- The per-edge selection: at interior edges the absorbing gauge, elsewhere the identity.
  have hsel : ∀ e : Edge (squareLatticeGraph width height),
      ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
        NormalSquareInteriorEdgeDatum e →
        ∀ X : (g : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim g)) ℂ,
          X e = Ze →
          ∀ (σ : SquareLatticeVertex width height → Fin d)
            (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
            edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
              edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
                (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
    intro e
    by_cases he : NormalSquareInteriorEdgeDatum e
    · obtain ⟨Ze, hZe⟩ := exists_absorbingGauge_of_normalSquareInteriorEdgeDatum A B
        hA hB hbond hAB hd hposA hposB e he
      exact ⟨Ze, fun _ => hZe⟩
    · exact ⟨1, fun hcon => absurd hcon he⟩
  choose X hX using hsel
  exact ⟨X, fun e he σ N => hX e he X rfl σ N⟩

end PEPS
end TNLean

end NormalSquareInteriorAbsorbedFamily
