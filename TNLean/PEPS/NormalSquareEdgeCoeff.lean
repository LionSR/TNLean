import TNLean.PEPS.NormalEdgeGaugeFamily
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed

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

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

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
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
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
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
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
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
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
    exists_regionEdgeGauge_normalSquareHorizontalTranslatedEdge_coeff A B hA hUA hB hUB
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
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
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
    exists_regionEdgeGauge_normalSquareVerticalTranslatedEdge_coeff A B hA hUA hB hUB
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
