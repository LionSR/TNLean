import TNLean.PEPS.TorusRectangleReferenceData
import TNLean.PEPS.TorusEdgeGauge
import TNLean.PEPS.NormalEdgeGaugeFamily

/-!
# The per-edge gauge at the torus reference edges from rectangle injectivity

Two normal PEPS on the discrete torus, related by `SameState` with matched bond dimensions and both
satisfying the rectangular-injectivity hypotheses with union closure, carry on the distinguished
horizontal and vertical reference edges the per-edge gauge of the edge blocking: the bond
dimensions coincide and the forward region-insertion transfer is conjugation by an invertible
matrix, together with the region-insertion coefficient identity the conjugation realizes.

This is `exists_regionEdgeGauge_torus_coeff` fed the faithful rectangle-injectivity reference datum
of `TNLean/PEPS/TorusRectangleReferenceData.lean`, in place of the vertex-injective singleton
datum.  The injectivity inputs are the rectangular-injectivity hypotheses for both tensors plus
union closure for the second tensor's host block; no single-vertex injectivity is used.

## References

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
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red := by
    have hi := hB.horizontalEdgeRed_injective (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
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
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red := by
    have hi := hB.verticalEdgeRed_injective (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ DA.red) :=
    regionBlockedTensorInjective_host DB hUB
  exact exists_regionEdgeGauge_torus_coeff DA DB rfl rfl rfl hbond hAB hd hposA hposB hsingle
    hRB hCB

end PEPS
end TNLean
