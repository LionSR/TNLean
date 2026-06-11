import TNLean.PEPS.TorusRectangleGauge
import TNLean.PEPS.TorusConjCovarianceFamily

/-!
# The reference-edge coefficient-identity witness from rectangle injectivity

The orientation-uniform-mod-scalar family is assembled from an `EdgeCoeffIdentityWitness` at every
edge of each orientation class (`isTorusOrientationUniformGaugeFamilyModScalar_of_edgeWitnesses`).
This file produces such a witness at the distinguished horizontal reference edge from the faithful
rectangle-injectivity reference datum: the per-edge gauge of `exists_horizontalReferenceEdgeGauge_coeff`
realizes the region-insertion coefficient identity over the reference red region, so taking it as
both the per-edge gauge and the reference gauge yields a witness.

This is the base case of the geometric production the orientation-uniform reduction consumes.  The
remaining step — transporting the reference witness along each class translation to obtain a witness
at every edge against the *transported* reference matrix — is the residual obligation recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, using
`regionInsertedCoeff_translate_coeffIdentity` and `exists_regionEdgeGauge_torus_coeff` on the
translated blocking datum.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **A coefficient-identity witness at the horizontal reference edge from rectangle injectivity.**

For two torus tensors `A`, `B` with the same state, matched bond dimensions, positive bonds, and
both satisfying the rectangular-injectivity hypotheses with union closure, the distinguished
horizontal reference edge carries an `EdgeCoeffIdentityWitness` whose region is the reference red
block and whose per-edge and reference gauges are both the per-edge gauge `Z` produced by the gauge
engine.  Both coefficient identities are the single identity `Z` realizes, so the witness holds.

This exhibits the witness interface as inhabited by the faithful rectangle-injectivity reference
datum, the base case of the orientation-class production.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_edgeCoeffIdentityWitness_horizontalReference
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
    (hxw : xStart + 5 < width) (hyh : yStart + 5 < height)
    (hxw' : xStart + 7 ≤ width) (hyh' : yStart + 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    ∃ (hE : A.bondDim (torusHorizontalReferenceEdge xStart yStart) =
        B.bondDim (torusHorizontalReferenceEdge xStart yStart))
      (Z : GL (Fin (B.bondDim (torusHorizontalReferenceEdge xStart yStart))) ℂ),
      Nonempty (EdgeCoeffIdentityWitness A B (torusHorizontalReferenceEdge xStart yStart) Z Z hE) := by
  obtain ⟨hEdge, Z, hZ⟩ :=
    exists_horizontalReferenceEdgeGauge_coeff hA hB hUA hUB hx0 hy0 hxw hyh hxw' hyh'
      hbond hAB hd hposA hposB
  refine ⟨hEdge, Z, ⟨?_⟩⟩
  -- `B`'s red and host blocks are injective.
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (torusHorizontalRectangleBlockingDatum hA hUA hx0 hy0 hxw' hyh').red := by
    have hi := hB.horizontalEdgeRed_injective (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ (torusHorizontalRectangleBlockingDatum hA hUA hx0 hy0 hxw' hyh').red) :=
    regionBlockedTensorInjective_host
      (torusHorizontalRectangleBlockingDatum hB hUB hx0 hy0 hxw' hyh') hUB
  -- The single boundary edge of the reference red region.
  have hsingle := fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hA hUA hx0 hy0
    hxw hyh hxw' hyh' g
  exact
    { region := (torusHorizontalRectangleBlockingDatum hA hUA hx0 hy0 hxw' hyh').red
      isBoundary :=
        (singleBoundaryEdge (G := torusGraph width height) A
          (torusHorizontalRectangleBlockingDatum hA hUA hx0 hy0 hxw' hyh').red
          (torusHorizontalRectangleBlockingDatum hA hUA hx0 hy0 hxw' hyh').blue
          (torusHorizontalReferenceEdge xStart yStart) hsingle).2
      hRB := hRB
      hCB := hCB
      hposB := hposB
      hidZ := hZ
      hidZref := hZ }

end PEPS
end TNLean
