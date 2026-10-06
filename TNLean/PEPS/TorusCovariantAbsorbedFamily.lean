/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusReferenceAbsorbedFamily

/-!
# The translation-covariant absorbed gauge family on the torus

This file produces the every-edge bare-edge absorbed equality with the per-edge gauge family
*constructed* rather than chosen edge by edge: every edge of each orientation class receives the
orientation-adapted absorbing gauge of the transported reference witness, the reference gauge of
its class carried along the unique translation reaching the edge (arXiv:1804.04964, Section 3,
proof of Theorem 3, lines 1449--1544 of `Papers/1804.04964/paper_normal.tex`).

Because the whole family is read off two reference gauges, it is translation covariant
(`IsTranslationCovariantGaugeFamily`): the gauge at any translate of an edge is the gauge at the
edge carried across the bond-dimension equality, transposed-inverted exactly when the
translation swaps the stored endpoint order.  This covariance is the source's *"the same matrix
`X` (`Y`) on all horizontal (vertical) edges"* in the ordered edge convention, and it is the
input to the translation invariance of the comparison scalars in the final step of Theorem 3.

The family is *not* literally one matrix per orientation class in the ordered edge convention:
on the edges wrapping a torus seam the stored endpoint order is reversed, so the family carries
the transposed inverse of the reference matrix there.  A lexicographically uniform-up-to-scalar
family therefore cannot describe it (see `docs/paper-gaps/peps_normal_ft_section3_route.tex`,
section "Closure on the torus"); the covariance recorded here is the orientation-faithful
uniformity statement.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The translation-covariant absorbed gauge family on the torus.**

For a translation-invariant pair `A`, `B` on the torus with matched bond dimensions, positive
bonds, the same state, and both satisfying the rectangular-injectivity hypotheses with union
closure, there is a per-edge gauge family `X` over the second tensor's bonds that

* is translation covariant (`IsTranslationCovariantGaugeFamily`): the gauge at any translate of
  an edge is the gauge at the edge carried across the bond-dimension equality,
  transposed-inverted exactly when the translation swaps the stored endpoint order; and
* satisfies the bare-edge absorbed equality against `applyGauge B X` at every edge: inserting
  `N` on `A`'s edge `e` matches inserting the reindexed `N` on `applyGauge B X`'s edge `e`, for
  every global physical configuration and every matrix.

Rather than choosing a witness independently at each edge, every edge of each orientation class
receives the orientation-adapted absorbing gauge of the *transported* reference witness: one
horizontal reference gauge and one vertical reference gauge, carried along the unique
translation reaching the edge.  The translation covariance is exactly the determinism of this
construction.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_torusCovariantAbsorbedGaugeFamily
    {A B : Tensor (torusGraph width height) d} {xhStart yhStart xvStart yvStart : ℕ}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hxh0 : 2 ≤ xhStart) (hyh0 : 1 ≤ yhStart)
    (hxhw : xhStart + 5 = width ∨ xhStart + 7 ≤ width)
    (hyhh : yhStart + 5 = height ∨ yhStart + 7 ≤ height)
    (hxv0 : 1 ≤ xvStart) (hyv0 : 2 ≤ yvStart)
    (hxvw : xvStart + 5 = width ∨ xvStart + 7 ≤ width)
    (hyvh : yvStart + 5 = height ∨ yvStart + 7 ≤ height)
    (hbd : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    ∃ X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ,
      IsTranslationCovariantGaugeFamily B X ∧
      ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff (G := torusGraph width height) A e σ N =
          edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
            (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N) := by
  classical
  have hw : 2 < width := by omega
  have hh : 2 < height := by omega
  -- The two reference gauges and their coefficient identities at the reference edges.
  obtain ⟨hEh, Zh, hZh⟩ :=
    exists_horizontalReferenceEdgeGauge_coeff hAr hBr hUA hUB hxh0 hyh0 hxhw hyhh
      hbd hAB hd hposA hposB
  obtain ⟨hEv, Zv, hZv⟩ :=
    exists_verticalReferenceEdgeGauge_coeff hAr hBr hUA hUB hxv0 hyv0 hxvw hyvh
      hbd hAB hd hposA hposB
  -- The reference regions and their distinguished boundary edges.
  set Rh := (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw hyhh).red with hRhdef
  set fh := singleBoundaryEdge (G := torusGraph width height) A Rh
    (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw hyhh).blue
    (torusHorizontalReferenceEdge xhStart yhStart)
    (fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hAr hUA hxh0 hyh0 hxhw
      hyhh g) with hfhdef
  set Rv := (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw hyvh).red with hRvdef
  set fv := singleBoundaryEdge (G := torusGraph width height) A Rv
    (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw hyvh).blue
    (torusVerticalReferenceEdge xvStart yvStart)
    (fun g => isCrossingEdge_torusVerticalRectangleBlockingDatum A hAr hUA hxv0 hyv0 hxvw
      hyvh g) with hfvdef
  have hRhB : RegionBlockedTensorInjective B Rh := by
    have hi := hBr.horizontalEdgeRed_injective (xStart := xhStart) (yStart := yhStart)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hChB : RegionBlockedTensorInjective B (Finset.univ \ Rh) :=
    regionBlockedTensorInjective_host
      (torusHorizontalRectangleBlockingDatum hBr hUB hxh0 hyh0 hxhw hyhh) hUB
  have hRvB : RegionBlockedTensorInjective B Rv := by
    have hi := hBr.verticalEdgeRed_injective (xStart := xvStart) (yStart := yvStart)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCvB : RegionBlockedTensorInjective B (Finset.univ \ Rv) :=
    regionBlockedTensorInjective_host
      (torusVerticalRectangleBlockingDatum hBr hUB hxv0 hyv0 hxvw hyvh) hUB
  let wh : EdgeCoeffIdentityWitness A B fh.1 Zh Zh (congr_fun hbd fh.1) :=
    ⟨Rh, fh.property, hRhB, hChB, hposB, hZh, hZh⟩
  let wv : EdgeCoeffIdentityWitness A B fv.1 Zv Zv (congr_fun hbd fv.1) :=
    ⟨Rv, fv.property, hRvB, hCvB, hposB, hZv, hZv⟩
  exact exists_torusCovariantAbsorbedGaugeFamily_of_edgeReferenceWitnesses
    hA hB hw hh hbd hposA fh.1 fv.1
    (isHorizontalTorusEdge_torusHorizontalReferenceEdge xhStart yhStart)
    (isVerticalTorusEdge_torusVerticalReferenceEdge xvStart yvStart) Zh Zh Zv Zv wh wv
    (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw hyhh).left_mem_red
    (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw hyvh).left_mem_red

end PEPS
end TNLean
