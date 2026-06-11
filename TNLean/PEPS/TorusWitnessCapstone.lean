import TNLean.PEPS.TorusWitnessTranslate

/-!
# The orientation-uniform-mod-scalar family from the torus rectangle hypotheses

The orientation-uniform reduction of the normal PEPS Fundamental Theorem on the discrete torus is
assembled from an `EdgeCoeffIdentityWitness` at every edge of each orientation class
(`isTorusOrientationUniformGaugeFamilyModScalar_of_edgeWitnesses`).  This file produces those
witnesses for a translation-invariant pair from the source's rectangle-injectivity hypotheses, by
transporting the reference-edge coefficient identity (`exists_horizontalReferenceEdgeGauge_coeff`)
along each class translation (`edgeCoeffIdentityWitness_translate`).

The per-edge gauge family `X` is supplied with the per-edge coefficient identity it realizes over
the image of the reference region; this is the shape the per-edge gauge engine delivers.  Matching
the transported reference gauge with the capstone's `glReindex (huni.horizontal he).symm Xh`
(`glReindex_glReindex`) and gathering the two orientation classes gives the
orientation-uniform-mod-scalar family the reduction concludes.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- A torus right edge is a horizontal edge. -/
theorem isHorizontalTorusEdge_torusRightEdge (p : TorusVertex width height) :
    IsHorizontalTorusEdge (torusRightEdge p) := by
  have hadj : torusHorizontalNeighbor p (p.1 + 1, p.2) := ⟨rfl, Or.inl rfl⟩
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · change torusHorizontalNeighbor (torusRightEdge p).1.1 (torusRightEdge p).1.2
    rw [torusRightEdge, h1, h2]; exact hadj
  · change torusHorizontalNeighbor (torusRightEdge p).1.1 (torusRightEdge p).1.2
    rw [torusRightEdge, h1, h2]; exact torusHorizontalNeighbor_symm hadj

/-- A torus up edge is a vertical edge. -/
theorem isVerticalTorusEdge_torusUpEdge (p : TorusVertex width height) :
    IsVerticalTorusEdge (torusUpEdge p) := by
  have hadj : torusVerticalNeighbor p (p.1, p.2 + 1) := ⟨rfl, Or.inl rfl⟩
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · change torusVerticalNeighbor (torusUpEdge p).1.1 (torusUpEdge p).1.2
    rw [torusUpEdge, h1, h2]; exact hadj
  · change torusVerticalNeighbor (torusUpEdge p).1.1 (torusUpEdge p).1.2
    rw [torusUpEdge, h1, h2]; exact torusVerticalNeighbor_symm hadj

/-- The reference horizontal edge is a horizontal edge. -/
theorem isHorizontalTorusEdge_torusHorizontalReferenceEdge (xStart yStart : ℕ) :
    IsHorizontalTorusEdge
      (torusHorizontalReferenceEdge (width := width) (height := height) xStart yStart) :=
  isHorizontalTorusEdge_torusRightEdge _

/-- The reference vertical edge is a vertical edge. -/
theorem isVerticalTorusEdge_torusVerticalReferenceEdge (xStart yStart : ℕ) :
    IsVerticalTorusEdge
      (torusVerticalReferenceEdge (width := width) (height := height) xStart yStart) :=
  isVerticalTorusEdge_torusUpEdge _

/-- The translation carrying the reference horizontal edge to a given horizontal edge `e`, packaged
as data: the offset is the coordinate difference of the left endpoints. -/
noncomputable def translate_horizontalReferenceEdge {xStart yStart : ℕ}
    {e : Edge (torusGraph width height)} (he : IsHorizontalTorusEdge e) :
    {ab : ZMod width × ZMod height //
      e = Edge.map (translate ab.1 ab.2) (torusHorizontalReferenceEdge xStart yStart)} :=
  ⟨((isHorizontalTorusEdge_eq_rightEdge he).choose.1 - (((xStart : ℕ) + 1 : ZMod width)),
      (isHorizontalTorusEdge_eq_rightEdge he).choose.2 - (((yStart : ℕ) + 2 : ZMod height))),
    by
      conv_lhs => rw [(isHorizontalTorusEdge_eq_rightEdge he).choose_spec]
      rw [← translateEdge_eq_map, torusHorizontalReferenceEdge, translateEdge_torusRightEdge]
      congr 1
      apply Prod.ext <;> push_cast <;> ring⟩

/-- The translation carrying the reference vertical edge to a given vertical edge `e`, as data. -/
noncomputable def translate_verticalReferenceEdge {xStart yStart : ℕ}
    {e : Edge (torusGraph width height)} (he : IsVerticalTorusEdge e) :
    {ab : ZMod width × ZMod height //
      e = Edge.map (translate ab.1 ab.2) (torusVerticalReferenceEdge xStart yStart)} :=
  ⟨((isVerticalTorusEdge_eq_upEdge he).choose.1 - (((xStart : ℕ) + 2 : ZMod width)),
      (isVerticalTorusEdge_eq_upEdge he).choose.2 - (((yStart : ℕ) + 1 : ZMod height))),
    by
      conv_lhs => rw [(isVerticalTorusEdge_eq_upEdge he).choose_spec]
      rw [← translateEdge_eq_map, torusVerticalReferenceEdge, translateEdge_torusUpEdge]
      congr 1
      apply Prod.ext <;> push_cast <;> ring⟩

/-- **The horizontal coefficient-identity witness family on the torus from rectangle injectivity.**

For a translation-invariant pair `A`, `B` on the torus with matched bond dimensions, positive
bonds, the same state, and both satisfying the rectangular-injectivity hypotheses with union
closure, every horizontal edge carries an `EdgeCoeffIdentityWitness` whose per-edge and reference
gauges are both the reference horizontal gauge transported to that edge.

The reference horizontal gauge `Zh` and its coefficient identity come from
`exists_horizontalReferenceEdgeGauge_coeff` at the reference horizontal edge.  Writing each
horizontal edge as the translation image of the reference edge
(`translate_horizontalReferenceEdge`), the reference coefficient identity transports to that
edge realized by the transported gauge (`edgeCoeffIdentityWitness_translate`), supplying both
witness fields.  This is the horizontal half of the translation production the orientation-uniform
selection `isTorusOrientationUniformGaugeFamilyModScalar_of_edgeWitnesses` consumes; the per-edge
gauge family is the transported reference, the source's *"X, the same matrix on all horizontal
edges"*.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_edgeCoeffIdentityWitness_horizontalFamily
    {A B : Tensor (torusGraph width height) d} {xStart yStart : ℕ}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAh : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBh : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUAh : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUBh : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 1 ≤ yStart)
    (hxw : xStart + 5 < width) (hyh : yStart + 5 < height)
    (hxw' : xStart + 7 ≤ width) (hyh' : yStart + 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    ∀ (e : Edge (torusGraph width height)), IsHorizontalTorusEdge e →
      ∃ (Z Zref : GL (Fin (B.bondDim e)) ℂ) (hE : A.bondDim e = B.bondDim e),
        Nonempty (EdgeCoeffIdentityWitness A B e Z Zref hE) := by
  -- The reference horizontal gauge and its coefficient identity at the reference edge.
  obtain ⟨hEref, Zref, hZref⟩ :=
    exists_horizontalReferenceEdgeGauge_coeff hAh hBh hUAh hUBh hx0 hy0 hxw hyh hxw' hyh'
      hbond hAB hd hposA hposB
  intro e he
  -- Write `e` as the translation image of the reference horizontal edge.
  obtain ⟨⟨a, b⟩, rfl⟩ := translate_horizontalReferenceEdge (xStart := xStart)
    (yStart := yStart) he
  -- Abbreviate the reference region and its single boundary edge.
  set R := (torusHorizontalRectangleBlockingDatum hAh hUAh hx0 hy0 hxw' hyh').red with hRdef
  set f := singleBoundaryEdge (G := torusGraph width height) A R
    (torusHorizontalRectangleBlockingDatum hAh hUAh hx0 hy0 hxw' hyh').blue
    (torusHorizontalReferenceEdge xStart yStart)
    (fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hAh hUAh hx0 hy0 hxw hyh
      hxw' hyh' g) with hfdef
  -- `B`'s reference region block and host block are injective.
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B R := by
    have hi := hBh.horizontalEdgeRed_injective (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B (Finset.univ \ R) :=
    regionBlockedTensorInjective_host
      (torusHorizontalRectangleBlockingDatum hBh hUBh hx0 hy0 hxw' hyh') hUBh
  -- The bond-dimension equality at the translated boundary edge, derived from the reference
  -- equality and the two translation bond-dimension equalities.
  have hEX : A.bondDim (boundaryEdgeMap (translate a b) R f).1 =
      B.bondDim (boundaryEdgeMap (translate a b) R f).1 :=
    (bondDim_boundaryEdgeMap_translate hA a b R f).trans
      (hEref.trans (bondDim_boundaryEdgeMap_translate hB a b R f).symm)
  -- The transported reference gauge realizes both the per-edge and reference coefficient identities
  -- at the translated edge, by the transport lemma; the witness producer assembles the witness.
  refine ⟨glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref,
    glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref, hEX,
    ⟨edgeCoeffIdentityWitness_translate hA hB a b R f hEref Zref hposB hRB hCB hZref
      (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref) hEX ?_⟩⟩
  -- The per-edge gauge identity is the transported reference identity; preimage the image-region
  -- configurations through the configuration transport before the transported identity applies.
  intro M σ' τ'
  obtain ⟨σ, τ, rfl, rfl⟩ := exists_regionPhysicalConfig_translate_preimage (d := d) a b R σ' τ'
  exact regionInsertedCoeff_translate_coeffIdentity_conj hA hB a b R f hEref Zref hZref
    hEX (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref) rfl M σ τ

/-- **The vertical coefficient-identity witness family on the torus from rectangle injectivity.**

The vertical counterpart of `exists_edgeCoeffIdentityWitness_horizontalFamily`: every vertical edge
carries an `EdgeCoeffIdentityWitness` whose per-edge and reference gauges are both the reference
vertical gauge transported to that edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_edgeCoeffIdentityWitness_verticalFamily
    {A B : Tensor (torusGraph width height) d} {xStart yStart : ℕ}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAh : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBh : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUAh : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUBh : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hx0 : 2 ≤ xStart) (hy0 : 2 ≤ yStart)
    (hxw : xStart + 5 < width) (hyh : yStart + 5 < height)
    (hxw' : xStart + 7 ≤ width) (hyh' : yStart + 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    ∀ (e : Edge (torusGraph width height)), IsVerticalTorusEdge e →
      ∃ (Z Zref : GL (Fin (B.bondDim e)) ℂ) (hE : A.bondDim e = B.bondDim e),
        Nonempty (EdgeCoeffIdentityWitness A B e Z Zref hE) := by
  obtain ⟨hEref, Zref, hZref⟩ :=
    exists_verticalReferenceEdgeGauge_coeff hAh hBh hUAh hUBh hx0 hy0 hxw hyh hxw' hyh'
      hbond hAB hd hposA hposB
  intro e he
  obtain ⟨⟨a, b⟩, rfl⟩ := translate_verticalReferenceEdge (xStart := xStart)
    (yStart := yStart) he
  set R := (torusVerticalRectangleBlockingDatum hAh hUAh hx0 hy0 hxw' hyh').red with hRdef
  set f := singleBoundaryEdge (G := torusGraph width height) A R
    (torusVerticalRectangleBlockingDatum hAh hUAh hx0 hy0 hxw' hyh').blue
    (torusVerticalReferenceEdge xStart yStart)
    (fun g => isCrossingEdge_torusVerticalRectangleBlockingDatum A hAh hUAh hx0 hy0 hxw hyh
      hxw' hyh' g) with hfdef
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B R := by
    have hi := hBh.verticalEdgeRed_injective (xStart := xStart) (yStart := yStart)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B (Finset.univ \ R) :=
    regionBlockedTensorInjective_host
      (torusVerticalRectangleBlockingDatum hBh hUBh hx0 hy0 hxw' hyh') hUBh
  have hEX : A.bondDim (boundaryEdgeMap (translate a b) R f).1 =
      B.bondDim (boundaryEdgeMap (translate a b) R f).1 :=
    (bondDim_boundaryEdgeMap_translate hA a b R f).trans
      (hEref.trans (bondDim_boundaryEdgeMap_translate hB a b R f).symm)
  refine ⟨glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref,
    glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref, hEX,
    ⟨edgeCoeffIdentityWitness_translate hA hB a b R f hEref Zref hposB hRB hCB hZref
      (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref) hEX ?_⟩⟩
  intro M σ' τ'
  obtain ⟨σ, τ, rfl, rfl⟩ := exists_regionPhysicalConfig_translate_preimage (d := d) a b R σ' τ'
  exact regionInsertedCoeff_translate_coeffIdentity_conj hA hB a b R f hEref Zref hZref
    hEX (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Zref) rfl M σ τ

/-- **The orientation-uniform-mod-scalar family from the torus rectangle hypotheses.**

For a translation-invariant pair `A`, `B` on the torus with matched bond dimensions, positive
bonds, the same state, and both satisfying the rectangular-injectivity hypotheses with union
closure, there is a per-edge gauge family on the torus that is orientation uniform up to per-edge
scalars.

The horizontal and vertical coefficient-identity witness families
(`exists_edgeCoeffIdentityWitness_horizontalFamily`,
`exists_edgeCoeffIdentityWitness_verticalFamily`) provide, at every edge of each orientation class,
a witness whose per-edge and reference gauges are both the reference gauge transported to that edge.
Choosing the per-edge gauge family to be those transported reference gauges and feeding the
witnesses to the orientation-uniform selection
`isTorusOrientationUniformGaugeFamilyModScalar_of_edgeWitnesses` assembles the family
unconditionally from the source's rectangle hypotheses: this is the source's *"X and Y, the same
matrix on all horizontal (vertical) edges"*, with the per-edge scalars all one.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTorusOrientationUniformGaugeFamilyModScalar_torus_rectangle
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
    (hxhw : xhStart + 5 < width) (hyhh : yhStart + 5 < height)
    (hxhw' : xhStart + 7 ≤ width) (hyhh' : yhStart + 7 ≤ height)
    (hxv0 : 2 ≤ xvStart) (hyv0 : 2 ≤ yvStart)
    (hxvw : xvStart + 5 < width) (hyvh : yvStart + 5 < height)
    (hxvw' : xvStart + 7 ≤ width) (hyvh' : yvStart + 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    ∃ (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ),
      IsTorusOrientationUniformGaugeFamilyModScalar
        (torusUniformBondDim_of_translationInvariant hB) X := by
  classical
  set huni := torusUniformBondDim_of_translationInvariant hB with hunidef
  -- The two reference gauges and their per-edge witness families.
  obtain ⟨hEh, Zh, hZh⟩ :=
    exists_horizontalReferenceEdgeGauge_coeff hAr hBr hUA hUB hxh0 hyh0 hxhw hyhh hxhw' hyhh'
      hbond hAB hd hposA hposB
  obtain ⟨hEv, Zv, hZv⟩ :=
    exists_verticalReferenceEdgeGauge_coeff hAr hBr hUA hUB hxv0 hyv0 hxvw hyvh hxvw' hyvh'
      hbond hAB hd hposA hposB
  -- The reference horizontal/vertical orientation matrices, read at the reference edges.
  set Xh := glReindex
    (huni.horizontal (isHorizontalTorusEdge_torusHorizontalReferenceEdge xhStart yhStart)) Zh
    with hXhdef
  set Xv := glReindex
    (huni.vertical (isVerticalTorusEdge_torusVerticalReferenceEdge xvStart yvStart)) Zv
    with hXvdef
  refine ⟨torusOrientationUniformGauge huni Xh Xv,
    isTorusOrientationUniformGaugeFamilyModScalar_of_edgeWitnesses huni _ Xh Xv
      (fun e => congrFun hbond e) (fun e he => ?_) (fun e he => ?_)⟩
  · -- Horizontal witness: the per-edge gauge is `glReindex _ Xh`, which equals the transported
    -- reference single matrix; supply the witness against it.
    rw [torusOrientationUniformGauge_horizontal huni Xh Xv he]
    -- Write `e` as the translation image of the reference horizontal edge.
    obtain ⟨⟨a, b⟩, heq⟩ := translate_horizontalReferenceEdge (xStart := xhStart)
      (yStart := yhStart) he
    subst heq
    exact edgeCoeffIdentityWitness_translateUniform hA hB a b
      (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw' hyhh').red
      (singleBoundaryEdge (G := torusGraph width height) A
        (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw' hyhh').red
        (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw' hyhh').blue
        (torusHorizontalReferenceEdge xhStart yhStart)
        (fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hAr hUA hxh0 hyh0 hxhw
          hyhh hxhw' hyhh' g))
      hEh Zh hposB
      (by
        have hi := hBr.horizontalEdgeRed_injective (xStart := xhStart) (yStart := yhStart)
          (by omega) (by omega)
        rwa [regionInjectivityDataOf_isInjective] at hi)
      (regionBlockedTensorInjective_host
        (torusHorizontalRectangleBlockingDatum hBr hUB hxh0 hyh0 hxhw' hyhh') hUB)
      hZh Xh
      (huni.horizontal (isHorizontalTorusEdge_torusHorizontalReferenceEdge xhStart yhStart))
      (huni.horizontal he) hXhdef
  · rw [torusOrientationUniformGauge_vertical huni Xh Xv he]
    obtain ⟨⟨a, b⟩, heq⟩ := translate_verticalReferenceEdge (xStart := xvStart)
      (yStart := yvStart) he
    subst heq
    exact edgeCoeffIdentityWitness_translateUniform hA hB a b
      (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw' hyvh').red
      (singleBoundaryEdge (G := torusGraph width height) A
        (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw' hyvh').red
        (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw' hyvh').blue
        (torusVerticalReferenceEdge xvStart yvStart)
        (fun g => isCrossingEdge_torusVerticalRectangleBlockingDatum A hAr hUA hxv0 hyv0 hxvw
          hyvh hxvw' hyvh' g))
      hEv Zv hposB
      (by
        have hi := hBr.verticalEdgeRed_injective (xStart := xvStart) (yStart := yvStart)
          (by omega) (by omega)
        rwa [regionInjectivityDataOf_isInjective] at hi)
      (regionBlockedTensorInjective_host
        (torusVerticalRectangleBlockingDatum hBr hUB hxv0 hyv0 hxvw' hyvh') hUB)
      hZv Xv
      (huni.vertical (isVerticalTorusEdge_torusVerticalReferenceEdge xvStart yvStart))
      (huni.vertical he) hXvdef

end PEPS
end TNLean
