import TNLean.PEPS.TorusWitnessTranslate

/-!
# The per-edge coefficient-identity witness families on the torus

The torus construction in the normal PEPS Fundamental Theorem requires an
`EdgeCoeffIdentityWitness` at every edge of each orientation class.  This file produces those
witnesses for a translation-invariant pair from the source's rectangle-injectivity hypotheses, by
transporting the reference-edge coefficient identity (`exists_horizontalReferenceEdgeGauge_coeff`)
along each class translation (`edgeCoeffIdentityWitness_translate`).  The witnesses feed the
bare-edge absorbed equality (`edgeAbsorbed_of_edgeCoeffIdentityWitness`) and the
translation-covariant absorbed family (`exists_torusCovariantAbsorbedGaugeFamily`).

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
witness identities.  This is the horizontal half of the translation construction of the witnesses; the
per-edge gauge family is the transported reference, the source's *"X, the same matrix on all
horizontal edges"* read in the ordered edge convention.

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

end PEPS
end TNLean
