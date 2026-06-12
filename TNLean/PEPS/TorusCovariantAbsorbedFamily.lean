import TNLean.PEPS.TorusAbsorbedCovariance
import TNLean.PEPS.TorusEdgeAbsorbed

/-!
# The translation-covariant absorbed gauge family on the torus

This file rebuilds the every-edge bare-edge absorbed equality of
`exists_edgeAbsorbed_torus_rectangle` with the per-edge gauge family *constructed* rather than
chosen: every edge of each orientation class receives the orientation-adapted absorbing gauge of
the transported reference witness, the reference gauge of its class carried along the unique
translation reaching the edge (arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544
of `Papers/1804.04964/paper_normal.tex`).

Because the whole family is read off two reference gauges, it is translation covariant
(`IsTranslationCovariantGaugeFamily`): the gauge at any translate of an edge is the gauge at the
edge carried across the bond-dimension equality, transposed-inverted exactly when the
translation swaps the stored endpoint order.  This covariance is the source's *"the same matrix
`X` (`Y`) on all horizontal (vertical) edges"* in the ordered edge convention, and it is the
input to the translation invariance of the comparison scalars in the final step of Theorem 3.

The family is *not* literally one matrix per orientation class in the ordered edge convention:
on the edges wrapping a torus seam the stored endpoint order is reversed, so the family carries
the transposed inverse of the reference matrix there.  The lex-uniform predicate
`IsTorusOrientationUniformGaugeFamilyModScalar` therefore does not describe this family; the
covariance recorded here is the orientation-faithful uniformity statement.

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

/-- Transport across matching translation parameters collapses: if `a' = a` and `b' = b`, the
reindexed absorbing gauge of the `(a', b')`-translate is the absorbing gauge of the
`(a, b)`-translate. -/
theorem glReindex_transportedAbsorbedGauge_eq (B : Tensor (torusGraph width height) d)
    (hB : IsTorusTranslationInvariant B)
    (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ) {a a' : ZMod width} {b b' : ZMod height}
    (ha : a' = a) (hb : b' = b)
    (hcast : B.bondDim (boundaryEdgeMap (translate a' b') R f).1 =
      B.bondDim (boundaryEdgeMap (translate a b) R f).1) :
    glReindex hcast (transportedAbsorbedGauge B hB R f Z a' b') =
      transportedAbsorbedGauge B hB R f Z a b := by
  subst ha
  subst hb
  exact glReindex_self hcast _

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

Unlike `exists_edgeAbsorbed_torus_rectangle`, whose per-edge witnesses are chosen independently,
here every edge of each orientation class receives the orientation-adapted absorbing gauge of
the *transported* reference witness: one horizontal reference gauge and one vertical reference
gauge, carried along the unique translation reaching the edge.  The translation covariance is
exactly the determinism of this construction.

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
    (hxhw : xhStart + 5 < width) (hyhh : yhStart + 5 < height)
    (hxhw' : xhStart + 7 ≤ width) (hyhh' : yhStart + 7 ≤ height)
    (hxv0 : 2 ≤ xvStart) (hyv0 : 2 ≤ yvStart)
    (hxvw : xvStart + 5 < width) (hyvh : yvStart + 5 < height)
    (hxvw' : xvStart + 7 ≤ width) (hyvh' : yvStart + 7 ≤ height)
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
    exists_horizontalReferenceEdgeGauge_coeff hAr hBr hUA hUB hxh0 hyh0 hxhw hyhh hxhw' hyhh'
      hbd hAB hd hposA hposB
  obtain ⟨hEv, Zv, hZv⟩ :=
    exists_verticalReferenceEdgeGauge_coeff hAr hBr hUA hUB hxv0 hyv0 hxvw hyvh hxvw' hyvh'
      hbd hAB hd hposA hposB
  -- The reference regions and their distinguished boundary edges.
  set Rh := (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw' hyhh').red with hRhdef
  set fh := singleBoundaryEdge (G := torusGraph width height) A Rh
    (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw' hyhh').blue
    (torusHorizontalReferenceEdge xhStart yhStart)
    (fun g => isCrossingEdge_torusHorizontalRectangleBlockingDatum A hAr hUA hxh0 hyh0 hxhw
      hyhh hxhw' hyhh' g) with hfhdef
  set Rv := (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw' hyvh').red with hRvdef
  set fv := singleBoundaryEdge (G := torusGraph width height) A Rv
    (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw' hyvh').blue
    (torusVerticalReferenceEdge xvStart yvStart)
    (fun g => isCrossingEdge_torusVerticalRectangleBlockingDatum A hAr hUA hxv0 hyv0 hxvw
      hyvh hxvw' hyvh' g) with hfvdef
  -- The constructed family: at each edge, the absorbing gauge of the transported reference
  -- witness of its orientation class, along the chosen translation reaching the edge.
  set X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ := fun e =>
    if he : IsHorizontalTorusEdge e then
      glReindex
        (congrArg B.bondDim
          (translate_horizontalReferenceEdge (xStart := xhStart) (yStart := yhStart) he).2.symm)
        (transportedAbsorbedGauge B hB Rh fh Zh
          (translate_horizontalReferenceEdge (xStart := xhStart) (yStart := yhStart) he).1.1
          (translate_horizontalReferenceEdge (xStart := xhStart) (yStart := yhStart) he).1.2)
    else
      glReindex
        (congrArg B.bondDim
          (translate_verticalReferenceEdge (xStart := xvStart) (yStart := yvStart)
            ((torusEdge_horizontal_or_vertical e).resolve_left he)).2.symm)
        (transportedAbsorbedGauge B hB Rv fv Zv
          (translate_verticalReferenceEdge (xStart := xvStart) (yStart := yvStart)
            ((torusEdge_horizontal_or_vertical e).resolve_left he)).1.1
          (translate_verticalReferenceEdge (xStart := xvStart) (yStart := yvStart)
            ((torusEdge_horizontal_or_vertical e).resolve_left he)).1.2)
    with hXdef
  -- The family at any translate of the horizontal reference edge is the transported absorbing
  -- gauge of that translate: the chosen translation agrees with the given one by rigidity.
  have hUh : ∀ (a : ZMod width) (b : ZMod height),
      X (Edge.map (translate a b) (torusHorizontalReferenceEdge xhStart yhStart)) =
        transportedAbsorbedGauge B hB Rh fh Zh a b := by
    intro a b
    have hhor : IsHorizontalTorusEdge
        (Edge.map (translate a b) (torusHorizontalReferenceEdge xhStart yhStart)) := by
      rw [← translateEdge_eq_map]
      exact translateEdge_isHorizontal a b
        (isHorizontalTorusEdge_torusHorizontalReferenceEdge xhStart yhStart)
    rw [hXdef]
    simp only
    rw [dif_pos hhor]
    generalize translate_horizontalReferenceEdge (xStart := xhStart) (yStart := yhStart) hhor
      = pq
    obtain ⟨⟨a', b'⟩, hspec⟩ := pq
    have hmap : Edge.map (translate a' b') (torusHorizontalReferenceEdge xhStart yhStart) =
        Edge.map (translate a b) (torusHorizontalReferenceEdge xhStart yhStart) := hspec.symm
    obtain ⟨ha, hb⟩ := translate_param_unique_right hw _ hmap
    exact glReindex_transportedAbsorbedGauge_eq B hB Rh fh Zh ha hb _
  have hUv : ∀ (a : ZMod width) (b : ZMod height),
      X (Edge.map (translate a b) (torusVerticalReferenceEdge xvStart yvStart)) =
        transportedAbsorbedGauge B hB Rv fv Zv a b := by
    intro a b
    have hver : IsVerticalTorusEdge
        (Edge.map (translate a b) (torusVerticalReferenceEdge xvStart yvStart)) := by
      rw [← translateEdge_eq_map]
      exact translateEdge_isVertical a b
        (isVerticalTorusEdge_torusVerticalReferenceEdge xvStart yvStart)
    have hnh : ¬ IsHorizontalTorusEdge
        (Edge.map (translate a b) (torusVerticalReferenceEdge xvStart yvStart)) := fun hcon =>
      torusEdge_not_horizontal_and_vertical _ ⟨hcon, hver⟩
    rw [hXdef]
    simp only
    rw [dif_neg hnh]
    generalize translate_verticalReferenceEdge (xStart := xvStart) (yStart := yvStart)
      ((torusEdge_horizontal_or_vertical _).resolve_left hnh) = pq
    obtain ⟨⟨a', b'⟩, hspec⟩ := pq
    have hmap : Edge.map (translate a' b') (torusVerticalReferenceEdge xvStart yvStart) =
        Edge.map (translate a b) (torusVerticalReferenceEdge xvStart yvStart) := hspec.symm
    obtain ⟨ha, hb⟩ := translate_param_unique_up hh _ hmap
    exact glReindex_transportedAbsorbedGauge_eq B hB Rv fv Zv ha hb _
  -- The two reference boundary edges have their first stored endpoint in the reference region.
  have hmemh : fh.1.1.1 ∈ Rh :=
    (torusHorizontalRectangleBlockingDatum hAr hUA hxh0 hyh0 hxhw' hyhh').left_mem_red
  have hmemv : fv.1.1.1 ∈ Rv :=
    (torusVerticalRectangleBlockingDatum hAr hUA hxv0 hyv0 hxvw' hyvh').left_mem_red
  refine ⟨X, ?_, ?_⟩
  · -- Translation covariance.
    intro a b e
    rcases torusEdge_horizontal_or_vertical e with he | he
    · obtain ⟨⟨a₀, b₀⟩, rfl⟩ :=
        translate_horizontalReferenceEdge (xStart := xhStart) (yStart := yhStart) he
      rw [translateEdge_translateEdge]
      intro h
      rw [hUh a₀ b₀, hUh (a₀ + a) (b₀ + b)]
      exact transportedAbsorbedGauge_translate_pair B hB Rh fh Zh hmemh a₀ (a₀ + a) a b₀
        (b₀ + b) b (by apply Prod.ext <;> simp <;> ring) (by apply Prod.ext <;> simp <;> ring) h
    · obtain ⟨⟨a₀, b₀⟩, rfl⟩ :=
        translate_verticalReferenceEdge (xStart := xvStart) (yStart := yvStart) he
      rw [translateEdge_translateEdge]
      intro h
      rw [hUv a₀ b₀, hUv (a₀ + a) (b₀ + b)]
      exact transportedAbsorbedGauge_translate_pair B hB Rv fv Zv hmemv a₀ (a₀ + a) a b₀
        (b₀ + b) b (by apply Prod.ext <;> simp <;> ring) (by apply Prod.ext <;> simp <;> ring) h
  · -- The bare-edge absorbed equality at every edge.
    intro e σ N
    rcases torusEdge_horizontal_or_vertical e with he | he
    · obtain ⟨⟨a, b⟩, rfl⟩ :=
        translate_horizontalReferenceEdge (xStart := xhStart) (yStart := yhStart) he
      -- `B`'s reference region block and host block are injective.
      have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B Rh := by
        have hi := hBr.horizontalEdgeRed_injective (xStart := xhStart) (yStart := yhStart)
          (by omega) (by omega)
        rwa [regionInjectivityDataOf_isInjective] at hi
      have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
          (Finset.univ \ Rh) :=
        regionBlockedTensorInjective_host
          (torusHorizontalRectangleBlockingDatum hBr hUB hxh0 hyh0 hxhw' hyhh') hUB
      have hEX : A.bondDim (boundaryEdgeMap (translate a b) Rh fh).1 =
          B.bondDim (boundaryEdgeMap (translate a b) Rh fh).1 :=
        (bondDim_boundaryEdgeMap_translate hA a b Rh fh).trans
          (hEh.trans (bondDim_boundaryEdgeMap_translate hB a b Rh fh).symm)
      refine edgeAbsorbed_of_edgeCoeffIdentityWitness
        (edgeCoeffIdentityWitness_translate hA hB a b Rh fh hEh Zh hposB hRB hCB hZh
          (glReindex (bondDim_boundaryEdgeMap_translate hB a b Rh fh).symm Zh) hEX ?_)
        hbd X (hUh a b) hposA σ N
      intro M σ' τ'
      obtain ⟨σ₀, τ₀, rfl, rfl⟩ :=
        exists_regionPhysicalConfig_translate_preimage (d := d) a b Rh σ' τ'
      exact regionInsertedCoeff_translate_coeffIdentity_conj hA hB a b Rh fh hEh Zh hZh
        hEX (glReindex (bondDim_boundaryEdgeMap_translate hB a b Rh fh).symm Zh) rfl M σ₀ τ₀
    · obtain ⟨⟨a, b⟩, rfl⟩ :=
        translate_verticalReferenceEdge (xStart := xvStart) (yStart := yvStart) he
      have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B Rv := by
        have hi := hBr.verticalEdgeRed_injective (xStart := xvStart) (yStart := yvStart)
          (by omega) (by omega)
        rwa [regionInjectivityDataOf_isInjective] at hi
      have hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
          (Finset.univ \ Rv) :=
        regionBlockedTensorInjective_host
          (torusVerticalRectangleBlockingDatum hBr hUB hxv0 hyv0 hxvw' hyvh') hUB
      have hEX : A.bondDim (boundaryEdgeMap (translate a b) Rv fv).1 =
          B.bondDim (boundaryEdgeMap (translate a b) Rv fv).1 :=
        (bondDim_boundaryEdgeMap_translate hA a b Rv fv).trans
          (hEv.trans (bondDim_boundaryEdgeMap_translate hB a b Rv fv).symm)
      refine edgeAbsorbed_of_edgeCoeffIdentityWitness
        (edgeCoeffIdentityWitness_translate hA hB a b Rv fv hEv Zv hposB hRB hCB hZv
          (glReindex (bondDim_boundaryEdgeMap_translate hB a b Rv fv).symm Zv) hEX ?_)
        hbd X (hUv a b) hposA σ N
      intro M σ' τ'
      obtain ⟨σ₀, τ₀, rfl, rfl⟩ :=
        exists_regionPhysicalConfig_translate_preimage (d := d) a b Rv σ' τ'
      exact regionInsertedCoeff_translate_coeffIdentity_conj hA hB a b Rv fv hEv Zv hZv
        hEX (glReindex (bondDim_boundaryEdgeMap_translate hB a b Rv fv).symm Zv) rfl M σ₀ τ₀

end PEPS
end TNLean
