/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusAbsorbedCovariance
import TNLean.PEPS.TorusEdgeAbsorbed

/-!
# A covariant absorbed gauge family from two reference witnesses

A horizontal and a vertical distinguished-edge coefficient witness are propagated
by translations. The resulting absorbed edge gauges are translation covariant,
including the transposed inverse when a translation reverses the stored endpoint
order. The witnessing regions need not be rectangles.

This auxiliary construction separates witness propagation from the geometric
construction of witnesses in arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1449--1544 of `Papers/1804.04964/paper_normal.tex`.
-/

open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

private noncomputable def translate_rightEdge_from (p : TorusVertex width height)
    {e : Edge (torusGraph width height)} (he : IsHorizontalTorusEdge e) :
    {ab : ZMod width × ZMod height // e = Edge.map (translate ab.1 ab.2) (torusRightEdge p)} :=
  ⟨((isHorizontalTorusEdge_eq_rightEdge he).choose.1 - p.1,
    (isHorizontalTorusEdge_eq_rightEdge he).choose.2 - p.2), by
    conv_lhs => rw [(isHorizontalTorusEdge_eq_rightEdge he).choose_spec]
    rw [← translateEdge_eq_map, translateEdge_torusRightEdge]
    congr 1
    apply Prod.ext <;> simp⟩

private noncomputable def translate_upEdge_from (p : TorusVertex width height)
    {e : Edge (torusGraph width height)} (he : IsVerticalTorusEdge e) :
    {ab : ZMod width × ZMod height // e = Edge.map (translate ab.1 ab.2) (torusUpEdge p)} :=
  ⟨((isVerticalTorusEdge_eq_upEdge he).choose.1 - p.1,
    (isVerticalTorusEdge_eq_upEdge he).choose.2 - p.2), by
    conv_lhs => rw [(isVerticalTorusEdge_eq_upEdge he).choose_spec]
    rw [← translateEdge_eq_map, translateEdge_torusUpEdge]
    congr 1
    apply Prod.ext <;> simp⟩

/-- The translated coefficient witness when its edge gauge is the transported reference gauge. -/
private noncomputable def transportedEdgeCoeffIdentityWitness
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (hE : A.bondDim f.1 = B.bondDim f.1)
    (Z : GL (Fin (B.bondDim f.1)) ℂ)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B R)
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B (Finset.univ \ R))
    (hid : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R)
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := torusGraph width height) A R f M σ τ =
        regionInsertedCoeff (G := torusGraph width height) B R f
          ((Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
            (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (hEX : A.bondDim (boundaryEdgeMap (translate a b) R f).1 =
      B.bondDim (boundaryEdgeMap (translate a b) R f).1) :
    EdgeCoeffIdentityWitness A B (boundaryEdgeMap (translate a b) R f).1
      (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z)
      (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z) hEX :=
  edgeCoeffIdentityWitness_translate hA hB a b R f hE Z hposB hRB hCB hid
    (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z) hEX (by
      intro M σ' τ'
      obtain ⟨σ, τ, rfl, rfl⟩ :=
        exists_regionPhysicalConfig_translate_preimage (d := d) a b R σ' τ'
      exact regionInsertedCoeff_translate_coeffIdentity_conj hA hB a b R f hE Z hid hEX
        (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z) rfl M σ τ)

private theorem exists_torusCovariantAbsorbedGaugeFamily_of_referenceWitnesses
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hw : 2 < width) (hh : 2 < height) (hbd : A.bondDim = B.bondDim)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (ph pv : TorusVertex width height)
    (Zh Zhref : GL (Fin (B.bondDim (torusRightEdge ph))) ℂ)
    (Zv Zvref : GL (Fin (B.bondDim (torusUpEdge pv))) ℂ)
    (wh : EdgeCoeffIdentityWitness A B (torusRightEdge ph) Zh Zhref (congr_fun hbd _))
    (wv : EdgeCoeffIdentityWitness A B (torusUpEdge pv) Zv Zvref (congr_fun hbd _))
    (hmemh : (torusRightEdge ph).1.1 ∈ wh.region)
    (hmemv : (torusUpEdge pv).1.1 ∈ wv.region) :
    ∃ X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ,
      IsTranslationCovariantGaugeFamily B X ∧
      ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N) := by
  classical
  let Rh := wh.region
  let Rv := wv.region
  let fh : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge Rh e} :=
    ⟨torusRightEdge ph, wh.isBoundary⟩
  let fv : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge Rv e} :=
    ⟨torusUpEdge pv, wv.isBoundary⟩
  let hEh := congr_fun hbd (torusRightEdge ph)
  let hEv := congr_fun hbd (torusUpEdge pv)
  -- The constructed family: at each edge, the absorbing gauge of the transported reference
  -- witness of its orientation class, along the chosen translation reaching the edge.
  set X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ := fun e =>
    if he : IsHorizontalTorusEdge e then
      glReindex
        (congrArg B.bondDim
          (translate_rightEdge_from ph he).2.symm)
        (transportedAbsorbedGauge B hB Rh fh Zh
          (translate_rightEdge_from ph he).1.1
          (translate_rightEdge_from ph he).1.2)
    else
      glReindex
        (congrArg B.bondDim
          (translate_upEdge_from pv
            ((torusEdge_horizontal_or_vertical e).resolve_left he)).2.symm)
        (transportedAbsorbedGauge B hB Rv fv Zv
          (translate_upEdge_from pv
            ((torusEdge_horizontal_or_vertical e).resolve_left he)).1.1
          (translate_upEdge_from pv
            ((torusEdge_horizontal_or_vertical e).resolve_left he)).1.2)
    with hXdef
  -- The family at any translate of the horizontal reference edge is the transported absorbing
  -- gauge of that translate: the chosen translation agrees with the given one by rigidity.
  have hUh : ∀ (a : ZMod width) (b : ZMod height),
      X (Edge.map (translate a b) (torusRightEdge ph)) =
        transportedAbsorbedGauge B hB Rh fh Zh a b := by
    intro a b
    have hhor : IsHorizontalTorusEdge
        (Edge.map (translate a b) (torusRightEdge ph)) := by
      rw [← translateEdge_eq_map]
      exact translateEdge_isHorizontal a b
        (isHorizontalTorusEdge_torusRightEdge ph)
    rw [hXdef]
    simp only
    rw [dite_eq_left hhor]
    generalize translate_rightEdge_from ph hhor
      = pq
    obtain ⟨⟨a', b'⟩, hspec⟩ := pq
    have hmap : Edge.map (translate a' b') (torusRightEdge ph) =
        Edge.map (translate a b) (torusRightEdge ph) := hspec.symm
    obtain ⟨ha, hb⟩ := translate_param_unique_right hw _ hmap
    subst a'
    subst b'
    exact glReindex_self _ _
  have hUv : ∀ (a : ZMod width) (b : ZMod height),
      X (Edge.map (translate a b) (torusUpEdge pv)) =
        transportedAbsorbedGauge B hB Rv fv Zv a b := by
    intro a b
    have hver : IsVerticalTorusEdge
        (Edge.map (translate a b) (torusUpEdge pv)) := by
      rw [← translateEdge_eq_map]
      exact translateEdge_isVertical a b
        (isVerticalTorusEdge_torusUpEdge pv)
    have hnh : ¬ IsHorizontalTorusEdge
        (Edge.map (translate a b) (torusUpEdge pv)) := fun hcon =>
      torusEdge_not_horizontal_and_vertical _ ⟨hcon, hver⟩
    rw [hXdef]
    simp only
    rw [dite_eq_right hnh]
    generalize translate_upEdge_from pv
      ((torusEdge_horizontal_or_vertical _).resolve_left hnh) = pq
    obtain ⟨⟨a', b'⟩, hspec⟩ := pq
    have hmap : Edge.map (translate a' b') (torusUpEdge pv) =
        Edge.map (translate a b) (torusUpEdge pv) := hspec.symm
    obtain ⟨ha, hb⟩ := translate_param_unique_up hh _ hmap
    subst a'
    subst b'
    exact glReindex_self _ _
  refine ⟨X, ?_, ?_⟩
  · -- Translation covariance.
    intro a b e
    rcases torusEdge_horizontal_or_vertical e with he | he
    · obtain ⟨⟨a₀, b₀⟩, rfl⟩ :=
        translate_rightEdge_from ph he
      rw [translateEdge_translateEdge]
      intro h
      rw [hUh a₀ b₀, hUh (a₀ + a) (b₀ + b)]
      exact transportedAbsorbedGauge_translate_pair B hB Rh fh Zh hmemh a₀ (a₀ + a) a b₀
        (b₀ + b) b (by apply Prod.ext <;> simp <;> ring) (by apply Prod.ext <;> simp <;> ring) h
    · obtain ⟨⟨a₀, b₀⟩, rfl⟩ :=
        translate_upEdge_from pv he
      rw [translateEdge_translateEdge]
      intro h
      rw [hUv a₀ b₀, hUv (a₀ + a) (b₀ + b)]
      exact transportedAbsorbedGauge_translate_pair B hB Rv fv Zv hmemv a₀ (a₀ + a) a b₀
        (b₀ + b) b (by apply Prod.ext <;> simp <;> ring) (by apply Prod.ext <;> simp <;> ring) h
  · -- The bare-edge absorbed equality at every edge.
    intro e σ N
    rcases torusEdge_horizontal_or_vertical e with he | he
    · obtain ⟨⟨a, b⟩, rfl⟩ :=
        translate_rightEdge_from ph he
      have hEX : A.bondDim (boundaryEdgeMap (translate a b) Rh fh).1 =
          B.bondDim (boundaryEdgeMap (translate a b) Rh fh).1 :=
        (bondDim_boundaryEdgeMap_translate hA a b Rh fh).trans
          (hEh.trans (bondDim_boundaryEdgeMap_translate hB a b Rh fh).symm)
      refine edgeAbsorbed_of_edgeCoeffIdentityWitness
        (transportedEdgeCoeffIdentityWitness hA hB a b Rh fh hEh Zh wh.hposB
          wh.hRB wh.hCB wh.hidZ hEX)
        hbd X (hUh a b) hposA σ N
    · obtain ⟨⟨a, b⟩, rfl⟩ :=
        translate_upEdge_from pv he
      have hEX : A.bondDim (boundaryEdgeMap (translate a b) Rv fv).1 =
          B.bondDim (boundaryEdgeMap (translate a b) Rv fv).1 :=
        (bondDim_boundaryEdgeMap_translate hA a b Rv fv).trans
          (hEv.trans (bondDim_boundaryEdgeMap_translate hB a b Rv fv).symm)
      refine edgeAbsorbed_of_edgeCoeffIdentityWitness
        (transportedEdgeCoeffIdentityWitness hA hB a b Rv fv hEv Zv wv.hposB
          wv.hRB wv.hCB wv.hidZ hEX)
        hbd X (hUv a b) hposA σ N

/-- Two distinguished-edge coefficient witnesses determine a translation-covariant
absorbed gauge family. One distinguished edge is horizontal and the other vertical;
the first stored endpoint of each edge belongs to its witnessing region.

The statement assumes only the supplied witnesses, translation invariance, matched
bond dimensions, positive bonds of the first tensor, and torus side lengths greater
than two. No rectangular shape is imposed on either witnessing region.

This is the witness-propagation step of arXiv:1804.04964, Section 3, proof of
Theorem 3, lines 1449--1544 of `Papers/1804.04964/paper_normal.tex`. -/
theorem exists_torusCovariantAbsorbedGaugeFamily_of_edgeReferenceWitnesses
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hw : 2 < width) (hh : 2 < height) (hbd : A.bondDim = B.bondDim)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (eh ev : Edge (torusGraph width height))
    (heh : IsHorizontalTorusEdge eh) (hev : IsVerticalTorusEdge ev)
    (Zh Zhref : GL (Fin (B.bondDim eh)) ℂ) (Zv Zvref : GL (Fin (B.bondDim ev)) ℂ)
    (wh : EdgeCoeffIdentityWitness A B eh Zh Zhref (congr_fun hbd eh))
    (wv : EdgeCoeffIdentityWitness A B ev Zv Zvref (congr_fun hbd ev))
    (hmemh : eh.1.1 ∈ wh.region) (hmemv : ev.1.1 ∈ wv.region) :
    ∃ X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ,
      IsTranslationCovariantGaugeFamily B X ∧
      ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N) := by
  rcases isHorizontalTorusEdge_eq_rightEdge heh with ⟨ph, rfl⟩
  rcases isVerticalTorusEdge_eq_upEdge hev with ⟨pv, rfl⟩
  exact exists_torusCovariantAbsorbedGaugeFamily_of_referenceWitnesses
    hA hB hw hh hbd hposA ph pv Zh Zhref Zv Zvref wh wv hmemh hmemv

end TNLean.PEPS
