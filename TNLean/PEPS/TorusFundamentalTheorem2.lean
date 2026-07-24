/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusFundamentalTheorem
import TNLean.PEPS.NormalSquareInjectivity
import TNLean.PEPS.TorusCovariantAbsorbedFamily
import TNLean.PEPS.TorusGaugedWeightCovariance
import TNLean.PEPS.TorusCornerRegion
import TNLean.PEPS.RegionBlock.ReindexInjectivity
import TNLean.PEPS.NormalBondDimension

/-!
# The unconditional normal PEPS Fundamental Theorem on the torus

This file proves the torus Fundamental Theorem with no conditional per-vertex hypothesis: from
the source hypotheses alone --- translation
invariance, positive bonds, the same state, the
rectangular-injectivity hypotheses (the union closure of injective regions is derived from the
positive bonds, and the bond-dimension equality from the rectangular-injectivity hypotheses
via `bondDim_eq_of_normalTorusRectangle`), and the source's own sizes `n, m ≥ 7` --- it
produces a per-edge gauge family
`X` and a single scalar `λ` with

* the translation covariance of `X` (the faithful torus form of the source's *"the same matrix
  on all horizontal (vertical) edges"*, with the wraparound endpoint swap of the ordered edge
  convention accounted for),
* the bare-edge absorbed equality at every edge,
* the per-vertex relation `A_v = λ · (gauge action of B at v)` at every torus vertex, and
* the scalar condition `λ^{width·height} = 1`

(arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1471 of
`Papers/1804.04964/paper_normal.tex`).

The production: the translation-covariant absorbed gauge family
(`exists_torusCovariantAbsorbedGaugeFamily`) supplies `X` with the bare-edge absorbed equality;
the comparison at the corner region and its insert-completed square
(`twoBlockProportional_of_edgeAbsorbed`) supplies two proportionality scalars `c_R`, `c_S`;
translation covariance transports both proportionalities to every translate with the *same*
scalars (`twoBlockScalarProportional_translate`), so the inserted-site scalar extraction
(`component_eq_gaugeVertex_of_twoBlockProportional`) yields the per-vertex relation with the
single ratio `λ = c_S / c_R` at every vertex; the scalar condition follows from
`lambda_pow_card_torus_eq_one`.

The conclusion does not assert that `X` is lexicographically one matrix per orientation class up
to scalars: the ordered edge convention stores a wraparound edge with its endpoints swapped, so
the absorbing family carries the transposed inverse of the class matrix on the seam edges and is
*not* one matrix per class up to scalars in that convention (see
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, section "Closure on the torus").  The
translation covariance conjunct is the orientation-faithful statement of the source's
uniformity.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1471 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- The vertex image of a translated region inserts the translated vertex. -/
theorem Region_map_insert (a : ZMod width) (b : ZMod height)
    (v : TorusVertex width height) (R : Finset (TorusVertex width height)) :
    Region.map (translate a b) (insert v R) =
      insert (translate a b v) (Region.map (translate a b) R) :=
  Finset.map_insert _ _ _

/-- Blocked-region injectivity of a translation-invariant tensor transports to every translated
region. -/
theorem regionBlockedTensorInjective_translate {T : Tensor (torusGraph width height) d}
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height))
    (h : RegionBlockedTensorInjective (G := torusGraph width height) T R) :
    RegionBlockedTensorInjective (G := torusGraph width height) T
      (Region.map (translate a b) R) := by
  have htr := (regionBlockedTensorInjective_transport T (translate a b) R).mpr h
  rwa [hT a b] at htr

/-- **The per-vertex gauge relation from the corner-region comparison.**

For a translation-invariant pair with a translation-covariant gauge family, the two comparison
proportionalities at the corner region and its insert-completed square transport to every
vertex's translate with the same scalars, so the inserted-site scalar extraction yields the
per-vertex relation `A_v = (c_S/c_R) · (gauge action of B at v)` with one ratio at every torus
vertex.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem component_eq_gaugeVertex_of_cornerProportional
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    {X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ}
    (hXcov : IsTranslationCovariantGaugeFamily B X)
    (hbond : A.bondDim = B.bondDim)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hw : 7 ≤ width) (hh : 7 ≤ height) {cR cS : ℂ} (hcR0 : cR ≠ 0)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B cornerRegion)
    (hcRprop : TwoBlockScalarProportional.{0, 0, 0, 0}
      (regionTwoBlock (G := torusGraph width height) A cornerRegion)
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbond)
        cornerRegion) cR)
    (hcSprop : TwoBlockScalarProportional.{0, 0, 0, 0}
      (regionTwoBlock (G := torusGraph width height) A
        (insert (cornerVertex : TorusVertex width height) cornerRegion))
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbond)
        (insert (cornerVertex : TorusVertex width height) cornerRegion)) cS)
    (v : TorusVertex width height)
    (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
    (σ : Fin d) :
    A.component v η σ =
      (cS / cR) * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ := by
  -- The translation carrying the corner vertex to `v`.
  set a := v.1 - ((2 : ℕ) : ZMod width) with hadef
  set b := v.2 - ((2 : ℕ) : ZMod height) with hbdef
  have hvmap : translate a b (cornerVertex : TorusVertex width height) = v := by
    apply Prod.ext
    · rw [hadef]
      simp [cornerVertex]
    · rw [hbdef]
      simp [cornerVertex]
  -- The vertex lies outside the translated corner region.
  have hvR : v ∉ Region.map (translate a b) cornerRegion := by
    rw [← hvmap, mem_Region_map_apply]
    exact cornerVertex_notMem_cornerRegion hw hh
  -- The reindexed gauge-absorbed tensor is injective on the translated corner region.
  have hRC_v : RegionBlockedTensorInjective (G := torusGraph width height)
      (reindexTensor (G := torusGraph width height) (applyGauge B X) hbond)
      (Region.map (translate a b) cornerRegion) :=
    regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond _
      (regionBlockedTensorInjective_applyGauge B X _
        (regionBlockedTensorInjective_translate hB a b cornerRegion hRB))
  -- The two transported proportionalities, with the base scalars.
  have hRprop_v := twoBlockScalarProportional_translate hA hB hXcov hbond a b
    cornerRegion hcRprop
  have hSprop_v := twoBlockScalarProportional_translate hA hB hXcov hbond a b
    (insert (cornerVertex : TorusVertex width height) cornerRegion) hcSprop
  rw [Region_map_insert a b cornerVertex cornerRegion, hvmap] at hSprop_v
  -- The inserted-site scalar extraction at `v`.
  exact component_eq_gaugeVertex_of_twoBlockProportional A B
    (Region.map (translate a b) cornerRegion) hvR hbond X cR cS hcR0 hposA hRC_v
    hRprop_v hSprop_v η σ

/-- **Equal bond dimensions from normal torus rectangular injectivity.**

From the source's rectangular-injectivity hypotheses on the torus, together with translation
invariance, the same state, and positive bond dimensions, the two tensors have equal bond
dimensions on every edge.  The bond-dimension equality is derived from the one-edge blocking
data built from the rectangular injectivity (the source's Lemma `inj_isomorph`, lines 560--583
of `Papers/1804.04964/paper_normal.tex`), not assumed.

Source: arXiv:1804.04964, Section 3, lines 560--583 and 1407--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_eq_of_normalTorusRectangle
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hw : 7 ≤ width) (hh : 7 ≤ height)
    (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    A.bondDim = B.bondDim := by
  set xStart := width - 5 with hxStart_def
  set yStart := height - 5 with hyStart_def
  have hx0h : 2 ≤ xStart := by omega
  have hy0h : 1 ≤ yStart := by omega
  have hx0v : 1 ≤ xStart := by omega
  have hy0v : 2 ≤ yStart := by omega
  have hx_seam : xStart + 5 = width ∨ xStart + 7 ≤ width := Or.inl (by omega)
  have hy_seam : yStart + 5 = height ∨ yStart + 7 ≤ height := Or.inl (by omega)
  -- Reference edges
  let eh : Edge (torusGraph width height) := torusHorizontalReferenceEdge xStart yStart
  let ev : Edge (torusGraph width height) := torusVerticalReferenceEdge xStart yStart
  -- The reference coordinates
  set xref : ZMod width := ((xStart + 1 : ℕ) : ZMod width) with hxref
  set yref : ZMod height := ((yStart + 2 : ℕ) : ZMod height) with hyref
  have heh_eq : eh = torusRightEdge (xref, yref) := by
    dsimp [eh, torusHorizontalReferenceEdge, xref, yref]
  set xvref : ZMod width := ((xStart + 2 : ℕ) : ZMod width) with hxvref
  set yvref : ZMod height := ((yStart + 1 : ℕ) : ZMod height) with hyvref
  have hev_eq : ev = torusUpEdge (xvref, yvref) := by
    dsimp [ev, torusVerticalReferenceEdge, xvref, yvref]
  -- Blocking data at the horizontal reference edge
  let DAh := torusHorizontalRectangleBlockingDatum hAr hUA hx0h hy0h hx_seam hy_seam
  let DBh := torusHorizontalRectangleBlockingDatum hBr hUB hx0h hy0h hx_seam hy_seam
  have hredh : DAh.red = DBh.red := rfl
  have hblueh : DAh.blue = DBh.blue := rfl
  have hsingleh := isCrossingEdge_torusHorizontalRectangleBlockingDatum
    A hAr hUA hx0h hy0h hx_seam hy_seam
  have hbond_eh : A.bondDim eh = B.bondDim eh :=
    bondDim_apply_eq_of_blockingData DAh DBh hredh hblueh hAB hd hposA hposB hsingleh
  -- Blocking data at the vertical reference edge
  let DAv := torusVerticalRectangleBlockingDatum hAr hUA hx0v hy0v hx_seam hy_seam
  let DBv := torusVerticalRectangleBlockingDatum hBr hUB hx0v hy0v hx_seam hy_seam
  have hredv : DAv.red = DBv.red := rfl
  have hbluev : DAv.blue = DBv.blue := rfl
  have hsinglev := isCrossingEdge_torusVerticalRectangleBlockingDatum
    A hAr hUA hx0v hy0v hx_seam hy_seam
  have hbond_ev : A.bondDim ev = B.bondDim ev :=
    bondDim_apply_eq_of_blockingData DAv DBv hredv hbluev hAB hd hposA hposB hsinglev
  -- Extend to all edges via translation invariance
  funext e
  rcases torusEdge_horizontal_or_vertical e with (hhoriz | hvert)
  · -- e is horizontal: e = torusRightEdge p for some p
    obtain ⟨p, hp⟩ := isHorizontalTorusEdge_eq_rightEdge hhoriz
    subst hp
    have htransA : A.bondDim (torusRightEdge p) = A.bondDim eh := by
      calc
        A.bondDim (torusRightEdge p) = A.bondDim (
            translateEdge (p.1 - xref) (p.2 - yref) (torusRightEdge (xref, yref))) := by
          rw [translateEdge_torusRightEdge (p.1 - xref) (p.2 - yref) (xref, yref)]
          simp [sub_add_cancel]
        _ = A.bondDim (torusRightEdge (xref, yref)) :=
          bondDim_translateEdge_of_translationInvariant hA _ _ _
        _ = A.bondDim eh := by rw [← heh_eq]
    have htransB : B.bondDim (torusRightEdge p) = B.bondDim eh := by
      calc
        B.bondDim (torusRightEdge p) = B.bondDim (
            translateEdge (p.1 - xref) (p.2 - yref) (torusRightEdge (xref, yref))) := by
          rw [translateEdge_torusRightEdge (p.1 - xref) (p.2 - yref) (xref, yref)]
          simp [sub_add_cancel]
        _ = B.bondDim (torusRightEdge (xref, yref)) :=
          bondDim_translateEdge_of_translationInvariant hB _ _ _
        _ = B.bondDim eh := by rw [← heh_eq]
    rw [htransA, htransB, hbond_eh]
  · -- e is vertical: e = torusUpEdge p for some p
    obtain ⟨p, hp⟩ := isVerticalTorusEdge_eq_upEdge hvert
    subst hp
    have htransA : A.bondDim (torusUpEdge p) = A.bondDim ev := by
      calc
        A.bondDim (torusUpEdge p) = A.bondDim (
            translateEdge (p.1 - xvref) (p.2 - yvref) (torusUpEdge (xvref, yvref))) := by
          rw [translateEdge_torusUpEdge (p.1 - xvref) (p.2 - yvref) (xvref, yvref)]
          simp [sub_add_cancel]
        _ = A.bondDim (torusUpEdge (xvref, yvref)) :=
          bondDim_translateEdge_of_translationInvariant hA _ _ _
        _ = A.bondDim ev := by rw [← hev_eq]
    have htransB : B.bondDim (torusUpEdge p) = B.bondDim ev := by
      calc
        B.bondDim (torusUpEdge p) = B.bondDim (
            translateEdge (p.1 - xvref) (p.2 - yvref) (torusUpEdge (xvref, yvref))) := by
          rw [translateEdge_torusUpEdge (p.1 - xvref) (p.2 - yvref) (xvref, yvref)]
          simp [sub_add_cancel]
        _ = B.bondDim (torusUpEdge (xvref, yvref)) :=
          bondDim_translateEdge_of_translationInvariant hB _ _ _
        _ = B.bondDim ev := by rw [← hev_eq]
    rw [htransA, htransB, hbond_ev]

/-- **Unconditional normal PEPS Fundamental Theorem on the torus.**

For a translation-invariant pair `A`, `B` on the discrete `n × m` torus with `n, m ≥ 7` (the
source's own sizes), positive bonds, the same state, and both
satisfying the rectangular-injectivity hypotheses,
the bond dimensions of `A` and `B` agree on every edge and
there are a translation-covariant per-edge gauge family `X` realizing the
bare-edge absorbed equality at every edge, and a single scalar `λ` with the per-vertex relation
`A_v = λ · (gauge action of B at v)` at every torus vertex and `λ^{width·height} = 1`.  The
union closure of injective regions is derived from the positive bonds
(`regionInjectivityUnionClosure_of_overlap`), and the bond-dimension equality is derived
from the rectangular injectivity hypotheses (`bondDim_eq_of_normalTorusRectangle`); neither
is assumed.

This is the torus form of Theorem 3 (arXiv:1804.04964, Section 3, lines 1453--1471 of
`Papers/1804.04964/paper_normal.tex`): `B = λ · (X, Y\text{-action on } A)` with
`λ^{n·m} = 1`, with no conditional per-vertex hypothesis.  The single `λ` is produced by
transporting the corner-region comparison to every vertex along the translations; the
translation covariance of the gauge family is what makes the transported comparison scalars
agree.  The reference blockings are anchored at `(width - 5, height - 5)`, touching the seam on
the right and top, which is what packs them into every torus with `n, m ≥ 7`; the source packs
its example regions into a `7 × 7` torus through complement regions that wrap the seam, which
the wraparound-free rectangle covers here avoid.

The gauge family is characterized here by its translation covariance rather than by a
lexicographic one-matrix-per-class predicate: the ordered edge
convention stores a wraparound edge with swapped endpoints, so the absorbing family carries the
transposed inverse of the class matrix on the seam edges, which a lexicographically uniform
family cannot describe (see `docs/paper-gaps/peps_normal_ft_section3_route.tex`, section
"Closure on the torus").

Source: arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1471 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalTorusPEPS_unconditional
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hw : 7 ≤ width) (hh : 7 ≤ height)
    (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g) :
    ∃ (hbond : A.bondDim = B.bondDim)
        (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ),
      IsTranslationCovariantGaugeFamily B X ∧
      (∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff (G := torusGraph width height) A e σ N =
          edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
            (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N)) ∧
      ∃ lam : ℂ,
        (∀ (v : TorusVertex width height)
          (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
          (σ : Fin d),
          A.component v η σ =
            lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ) ∧
        lam ^ (width * height) = 1 := by
  classical
  -- The union closure of injective regions, from positive bonds.
  have hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A) :=
    regionInjectivityUnionClosure_of_overlap A hposA
  have hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B) :=
    regionInjectivityUnionClosure_of_overlap B hposB
  -- The bond-dimension equality, from the rectangular injectivity hypotheses.
  have hbond : A.bondDim = B.bondDim :=
    bondDim_eq_of_normalTorusRectangle hA hB hAr hBr hUA hUB hw hh hAB hd hposA hposB
  -- The translation-covariant absorbed gauge family, at the seam-touching reference anchors.
  obtain ⟨X, hXcov, hedge⟩ := exists_torusCovariantAbsorbedGaugeFamily
    (xhStart := width - 5) (yhStart := height - 5) (xvStart := width - 5) (yvStart := height - 5)
    hA hB hAr hBr hUA hUB (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) hbond hAB hd hposA hposB
  -- The base injectivity facts at the corner region and its insert-completed square, for `A`.
  have hRA : RegionBlockedTensorInjective (G := torusGraph width height) A cornerRegion := by
    have hi := hAr.cornerRegion_injective hUA hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hSA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (insert (cornerVertex : TorusVertex width height) cornerRegion) := by
    rw [insert_cornerVertex_cornerRegion hw hh]
    have hi := hAr.cornerSquare_injective hUA hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCRA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ cornerRegion) := by
    have hi := hAr.compl_cornerRegion_injective hUA hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCSA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (Finset.univ \ insert (cornerVertex : TorusVertex width height) cornerRegion) := by
    rw [insert_cornerVertex_cornerRegion hw hh]
    have hi := hAr.compl_cornerSquare_injective hUA hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  -- The same base facts for `B`, lifted through the gauge and the bond-dimension reindex.
  have liftC : ∀ R : Finset (TorusVertex width height),
      RegionBlockedTensorInjective (G := torusGraph width height) B R →
      RegionBlockedTensorInjective (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbond) R := fun R hRB =>
    regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond R
      (regionBlockedTensorInjective_applyGauge B X R hRB)
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B cornerRegion := by
    have hi := hBr.cornerRegion_injective hUB hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hSB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (insert (cornerVertex : TorusVertex width height) cornerRegion) := by
    rw [insert_cornerVertex_cornerRegion hw hh]
    have hi := hBr.cornerSquare_injective hUB hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ cornerRegion) := by
    have hi := hBr.compl_cornerRegion_injective hUB hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCSB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ insert (cornerVertex : TorusVertex width height) cornerRegion) := by
    rw [insert_cornerVertex_cornerRegion hw hh]
    have hi := hBr.compl_cornerSquare_injective hUB hw hh
    rwa [regionInjectivityDataOf_isInjective] at hi
  -- Boundary edges of the two base comparison regions.
  haveI hNeR : Nonempty {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) cornerRegion f} :=
    ⟨⟨torusUpEdge cornerVertex, isRegionBoundaryEdge_cornerRegion hw hh⟩⟩
  haveI hNeS : Nonempty {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height)
        (insert (cornerVertex : TorusVertex width height) cornerRegion) f} := by
    rw [insert_cornerVertex_cornerRegion hw hh]
    exact ⟨⟨torusUpEdge belowCornerVertex, isRegionBoundaryEdge_cornerSquare hw hh⟩⟩
  -- The two base comparison proportionalities.
  obtain ⟨cR, hcR0, hcRprop⟩ := twoBlockProportional_of_edgeAbsorbed A B hbond X cornerRegion
    hRA hCRA (liftC _ hRB) (liftC _ hCRB) hedge
  obtain ⟨cS, hcS0, hcSprop⟩ := twoBlockProportional_of_edgeAbsorbed A B hbond X
    (insert (cornerVertex : TorusVertex width height) cornerRegion)
    hSA hCSA (liftC _ hSB) (liftC _ hCSB) hedge
  -- The per-vertex relation with the single ratio `λ = c_S / c_R`.
  have hPV := component_eq_gaugeVertex_of_cornerProportional hA hB hXcov hbond hposA hw hh
    hcR0 hRB hcRprop hcSprop
  exact ⟨hbond, X, hXcov, hedge, cS / cR, hPV,
    lambda_pow_card_torus_eq_one A B cornerRegion hRA hCRA hposA hAB X hbond (cS / cR) hPV⟩

end PEPS
end TNLean
