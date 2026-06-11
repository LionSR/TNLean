import TNLean.PEPS.TorusWitnessCapstone
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed

/-!
# The bare-edge absorbed equality at every torus edge

This file produces, from the torus rectangle-injectivity hypotheses, a single per-edge gauge family
`X` over the second tensor's bonds for which the *bare-edge absorbed equality* against
`applyGauge B X` holds at every edge of the discrete torus (arXiv:1804.04964, Section 3, proof of
Theorem 3, lines 1519--1544 of `Papers/1804.04964/paper_normal.tex`):

> `edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ (reindex N)`.

The per-edge gauge engine delivers, at every horizontal (vertical) edge `e`, an
`EdgeCoeffIdentityWitness` carrying a red blocking region `R_e` whose single boundary edge is `e`
and a *conjugation*-form coefficient identity realized by a per-edge gauge `Z_e`
(`exists_edgeCoeffIdentityWitness_horizontalFamily`,
`exists_edgeCoeffIdentityWitness_verticalFamily`).  The family `X` is built edgewise from those
witnesses by the orientation-adapted absorbing gauge `absorbedBoundaryGauge B R_e ⟨e,_⟩ Z_e`, and
the bare-edge absorbed equality at `e` follows from `edgeAbsorbed_of_conjIdentity`.  Because the
bare-edge identity at `e` depends only on the gauge `X e` (the open-edge gauge cancellation
`edgeInsertedCoeff_applyGauge`), the absorbing choice at each edge is independent of the others.

The orientation-uniformity of this absorbing family (that it is one horizontal matrix and one
vertical matrix up to per-edge scalars, the shape the torus Fundamental Theorem's gauge conclusion
asserts) is the remaining open piece recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The bare-edge absorbed equality from a single edge witness.**

If an edge `e` of the torus carries an `EdgeCoeffIdentityWitness` with per-edge gauge `Z`, then the
bare-edge absorbed equality holds at `e` against `applyGauge B X`, provided `X e` is the
orientation-adapted absorbing gauge `absorbedBoundaryGauge B w.region ⟨e, w.isBoundary⟩ Z` and
every bond dimension of `A` is positive.

The witness's conjugation-form coefficient identity (`EdgeCoeffIdentityWitness.hidZ`) is fed to
`edgeAbsorbed_of_conjIdentity`, which converts it to the absorbed region equality and cancels the
shared positive interior multiplicity to the bare-edge identity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeAbsorbed_of_edgeCoeffIdentityWitness
    {A B : Tensor (torusGraph width height) d} {e : Edge (torusGraph width height)}
    {Z Zref : GL (Fin (B.bondDim e)) ℂ} {hE : A.bondDim e = B.bondDim e}
    (w : EdgeCoeffIdentityWitness A B e Z Zref hE)
    (hbd : A.bondDim = B.bondDim)
    (X : (g : Edge (torusGraph width height)) → GL (Fin (B.bondDim g)) ℂ)
    (hXe : X e = absorbedBoundaryGauge (G := torusGraph width height) B w.region
      ⟨e, w.isBoundary⟩ Z)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (σ : TorusVertex width height → Fin d)
    (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := torusGraph width height) A e σ N =
      edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N) := by
  -- The witness's boundary edge is `⟨e, w.isBoundary⟩`; `hE` and `congr_fun hbd e` agree.
  have hEeq : hE = congr_fun hbd e := Subsingleton.elim _ _
  subst hEeq
  exact edgeAbsorbed_of_conjIdentity A B w.region ⟨e, w.isBoundary⟩ hbd Z X hXe hposA
    (fun M σ' τ' => w.hidZ M σ' τ') σ N

/-- **A gauge family with the bare-edge absorbed equality at every torus edge.**

For a translation-invariant pair `A`, `B` on the torus with matched bond dimensions, positive bonds,
the same state, and both satisfying the rectangular-injectivity hypotheses with union closure, there
is a per-edge gauge family `X` over the second tensor's bonds for which the bare-edge absorbed
equality against `applyGauge B X` holds at every edge: inserting `N` on `A`'s edge `e` matches
inserting the reindexed `N` on `applyGauge B X`'s edge `e`, for every global physical configuration
and every matrix.

The horizontal and vertical coefficient-identity witness families
(`exists_edgeCoeffIdentityWitness_horizontalFamily`,
`exists_edgeCoeffIdentityWitness_verticalFamily`) supply, at every edge, a witness whose
conjugation-form coefficient identity is converted to the bare-edge absorbed equality by
`edgeAbsorbed_of_edgeCoeffIdentityWitness`.  The family `X` is the per-edge orientation-adapted
absorbing gauge read off each chosen witness; the bare-edge identity at `e` depends only on `X e`,
so the per-edge absorbing choices are independent.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_edgeAbsorbed_torus_rectangle
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
      ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff (G := torusGraph width height) A e σ N =
          edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
            (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N) := by
  classical
  -- The two orientation-class witness families.
  have witH := exists_edgeCoeffIdentityWitness_horizontalFamily hA hB hAr hBr hUA hUB
    hxh0 hyh0 hxhw hyhh hxhw' hyhh' hbd hAB hd hposA hposB
  have witV := exists_edgeCoeffIdentityWitness_verticalFamily hA hB hAr hBr hUA hUB
    hxv0 hyv0 hxvw hyvh hxvw' hyvh' hbd hAB hd hposA hposB
  -- For every edge, a chosen gauge, reference gauge, bond-dimension equality, and a *nonempty*
  -- witness of the appropriate orientation class.
  have hwit : ∀ e : Edge (torusGraph width height),
      ∃ (Z Zref : GL (Fin (B.bondDim e)) ℂ) (hE : A.bondDim e = B.bondDim e),
        Nonempty (EdgeCoeffIdentityWitness A B e Z Zref hE) := by
    intro e
    rcases torusEdge_horizontal_or_vertical e with he | he
    · exact witH e he
    · exact witV e he
  -- The chosen per-edge gauge, reference gauge, bond-dimension equality, and nonempty witness.
  choose Z Zref hE hne using hwit
  -- A chosen witness at each edge.
  set w : (e : Edge (torusGraph width height)) →
      EdgeCoeffIdentityWitness A B e (Z e) (Zref e) (hE e) := fun e => (hne e).some with hwdef
  -- The absorbing family, read off each chosen witness.
  refine ⟨fun e => absorbedBoundaryGauge (G := torusGraph width height) B (w e).region
    ⟨e, (w e).isBoundary⟩ (Z e), fun e σ N => ?_⟩
  exact edgeAbsorbed_of_edgeCoeffIdentityWitness (w e) hbd
    (fun g => absorbedBoundaryGauge (G := torusGraph width height) B (w g).region
      ⟨g, (w g).isBoundary⟩ (Z g)) rfl hposA σ N

end PEPS
end TNLean
