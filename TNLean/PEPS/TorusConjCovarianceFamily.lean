import TNLean.PEPS.TorusEdgeGaugeCovariance
import TNLean.PEPS.TorusClassAgreement

/-!
# The conjugation covariance family from per-edge coefficient identities

The orientation-uniform selection on the torus consumes the conjugation covariance `hcovH`/`hcovV`
of `isTorusOrientationUniformGaugeFamilyModScalar_of_conjCovariance`: on every horizontal
(vertical) edge the conjugation by the per-edge gauge coincides with the conjugation by the
transported reference matrix.  This file assembles that covariance from the per-edge coefficient
identities, isolating the single remaining geometric obligation — producing the two matched
coefficient-identity families at every edge — as the hypotheses `hidX`/`hidRef`.

For a fixed orientation class, suppose on every edge `e` of the class there is a region `R e` with a
single boundary edge equal to `e`, the second tensor's region and complement blocked-tensor
injective, and two coefficient identities: one realized by the per-edge gauge `X e` and one by the
transported reference gauge.  Then the conjugations by `X e` and by the transported reference
coincide (`gaugeConj_eq_of_coeffIdentities_torus`), which is exactly `hcovH` (`hcovV`).  Gathering
the two classes through the selection gives the orientation-uniform-up-to-scalar family.

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

/-- The data realizing the conjugation covariance at one edge: a region whose single boundary edge
is `e`, the second tensor's region/complement injectivity, and a pair of coefficient identities
realized by the per-edge gauge and the reference gauge respectively.

Bundling these per edge isolates the geometric obligation (producing the identities) from the
algebraic determinacy that turns them into the conjugation covariance.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
structure EdgeCoeffIdentityWitness (A B : Tensor (torusGraph width height) d)
    (e : Edge (torusGraph width height))
    (Z Zref : GL (Fin (B.bondDim e)) ℂ) (hE : A.bondDim e = B.bondDim e) where
  /-- The region whose single boundary edge is `e`. -/
  region : Finset (TorusVertex width height)
  /-- `e` is a boundary edge of the region. -/
  isBoundary : IsRegionBoundaryEdge (G := torusGraph width height) region e
  /-- The second tensor's region block is blocked-tensor injective. -/
  hRB : RegionBlockedTensorInjective (G := torusGraph width height) B region
  /-- The second tensor's host block is blocked-tensor injective. -/
  hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
    (Finset.univ \ region)
  /-- The second tensor has positive bond dimensions. -/
  hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g
  /-- The per-edge gauge `Z` realizes the region-insertion coefficient identity by conjugation. -/
  hidZ : ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) region)
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ region)),
    regionInsertedCoeff (G := torusGraph width height) A region ⟨e, isBoundary⟩ M σ τ =
      regionInsertedCoeff (G := torusGraph width height) B region ⟨e, isBoundary⟩
        ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
          (↑Z⁻¹ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)) σ τ
  /-- The reference gauge `Zref` realizes the same coefficient identity by conjugation. -/
  hidZref : ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) region)
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ region)),
    regionInsertedCoeff (G := torusGraph width height) A region ⟨e, isBoundary⟩ M σ τ =
      regionInsertedCoeff (G := torusGraph width height) B region ⟨e, isBoundary⟩
        ((Zref : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
          (↑Zref⁻¹ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)) σ τ

/-- From an edge coefficient-identity witness, the per-edge gauge and the reference gauge induce the
same conjugation map on every bond matrix.

This is `gaugeConj_eq_of_coeffIdentities_torus` read off the bundled witness: it is the conjugation
covariance at one edge.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem gaugeConj_eq_of_edgeCoeffIdentityWitness
    {A B : Tensor (torusGraph width height) d}
    {e : Edge (torusGraph width height)}
    {Z Zref : GL (Fin (B.bondDim e)) ℂ} {hE : A.bondDim e = B.bondDim e}
    (w : EdgeCoeffIdentityWitness A B e Z Zref hE)
    (N : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :
    (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) * N *
        (↑Z⁻¹ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
      (Zref : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) * N *
        (↑Zref⁻¹ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :=
  gaugeConj_eq_of_coeffIdentities_torus w.region ⟨e, w.isBoundary⟩ w.hRB w.hCB w.hposB
    (hE₁ := hE) (hE₂ := hE) Z Zref w.hidZ w.hidZref N

/-- **The orientation-uniform-mod-scalar family from per-edge coefficient-identity witnesses.**

For a torus pair `A`, `B` and a per-edge gauge family `X` over the second tensor's bond dimensions
with orientation-uniform bond dimensions, suppose on every horizontal edge `e` the gauge `X e` and
the transported reference gauge `glReindex (huni.horizontal he).symm Xh` both carry an edge
coefficient-identity witness (with `X e` realizing the per-edge identity and the transported
reference the reference identity), and likewise on every vertical edge with `Xv`.  Then `X` is
orientation uniform up to per-edge scalars.

The witnesses package the geometric production of the matched coefficient identities; their
algebraic content (the conjugation covariance) is `gaugeConj_eq_of_edgeCoeffIdentityWitness`, and
the assembly is `isTorusOrientationUniformGaugeFamilyModScalar_of_conjCovariance`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTorusOrientationUniformGaugeFamilyModScalar_of_edgeWitnesses
    {A B : Tensor (torusGraph width height) d} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim B.bondDim Dh Dv)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    (hE : ∀ e : Edge (torusGraph width height), A.bondDim e = B.bondDim e)
    (witH : ∀ (e : Edge (torusGraph width height)) (he : IsHorizontalTorusEdge e),
      EdgeCoeffIdentityWitness A B e (X e) (glReindex (huni.horizontal he).symm Xh) (hE e))
    (witV : ∀ (e : Edge (torusGraph width height)) (he : IsVerticalTorusEdge e),
      EdgeCoeffIdentityWitness A B e (X e) (glReindex (huni.vertical he).symm Xv) (hE e)) :
    IsTorusOrientationUniformGaugeFamilyModScalar huni X := by
  refine isTorusOrientationUniformGaugeFamilyModScalar_of_conjCovariance huni X Xh Xv
    (fun e he N => gaugeConj_eq_of_edgeCoeffIdentityWitness (witH e he) N)
    (fun e he N => gaugeConj_eq_of_edgeCoeffIdentityWitness (witV e he) N)

end PEPS
end TNLean
