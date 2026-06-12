import TNLean.PEPS.TorusEdgeGaugeCovariance

/-!
# The per-edge coefficient-identity witness on the torus

This file bundles, per torus edge, the data realizing a region-insertion coefficient identity
of `A` through `B` by conjugation: a region whose single boundary edge is the given edge, the
second tensor's region and complement blocked-tensor injectivity, and two coefficient
identities, one realized by the per-edge gauge and one by a reference gauge
(`EdgeCoeffIdentityWitness`).

The witness is the per-edge interface of the torus assembly: the witness transport produces it
at every translate of a reference edge (`edgeCoeffIdentityWitness_translate`), and its
conjugation-form identity is converted to the bare-edge absorbed equality consumed by the
translation-covariant absorbed family (`edgeAbsorbed_of_edgeCoeffIdentityWitness`).

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

end PEPS
end TNLean
