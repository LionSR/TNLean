/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Torus.TorusRectangleReferenceData
import TNLean.PEPS.FundamentalTheorem.Normal.RegionTransferCovariance
import TNLean.PEPS.FundamentalTheorem.Injective.EdgeGaugeFamily
import TNLean.PEPS.FundamentalTheorem.Normal.RegionTransportInsertion

/-!
# Conjugation covariance of the per-edge gauge on the torus

The per-edge gauges produced by the edge blocking are determined, as conjugation maps, by the
coefficient identities they realize.  This file supplies that algebraic determinacy.

Two invertible matrices `Z` and `Z'` on the same boundary edge `f` of a region `R`, each
realizing the region-insertion coefficient identity of `A` through `B` by conjugation
(`regionInsertedCoeff A R f M = regionInsertedCoeff B R f (conj_Z M)`), induce the *same*
conjugation map (`gaugeConj_eq_of_coeffIdentities`): the region-insertion transfer map is
determined by the coefficient identity (`regionInsertedCoeff_transferMap_unique`), and both
conjugations realize it.  The reindexing algebra equivalence turns a transported gauge
`glReindex h Z` into conjugation by the reindexed matrix.

These two facts turn the geometric translation covariance of the coefficient identity
(`regionInsertedCoeff_translate_coeffIdentity`) into the conjugation form consumed by the
witness transport of the translation-covariant absorbed family; the route is recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

It also contains the following results.

* `TNLean.PEPS.exists_edgeCoeffIdentityWitness_of_transport`: pullback of a torus
  coefficient-identity witness.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1407--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)

## The per-edge coefficient-identity witness on the torus

This file bundles, per torus edge, the data realizing a region-insertion coefficient identity
of `A` through `B` by conjugation: a region whose single boundary edge is the given edge, the
second tensor's region and complement blocked-tensor injectivity, and two coefficient
identities, one realized by the per-edge gauge and one by a reference gauge
(`EdgeCoeffIdentityWitness`).

The witness is the per-edge interface of the torus assembly: the witness transport produces it
at every translate of a reference edge (`edgeCoeffIdentityWitness_translate`), and its
conjugation-form identity is converted to the bare-edge absorbed equality consumed by the
translation-covariant absorbed family (`edgeAbsorbed_of_edgeCoeffIdentityWitness`).

### References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

section TorusEdgeGaugeCovariance

section

open ManyBody (Edge)

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

/-! ### Conjugation agreement from the coefficient identity -/

section CoeffBridge

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **Two conjugating gauges realizing the same coefficient identity induce the same map.**

Two invertible matrices `Z₁` and `Z₂` on the boundary edge `f` of a region `R`, both realizing
the region-insertion coefficient identity of `A` through `B` by conjugation
(`regionInsertedCoeff A R f M = regionInsertedCoeff B R f (conj_{Zᵢ} M)` for all configurations),
induce the same conjugation map across the bond-dimension equality: for every bond matrix `M`,
`Z₁ · (reindex M) · Z₁⁻¹ = Z₂ · (reindex M) · Z₂⁻¹`.  The region-insertion
transfer map is determined by its coefficient identity
(`regionInsertedCoeff_transferMap_unique`); both conjugations realize it, so they coincide.

This is the determinacy step that turns the geometric translation covariance of the coefficient
identity into the conjugation form the witness transport consumes.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem gaugeConj_eq_of_coeffIdentities (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    {hE₁ hE₂ : A.bondDim f.1 = B.bondDim f.1}
    (Z₁ Z₂ : GL (Fin (B.bondDim f.1)) ℂ)
    (h₁ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M *
            (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (h₂ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M *
            (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    (Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M *
      (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
    (Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M *
      (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :=
  regionInsertedCoeff_transferMap_unique A B R f hRB hCB hposB
    (fun N => (Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) N *
      (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ))
    (fun N => (Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) N *
      (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ))
    h₁ h₂ M

/-! ### Arbitrary target matrices from coefficient identities -/

/-- **Single-edge conjugation covariance from two coefficient identities.**

On a boundary edge `f` of a region `R`, with `B`'s region and complement blocked-tensor
injective and positive bonds, suppose the per-edge gauge `Z₁` and a second gauge `Z₂` (both
invertible over `B.bondDim f.1`) each realize the region-insertion coefficient identity of `A`
through `B` on `f` by conjugation.  Then they induce the same conjugation map on every bond
matrix `N` over `B.bondDim f.1`.

This is `gaugeConj_eq_of_coeffIdentities` read on an arbitrary target matrix: the bond-dimension
reindexing is surjective, so every `N` is a reindexed `M`, and the determinacy applies.  Reading
it on `N` over `B.bondDim f.1` (rather than `reindex M`) is the conjugation-covariance shape at
the edge `f.1`. -/
theorem gaugeConj_eq_of_coeffIdentities_target
    (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    {hE₁ hE₂ : A.bondDim f.1 = B.bondDim f.1}
    (Z₁ Z₂ : GL (Fin (B.bondDim f.1)) ℂ)
    (h₁ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M *
            (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (h₂ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M *
            (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    (Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
      (Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) := by
  -- Every target matrix `N` is a reindexed `M` (the reindexing is an algebra equivalence).
  obtain ⟨M, rfl⟩ := (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁)).surjective N
  have hmain := gaugeConj_eq_of_coeffIdentities A B R f hRB hCB hposB
    (hE₁ := hE₁) (hE₂ := hE₂) Z₁ Z₂ h₁ h₂ M
  -- The two reindexings along `hE₁` and `hE₂` coincide by proof irrelevance.
  have hcast : (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M) =
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M) := by
    congr 1
  rw [hcast] at hmain
  exact hmain

end CoeffBridge

end PEPS
end TNLean

end

section

open ManyBody (Edge)

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
  isBoundary : ManyBody.IsRegionBoundaryEdge (G := torusGraph width height) region e
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

end

end TorusEdgeGaugeCovariance

section TorusWitnessIsoTransport

/-!
## Pullback of a torus coefficient-identity witness

A graph isomorphism carries blocked regions, physical configurations and inserted matrices
by reindexing. Hence a coefficient identity for the transported tensor pair determines a
coefficient identity for the original pair. The region and its complement remain injective,
and positive bond dimensions are preserved. The first stored endpoint belongs to the pulled
back region whenever it is carried to the first stored endpoint of the image edge.

Source: arXiv:1804.04964, the exchange of horizontal and vertical directions at lines
2368--2444 of `Papers/1804.04964/paper_normal.tex`.
-/

open ManyBody (Edge)

open scoped Matrix
namespace TNLean.PEPS
variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
variable {G : SimpleGraph V} {G' : SimpleGraph W}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj] {d : ℕ}

private theorem regionInsertedCoeff_transport_pullback_conj
    {A B : Tensor G d} (φ : G ≃g G') (R : Finset V)
    (f : {e : Edge G // ManyBody.IsRegionBoundaryEdge R e})
    (hE : A.bondDim f.1 = B.bondDim f.1)
    (hE' : (A.transport φ).bondDim (boundaryEdgeMap φ R f).1 =
      (B.transport φ).bondDim (boundaryEdgeMap φ R f).1)
    (Z : GL (Fin ((B.transport φ).bondDim (boundaryEdgeMap φ R f).1)) ℂ)
    (hid : ∀ (M : Matrix (Fin ((A.transport φ).bondDim (boundaryEdgeMap φ R f).1))
        (Fin ((A.transport φ).bondDim (boundaryEdgeMap φ R f).1)) ℂ)
      (σ : RegionPhysicalConfig (V := W) (d := d) (Region.map φ R))
      (τ : RegionPhysicalConfig (V := W) (d := d) (Finset.univ \ Region.map φ R)),
      regionInsertedCoeff (A.transport φ) (Region.map φ R) (boundaryEdgeMap φ R f) M σ τ =
        regionInsertedCoeff (B.transport φ) (Region.map φ R) (boundaryEdgeMap φ R f)
          ((Z : Matrix (Fin ((B.transport φ).bondDim (boundaryEdgeMap φ R f).1))
            (Fin ((B.transport φ).bondDim (boundaryEdgeMap φ R f).1)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE') M *
            (↑Z⁻¹ : Matrix (Fin ((B.transport φ).bondDim (boundaryEdgeMap φ R f).1))
              (Fin ((B.transport φ).bondDim (boundaryEdgeMap φ R f).1)) ℂ)) σ τ)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff A R f M σ τ = regionInsertedCoeff B R f
      ((↑(glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Z) :
        Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
        (↑(glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Z)⁻¹ :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ := by
  have h := hid (Matrix.reindexAlgEquiv ℂ ℂ
      (finCongr (transport_bondDim_boundaryEdgeMap A φ R f).symm) M)
    (regionPhysicalConfigMap φ R σ)
    (regionPhysicalConfigCongr (d := d) (Region_map_compl φ R)
      (regionPhysicalConfigMap φ (Finset.univ \ R) τ))
  rw [regionInsertedCoeff_transport A φ R f, regionInsertedCoeff_transport B φ R f] at h
  convert h using 1
  · congr 1
  · congr 1
    rw [map_mul, map_mul, glReindex_coe,
      show (glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Z)⁻¹ =
        glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Z⁻¹ from
        (map_inv (glReindex (transport_bondDim_boundaryEdgeMap B φ R f)) Z).symm,
      glReindex_coe]
    congr 1

end TNLean.PEPS

namespace TNLean.PEPS
variable {width height width' height' d : ℕ}
variable [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)]
variable [NeZero width'] [NeZero height'] [Fact (1 < width')] [Fact (1 < height')]

private noncomputable def edgeCoeffIdentityWitness_transport_pullback
    {A B : Tensor (torusGraph width height) d}
    (φ : torusGraph width height ≃g torusGraph width' height')
    (R : Finset (TorusVertex width height))
    (f : {e : Edge (torusGraph width height) // ManyBody.IsRegionBoundaryEdge R e})
    (hE : A.bondDim f.1 = B.bondDim f.1)
    (hE' : (A.transport φ).bondDim (boundaryEdgeMap φ R f).1 =
      (B.transport φ).bondDim (boundaryEdgeMap φ R f).1)
    (Z Zref : GL (Fin ((B.transport φ).bondDim (boundaryEdgeMap φ R f).1)) ℂ)
    (w : EdgeCoeffIdentityWitness (A.transport φ) (B.transport φ)
      (boundaryEdgeMap φ R f).1 Z Zref hE')
    (hR : w.region = Region.map φ R) :
    EdgeCoeffIdentityWitness A B f.1
      (glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Z)
      (glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Zref) hE where
  region := R
  isBoundary := f.2
  hRB := by
    apply (regionBlockedTensorInjective_transport B φ R).mp
    rw [← hR]
    exact w.hRB
  hCB := by
    apply (regionBlockedTensorInjective_transport B φ (Finset.univ \ R)).mp
    rw [Region_map_compl, ← hR]
    exact w.hCB
  hposB := by
    intro e
    have h := w.hposB (ManyBody.Edge.map φ e)
    simpa only [Tensor.transport_bondDim, ManyBody.Edge.map_symm_map] using h
  hidZ := by
    apply regionInsertedCoeff_transport_pullback_conj φ R f hE hE' Z
    rcases w with ⟨Rw, hb, hrb, hcb, hp, hid, hidref⟩
    dsimp only at hR
    subst Rw
    exact hid
  hidZref := by
    apply regionInsertedCoeff_transport_pullback_conj φ R f hE hE' Zref
    rcases w with ⟨Rw, hb, hrb, hcb, hp, hid, hidref⟩
    dsimp only at hR
    subst Rw
    exact hidref

/-- Pull a coefficient-identity witness back through a torus graph isomorphism.
The gauge is reindexed to the original bond, and the witnessing region is the inverse image.
If the isomorphism preserves the first stored endpoint of this edge, membership of that endpoint
in the witnessing region is preserved. No shape condition on the region is required.

Source: arXiv:1804.04964, the exchange of the two directions in the two-dimensional argument,
lines 2368--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem exists_edgeCoeffIdentityWitness_of_transport
    {A B : Tensor (torusGraph width height) d}
    (φ : torusGraph width height ≃g torusGraph width' height')
    (e : Edge (torusGraph width height))
    (hE' : (A.transport φ).bondDim (ManyBody.Edge.map φ e) =
        (B.transport φ).bondDim (ManyBody.Edge.map φ e))
    (Z : GL (Fin ((B.transport φ).bondDim (ManyBody.Edge.map φ e))) ℂ)
    (w : EdgeCoeffIdentityWitness (A.transport φ) (B.transport φ) (ManyBody.Edge.map φ e) Z Z hE')
    (hfirst : φ e.1.1 = (ManyBody.Edge.map φ e).1.1)
    (hmem : (ManyBody.Edge.map φ e).1.1 ∈ w.region) :
    ∃ (hE : A.bondDim e = B.bondDim e) (Z₀ : GL (Fin (B.bondDim e)) ℂ)
      (w₀ : EdgeCoeffIdentityWitness A B e Z₀ Z₀ hE),
      e.1.1 ∈ w₀.region ∧ w₀.region = Region.map φ.symm w.region := by
  classical
  let R := Region.map φ.symm w.region
  have hR : Region.map φ R = w.region := by
    ext v
    simp only [R, mem_Region_map]
    change φ (φ.symm v) ∈ w.region ↔ v ∈ w.region
    rw [φ.apply_symm_apply]
  have hBoundary : ManyBody.IsRegionBoundaryEdge R e := by
    apply (isRegionBoundaryEdge_map φ R e).mp
    rw [hR]
    exact w.isBoundary
  let f : {e : Edge (torusGraph width height) // ManyBody.IsRegionBoundaryEdge R e} :=
    ⟨e, hBoundary⟩
  have hE : A.bondDim e = B.bondDim e := by
    simpa only [Tensor.transport_bondDim, ManyBody.Edge.map_symm_map] using hE'
  let w₀ := edgeCoeffIdentityWitness_transport_pullback φ R f hE hE' Z Z w hR.symm
  refine ⟨hE, glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Z, w₀, ?_, rfl⟩
  change e.1.1 ∈ Region.map φ.symm w.region
  rw [mem_Region_map]
  change φ e.1.1 ∈ w.region
  rw [hfirst]
  exact hmem
end TNLean.PEPS

end TorusWitnessIsoTransport
