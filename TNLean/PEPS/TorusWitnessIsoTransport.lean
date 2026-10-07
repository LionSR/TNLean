/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusConjCovarianceFamily
import TNLean.PEPS.RegionTransportInsertion

/-!
# Pullback of a torus coefficient-identity witness

A graph isomorphism carries blocked regions, physical configurations and inserted matrices
by reindexing. Hence a coefficient identity for the transported tensor pair determines a
coefficient identity for the original pair. The region and its complement remain injective,
and positive bond dimensions are preserved. The first stored endpoint belongs to the pulled
back region whenever it is carried to the first stored endpoint of the image edge.

Source: arXiv:1804.04964, the exchange of horizontal and vertical directions at lines
2368--2444 of `Papers/1804.04964/paper_normal.tex`.
-/

open scoped Matrix
namespace TNLean.PEPS
variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
variable {G : SimpleGraph V} {G' : SimpleGraph W}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj] {d : ℕ}

private theorem regionInsertedCoeff_transport_pullback_conj
    {A B : Tensor G d} (φ : G ≃g G') (R : Finset V)
    (f : {e : Edge G // IsRegionBoundaryEdge R e})
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
    (f : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e})
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
    have h := w.hposB (Edge.map φ e)
    simpa only [Tensor.transport_bondDim, Edge.map_symm_map] using h
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
    (hE' : (A.transport φ).bondDim (Edge.map φ e) = (B.transport φ).bondDim (Edge.map φ e))
    (Z : GL (Fin ((B.transport φ).bondDim (Edge.map φ e))) ℂ)
    (w : EdgeCoeffIdentityWitness (A.transport φ) (B.transport φ) (Edge.map φ e) Z Z hE')
    (hfirst : φ e.1.1 = (Edge.map φ e).1.1)
    (hmem : (Edge.map φ e).1.1 ∈ w.region) :
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
  have hBoundary : IsRegionBoundaryEdge R e := by
    apply (isRegionBoundaryEdge_map φ R e).mp
    rw [hR]
    exact w.isBoundary
  let f : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e} := ⟨e, hBoundary⟩
  have hE : A.bondDim e = B.bondDim e := by
    simpa only [Tensor.transport_bondDim, Edge.map_symm_map] using hE'
  let w₀ := edgeCoeffIdentityWitness_transport_pullback φ R f hE hE' Z Z w hR.symm
  refine ⟨hE, glReindex (transport_bondDim_boundaryEdgeMap B φ R f) Z, w₀, ?_, rfl⟩
  change e.1.1 ∈ Region.map φ.symm w.region
  rw [mem_Region_map]
  change φ e.1.1 ∈ w.region
  rw [hfirst]
  exact hmem
end TNLean.PEPS
