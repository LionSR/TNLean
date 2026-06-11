import TNLean.PEPS.TorusBlockingData
import TNLean.PEPS.NormalEdgeGaugeFamily

/-!
# The per-edge gauge at a torus edge from one-edge blocking data

Two normal PEPS on the discrete torus, related by `SameState` and matched bond dimensions, with
one-edge blocking data sharing the three blocks at an edge `e` and the single red-to-blue
crossing, have on `e` the per-edge gauge: the bond dimensions coincide and the forward
region-insertion transfer is conjugation by an invertible matrix
(`exists_regionEdgeGauge_torus`).  This is the graph-polymorphic coherent-frame gauge interface
`exists_regionEdgeGauge_of_blockingData` specialized to the torus; the torus carries the
required `Fintype`, `LinearOrder`, and `DecidableRel` instances, so the interface applies
verbatim.

For a translation-invariant pair the reference datum at the reference edge of an orientation
class is translated to every edge of that class
(`TNLean/PEPS/TorusBlockingData.lean`), so this gauge is available at every edge.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines
  254--586 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The per-edge gauge at a torus edge.**

Two normal PEPS `A` and `B` on the torus with one-edge blocking data `DA`, `DB` sharing the
three blocks at `e`, matched bond dimensions, the same state, positive bonds, the single
red-to-blue crossing on `e`, and `B`'s red and host injectivities, have the per-edge gauge on
`e`: the bond dimensions of `A` and `B` on `e` coincide and the forward region-insertion
transfer is conjugation by an invertible gauge matrix `Z`.

This is `exists_regionEdgeGauge_of_blockingData` (the coherent-frame interface, stated over a
general `Fintype`/`LinearOrder` vertex set) specialized to the torus; no single-vertex
injectivity is used.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_torus
    {A B : Tensor (torusGraph width height) d} {e : Edge (torusGraph width height)}
    (DA : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e)
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) B)
      (torusGraph width height) e)
    (hred : DA.red = DB.red) (hblue : DA.blue = DB.blue)
    (hcompl : DA.complement = DB.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hsingle : ∀ g : Edge (torusGraph width height),
      IsCrossingEdge (G := torusGraph width height) A DA.red DA.blue g ↔ g = e)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red)
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ DA.red)) :
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ)
        (fwd : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ →
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ),
        ∀ M, fwd M =
            (Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  obtain ⟨_, _, _, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData DA DB hred hblue hcompl hbond hAB hd hposA hposB
      hsingle hRB hCB
  exact ⟨hEdge, Z, _, hZ⟩

/-- **The per-edge gauge at a torus edge, with its coefficient identity.**

The same conclusion as `exists_regionEdgeGauge_torus`, but exposing the region-insertion
coefficient identity that the gauge conjugation realizes: on the single boundary edge
`f = ⟨e, _⟩` of the red block, inserting `M` into `A` and contracting matches inserting the
gauge conjugation `Z · (reindex M) · Z⁻¹` into `B`.  This is the defining identity of the
forward region-insertion transfer (`RegionInsertionTransfer.fwd_coeff`), specialized through
`Z`'s realization of that transfer.

The coefficient identity is the load-bearing extra output over `exists_regionEdgeGauge_torus`:
together with the determinacy of the region-insertion transfer map
(`regionInsertedCoeff_transferMap_unique`), it turns the geometric covariance of the per-edge
transfer maps under translation into the conjugation covariance the orientation-uniform
selection consumes.

No single-vertex injectivity is used; the injectivity inputs are the blocked-region
injectivities of the data and `B`'s red and host injectivities.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_torus_coeff
    {A B : Tensor (torusGraph width height) d} {e : Edge (torusGraph width height)}
    (DA : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e)
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) B)
      (torusGraph width height) e)
    (hred : DA.red = DB.red) (hblue : DA.blue = DB.blue)
    (hcompl : DA.complement = DB.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hsingle : ∀ g : Edge (torusGraph width height),
      IsCrossingEdge (G := torusGraph width height) A DA.red DA.blue g ↔ g = e)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B DA.red)
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ DA.red)) :
    ∃ (hEdge : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ),
        ∀ (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
          (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) DA.red)
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \ DA.red)),
          regionInsertedCoeff (G := torusGraph width height) A DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e hsingle) M
              σ τ =
            regionInsertedCoeff (G := torusGraph width height) B DA.red
              (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e hsingle)
              ((Z : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) *
                  Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
                  ((Z⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
                    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))
              σ τ := by
  obtain ⟨htransferAB, htransferBA, hmul, hEdge, Z, hZ⟩ :=
    exists_regionEdgeGauge_of_blockingData DA DB hred hblue hcompl hbond hAB hd hposA hposB
      hsingle hRB hCB
  refine ⟨hEdge, Z, fun M σ τ => ?_⟩
  -- The forward transfer of the region-insertion datum realizes the conjugation `conj_Z`
  -- (`hZ`) and satisfies the coefficient identity (`fwd_coeff`); rewriting along `hZ` gives the
  -- coefficient identity for the conjugation map.
  have hfwd := (regionInsertionTransfer_of_coeffTransfer A B DA.red
    (singleBoundaryEdge (G := torusGraph width height) A DA.red DA.blue e hsingle)
    hRB hCB hAB hposB hbond htransferAB htransferBA hmul).fwd_coeff M σ τ
  rw [hZ M] at hfwd
  exact hfwd

end PEPS
end TNLean
