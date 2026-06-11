import TNLean.PEPS.TorusBlockingData
import TNLean.PEPS.NormalEdgeGaugeFamily

/-!
# The per-edge gauge at a torus edge from one-edge blocking data

Two normal PEPS on the discrete torus, related by `SameState` and matched bond dimensions, with
one-edge blocking data sharing the three blocks at an edge `e` and the single red-to-blue
crossing, admit on `e` the per-edge gauge: the bond dimensions coincide and the forward
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
red-to-blue crossing on `e`, and `B`'s red and host injectivities, admit the per-edge gauge on
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

end PEPS
end TNLean
