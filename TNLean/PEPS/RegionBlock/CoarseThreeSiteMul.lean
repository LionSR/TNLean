import TNLean.PEPS.RegionBlock.CoarseThreeSite11

/-!
# The forward-transfer multiplicativity from two coherent coarse blocking frames

The per-edge gauge construction of the normal-PEPS edge comparison consumes three
inputs about the chosen forward transfer `coeffTransferMap` over the red block at the
single boundary edge `e`: the two cross-tensor coefficient transfers and the
multiplicativity of the chosen forward transfer.  The first two are produced by the
single-region coefficient transfer; the third is the load-bearing one, since a
coefficient transfer alone does not make the chosen forward map a homomorphism.

This file isolates that multiplicativity field as a reusable theorem.  The proof inside
`exists_regionEdgeGauge_of_coherentFrames` (`TNLean.PEPS.RegionBlock.CoarseThreeSite11`)
discharges the multiplicativity through the concrete single-edge transfer
`regionEdgeTransfer`: the bridge `coeffTransferMap_eq_regionEdgeTransfer` identifies the
chosen forward map with the concrete one through `regionInsertedCoeff_injective`, and
`regionEdgeTransfer_mul` is the concrete map's multiplicativity, itself the coarse
three-site `edgeTransferMatrix_mul` conjugated by the two bond models.  That field was
only ever available bundled inside the gauge assembly; exposing it standalone lets a
consumer that already holds the coefficient transfer (the overlapping-window route, whose
read-off side is unconditional on window and host injectivity) obtain the
multiplicativity from a coherent coarse blocking frame over the red block, with the same
three-block injectivity input and no single-vertex injectivity.

The single mathematical content the multiplicativity rests on is the coarse three-site
injectivity of the assembled coarse tensor at the distinguished super-bond, which the
coherent frame supplies from the blocked-region injectivity of its three regions: the two
endpoint super-sites are injective by the red and blue blocking injectivities, the middle
super-site by the complement blocking injectivity.  The original tensor's single vertices
play no role; the super-vertex injectivity stands in for the single-vertex spanning the
vertex-injective route would use.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--586 of `Papers/1804.04964/paper_normal.tex`; the corollary at
  lines 2297--2318](https://arxiv.org/abs/1804.04964)
- `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the residual of the overlapping-window
  multiplicativity; `docs/paper-gaps/peps_normal_ft_section3_route.tex`, the coarse
  three-site route that supplies it without single-vertex injectivity.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A B : Tensor G d}

/-- **The forward-transfer multiplicativity from two coherent coarse blocking frames.**

Two coherent coarse blocking frames over `A` and `B` sharing the three regions, the bond
dimensions, and the single red-to-blue crossing edge `e`, with `A` and `B` generating the
same state, make the chosen forward transfer `coeffTransferMap` over the red block at the
single boundary edge `e` multiplicative: the transfer of a product is the product of the
transfers.

This is the `hmul` field of the per-edge gauge, extracted as a standalone statement.  The
proof identifies the chosen forward map with the concrete single-edge transfer
`regionEdgeTransfer` through `coeffTransferMap_eq_regionEdgeTransfer`, and applies the
concrete transfer's multiplicativity `regionEdgeTransfer_mul`, the coarse
`edgeTransferMatrix_mul` conjugated by the two bond models.  No single-vertex injectivity
of `A` or `B` enters: the only injectivity input is the blocked-region injectivity of the
three regions, carried by the coherent frames, which makes the assembled coarse tensor
edge-blocked three-site injective at the distinguished super-bond.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransferMap_mul_of_coherentFrames
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e)
    (htransferAB : ∀ M : Matrix (Fin (A.bondDim
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
        (Fin (A.bondDim (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
          (Fin (B.bondDim
            (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.frame.red)),
          regionInsertedCoeff (G := G) A F.frame.red
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) M σ τ =
            regionInsertedCoeff (G := G) B F.frame.red
              (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) N σ τ)
    (M M' : Matrix (Fin (A.bondDim
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1))
        (Fin (A.bondDim
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle).1)) ℂ) :
    coeffTransferMap (G := G) A B F.frame.red
        (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) htransferAB (M * M') =
      coeffTransferMap (G := G) A B F.frame.red
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) htransferAB M *
        coeffTransferMap (G := G) A B F.frame.red
          (singleBoundaryEdge (G := G) A F.frame.red F.frame.blue e hsingle) htransferAB M' := by
  rw [coeffTransferMap_eq_regionEdgeTransfer F F' hP hP' hred hblue hcompl hbond hAB hd hposA
      hposB e hsingle htransferAB (M * M'),
    coeffTransferMap_eq_regionEdgeTransfer F F' hP hP' hred hblue hcompl hbond hAB hd hposA
      hposB e hsingle htransferAB M,
    coeffTransferMap_eq_regionEdgeTransfer F F' hP hP' hred hblue hcompl hbond hAB hd hposA
      hposB e hsingle htransferAB M']
  exact regionEdgeTransfer_mul F F' hP hP' hred hblue hcompl hbond hAB e hsingle M M'

end PEPS
end TNLean
