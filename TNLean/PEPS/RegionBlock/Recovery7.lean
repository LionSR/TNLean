import TNLean.PEPS.RegionBlock.Recovery6

/-!
# Region physical-to-virtual recovery: the region resonate identity and endpoint pin

This file assembles the two endpoint readings of the region-inserted coefficient
(the in-region endpoint reading of `TNLean.PEPS.RegionBlock.Recovery2` and the
out-of-region endpoint reading of `TNLean.PEPS.RegionBlock.Recovery6`) into the
**region resonate identity**: the two endpoint operators built from the first
tensor `A`, applied to the *second* tensor `B`'s closed state vectors, agree at the
endpoint physical legs. This is the region analogue of the resonate identity
`hEqB` that `edgeRightInsertionOp_realizes_edgeTransferMatrix`
(`TNLean.PEPS.InsertionAlgebra`) derives at the edge level and feeds into
`physical_to_virtual_insertion` (`TNLean.PEPS.InsertionRealization`).

Both endpoint readings collapse, across `SameState`, to the same
`SameState`-invariant closed-state realization sum
(`regionInsertionOp_regionStateVec_pin`, `TNLean.PEPS.RegionBlock.Recovery3`), so
the two readings agree. The in-region endpoint operator carries `M` through the
in-region endpoint `v`; the out-of-region endpoint operator carries `M` through
the out-of-region endpoint `vout`, which is the in-region endpoint of `f` viewed as
a boundary edge of the set complement `univ \ R`
(`regionBoundaryEdgeInVertex_compl_eq_outVertex`).

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The out-of-region-endpoint pin

The in-region endpoint pin `regionInsertionOp_regionStateVec_pin` applied to the
set complement `univ \ R` of `R`, with the inserted matrix transposed and the
region/complement physical arguments exchanged, recovers the first tensor's
region-inserted coefficient through the out-of-region endpoint `vout`. The cast
identity `regionInsertedCoeff_eq_compl` (`TNLean.PEPS.RegionBlock.Recovery6`) turns
the complement-side coefficient back into the original region-inserted coefficient. -/

/-- **The out-of-region-endpoint pin.** The out-of-region endpoint operator of the
first tensor from `M`, applied to the *second* tensor's closed state vector on the
set complement `univ \ R` and evaluated at the out-of-region endpoint physical leg,
recovers the first tensor's region-inserted coefficient of `M`, up to the interior
bond product over the non-boundary edges of `univ \ R`.

This is `regionInsertionOp_regionStateVec_pin` instanced at the set complement
`univ \ R`, with the inserted matrix transposed and the region/complement physical
arguments exchanged, read back through the complement-side cast identity
`regionInsertedCoeff_eq_compl`. Together with the in-region-endpoint pin it is the
doubled boundary-edge reading the region resonate identity equates.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertionOp_regionStateVec_pin_compl (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInteriorBondProd (G := G) A (Finset.univ \ R) •
        (regionInsertionOp (G := G) A (Finset.univ \ R)
          (regionBoundaryEdgeToCompl (G := G) R f) hvAout M.transpose.transpose
          (regionStateVec (G := G) B (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f) τ
            (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)))
          (τ ⟨regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f),
            regionBoundaryEdgeInVertex_mem (G := G) (Finset.univ \ R)
              (regionBoundaryEdgeToCompl (G := G) R f)⟩) =
      regionInsertedCoeff (G := G) A R f M σ τ := by
  rw [regionInsertedCoeff_eq_compl A R f M σ τ]
  exact regionInsertionOp_regionStateVec_pin A B (Finset.univ \ R)
    (regionBoundaryEdgeToCompl (G := G) R f) hvAout hAB M.transpose τ
    (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)

/-! ### The region resonate identity

Equating the in-region-endpoint pin and the out-of-region-endpoint pin gives the
**region resonate identity**: the in-region and out-of-region endpoint operators of
the first tensor, applied to the second tensor's closed state vectors at the two
endpoints, agree (up to their respective interior bond products). This is the
region analogue of the resonate identity `hEqB` that
`edgeRightInsertionOp_realizes_edgeTransferMatrix` feeds into
`physical_to_virtual_insertion`. It reads the two tensors only through the
`SameState`-invariant closed state vectors. -/

/-- **The region resonate identity.** The in-region-endpoint operator of the first
tensor from `M`, applied to the second tensor's closed state vector and evaluated at
the in-region endpoint leg, agrees with the out-of-region-endpoint operator from `M`,
applied to the second tensor's complement-side closed state vector and evaluated at
the out-of-region endpoint leg, each scaled by the interior bond product of the
respective block.

Both sides equal the first tensor's region-inserted coefficient of `M`: the left
side by the in-region-endpoint pin `regionInsertionOp_regionStateVec_pin`, the right
side by the out-of-region-endpoint pin
`regionInsertionOp_regionStateVec_pin_compl`. This is the doubled boundary-edge
reading the region resonate step equates.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem region_resonate_identity (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInteriorBondProd (G := G) A R •
        (regionInsertionOp (G := G) A R f hvA M.transpose
          (regionStateVec (G := G) B R f σ τ))
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩) =
      regionInteriorBondProd (G := G) A (Finset.univ \ R) •
        (regionInsertionOp (G := G) A (Finset.univ \ R)
          (regionBoundaryEdgeToCompl (G := G) R f) hvAout M.transpose.transpose
          (regionStateVec (G := G) B (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f) τ
            (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)))
          (τ ⟨regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f),
            regionBoundaryEdgeInVertex_mem (G := G) (Finset.univ \ R)
              (regionBoundaryEdgeToCompl (G := G) R f)⟩) := by
  rw [regionInsertionOp_regionStateVec_pin A B R f hvA hAB M σ τ,
    regionInsertionOp_regionStateVec_pin_compl A B R f hvAout hAB M σ τ]

end PEPS
end TNLean
