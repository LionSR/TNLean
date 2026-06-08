import TNLean.PEPS.RegionBlock.Recovery3

/-!
# Region physical-to-virtual recovery: incident-matrix form of the virtual pullback

This file isolates the last load-bearing fact behind the region physical-to-virtual
realization `RegionTransferRealizes` for the normal PEPS Fundamental Theorem
(remaining obligation 4 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`).

The conditional recovery `regionTransferRealizesAt_of_hform`
(`TNLean.PEPS.RegionBlock.Recovery3`) reduces the realization `hreal` to the
matrix-structure hypothesis

```
hform : localVirtualOpOfPhysicalOpAt B hvB
            (regionInsertionOp A R f hvA M.transpose) =
          localIncidentMatrixOp B (regionBoundaryEdgeInIncident R f)
            (regionTransferMatrix A B R f hvA hvB hposB M).transpose
```

Because `regionTransferMatrix … M` is *defined* as the read-off
`(incidentMatrixOfLocalOp B inc refRes W)ᵀ` of the virtual pullback
`W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`,
the hypothesis `hform` holds **exactly when `W` is of incident-matrix form** on the
boundary leg `inc`: if `W = localIncidentMatrixOp B inc P` for some matrix `P`, the
read-off recovers `P` (`incidentMatrixOfLocalOp_localIncidentMatrixOp`) and the
round-trip closes `hform`. This file proves that reduction unconditionally
(`hform_of_isIncidentMatrixForm`) and packages it as the per-matrix realization
`regionTransferRealizesAt_of_isIncidentMatrixForm`.

What remains for the unconditional normal theorem is the *region resonate* step:
showing `W` is of incident-matrix form by inverting the blocked complement endpoint
of the boundary edge `f`. This is the region analogue of the endpoint inversion of
`physical_to_virtual_insertion` (`TNLean.PEPS.InsertionRealization`), with the
empty interior of the two-block region/complement split replacing the middle-tensor
inversion.

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

/-! ### Incident-matrix form of the virtual pullback closes `hform`

The region transfer matrix is the read-off of the virtual pullback `W`. When `W`
is already of incident-matrix form on the boundary leg, the read-off inverts it
and `hform` is the round-trip identity. This is the unconditional reduction the
region resonate step feeds into. -/

/-- **The matrix-structure hypothesis `hform` from incident-matrix form.** If the
virtual pullback `W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f
hvA M.transpose)` of the transferred in-region endpoint operator is of
incident-matrix form on the boundary leg `inc` — that is, `W = localIncidentMatrixOp
B inc P` for some matrix `P` — then the matrix-structure hypothesis `hform` holds.

The region transfer matrix is the read-off `(incidentMatrixOfLocalOp B inc refRes
W)ᵀ`, so its transpose is `incidentMatrixOfLocalOp B inc refRes W`; reading off the
incident-matrix form `W` recovers `P` (`incidentMatrixOfLocalOp_localIncidentMatrixOp`),
and reinserting `P` returns `W`. This is the unconditional reduction of `hform` to
the incident-matrix structure of `W`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem hform_of_isIncidentMatrixForm (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (P : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hP : localVirtualOpOfPhysicalOpAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) P) :
    localVirtualOpOfPhysicalOpAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f)
        (regionTransferMatrix (G := G) A B R f hvA hvB hposB M).transpose := by
  classical
  set inc := regionBoundaryEdgeInIncident (G := G) R f with hinc
  set W := localVirtualOpOfPhysicalOpAt B hvB
    (regionInsertionOp (G := G) A R f hvA M.transpose) with hW
  -- The read-off recovers `P` from the incident-matrix form of `W`.
  have hread : (regionTransferMatrix (G := G) A B R f hvA hvB hposB M).transpose = P := by
    rw [regionTransferMatrix, Matrix.transpose_transpose, ← hW, hP,
      incidentMatrixOfLocalOp_localIncidentMatrixOp]
  rw [hread, hP]

end PEPS
end TNLean
