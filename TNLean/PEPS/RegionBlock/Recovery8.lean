import TNLean.PEPS.RegionBlock.Recovery7

/-!
# Region physical-to-virtual recovery: incident-matrix form to the realization bundle

This file connects the incident-matrix form of the virtual pullback to the
realization bundle `RegionTransferRealizes` of `TNLean.PEPS.RegionBlock.Recovery3`,
the last assembly toward the normal PEPS Fundamental Theorem (remaining obligation 4
of `docs/paper-gaps/peps_normal_ft_section3_route.tex`).

Recall the reduction chain already in place:

* `hform_of_isIncidentMatrixForm` (`TNLean.PEPS.RegionBlock.Recovery4`) turns
  incident-matrix form of the virtual pullback
  `W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`
  into the matrix-structure hypothesis `hform`.
* `regionTransferRealizesAt_of_hform` (`TNLean.PEPS.RegionBlock.Recovery3`) turns
  `hform` into the per-matrix realization (the body of `RegionTransferRealizes`).

This file packages the two into one step
(`regionTransferRealizes_of_isIncidentMatrixForm`): from the per-matrix
incident-matrix form of the virtual pullback, the realization bundle
`RegionTransferRealizes` follows, and hence — in both directions — the region
insertion transfer datum (`regionInsertionTransfer_of_realizes`).

The single remaining mathematical content of obligation 4 is therefore exactly the
hypothesis `hIncForm`: the virtual pullback `W` is of incident-matrix form on the
boundary leg `f`. This is the region resonate reconcile (step (iv) of the route
note): inverting both blocked endpoints through the blocked-region left inverses and
forcing the two read-off row functions to couple through a single matrix on `f`. The
prior files supply the resonate identity (`region_resonate_identity`), the row
factorings (`regionInsertedCoeff_eq_region_blockedMap`,
`regionInsertedCoeff_eq_complement_blockedMap`), and the read-offs
(`regionBlockedLeftInverse_region_regionInsertedCoeff`,
`regionBlockedLeftInverse_complement_regionInsertedCoeff`); what remains is the
reconcile itself.

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

/-! ### The realization bundle from per-matrix incident-matrix form

The realization bundle `RegionTransferRealizes` is exactly the per-matrix
realization quantified over all inserted matrices. Each per-matrix realization
follows from incident-matrix form of the virtual pullback through the existing
reduction `hform_of_isIncidentMatrixForm` then `regionTransferRealizesAt_of_hform`.
Quantifying over `M` assembles the bundle. -/

/-- **The realization bundle from incident-matrix form.** If, for every inserted
matrix `M`, the virtual pullback of the transferred in-region endpoint operator is
of incident-matrix form on the boundary leg `f`, then the region physical-to-virtual
realization bundle `RegionTransferRealizes` holds.

For each `M`, `hform_of_isIncidentMatrixForm` turns the incident-matrix form into the
matrix-structure hypothesis `hform`, and `regionTransferRealizesAt_of_hform` (using
the unconditional image-preservation half supplied by vertex injectivity) turns
`hform` into the per-matrix realization, which is the body of `RegionTransferRealizes`.

The hypothesis `hIncForm` is the only remaining mathematical content: it is the
region resonate reconcile (step (iv) of remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionTransferRealizes_of_isIncidentMatrixForm (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hIncForm : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ P : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        localVirtualOpOfPhysicalOpAt B hvB
            (regionInsertionOp (G := G) A R f hvA M.transpose) =
          localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) P) :
    RegionTransferRealizes (G := G) A B R f hvA hvB hposB := by
  intro M c
  obtain ⟨P, hP⟩ := hIncForm M
  have hform := hform_of_isIncidentMatrixForm A B R f hvA hvB hposB M P hP
  exact regionTransferRealizesAt_of_hform A B R f hvA hvB hAB hA hB hposA hposB M hform c

end PEPS
end TNLean
