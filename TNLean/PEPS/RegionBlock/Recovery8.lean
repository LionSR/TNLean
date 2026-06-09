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

/-! ### The region resonate reconcile hypothesis

The one remaining mathematical content of remaining obligation 4 is that, for every
inserted matrix `M`, the virtual pullback of the transferred in-region endpoint
operator is of incident-matrix form on the boundary leg `f`. Naming it as a
predicate keeps the conditional assembly below readable and pins down precisely what
the region resonate reconcile must establish. -/

/-- **The region resonate reconcile.** For every inserted matrix `M`, the virtual
pullback `localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`
of the transferred in-region endpoint operator is of incident-matrix form on the
boundary leg `f`.

This is the content of step (iv) of remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`: the region resonate reconcile
forcing the two read-off row functions to couple through a single matrix on `f`. It
is the region analogue of the incident-matrix form read from the edge resonate
identity by `physical_to_virtual_insertion` (`TNLean.PEPS.InsertionRealization`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
def RegionResonateReconcile (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f))) :
    Prop :=
  ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
    ∃ P : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      localVirtualOpOfPhysicalOpAt B hvB
          (regionInsertionOp (G := G) A R f hvA M.transpose) =
        localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) P

/-- The region resonate reconcile gives the region physical-to-virtual realization
bundle, by `regionTransferRealizes_of_isIncidentMatrixForm`. -/
theorem regionTransferRealizes_of_reconcile (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hrec : RegionResonateReconcile (G := G) A B R f hvA hvB) :
    RegionTransferRealizes (G := G) A B R f hvA hvB hposB :=
  regionTransferRealizes_of_isIncidentMatrixForm A B R f hvA hvB hAB hA hB hposA hposB hrec

/-! ### The region insertion transfer datum from the reconcile in both directions

With the region resonate reconcile in both directions, the realization bundles
follow, and `regionInsertionTransfer_of_realizes` (`TNLean.PEPS.RegionBlock.Recovery3`)
assembles the `RegionInsertionTransfer` datum. Feeding it to
`exists_regionEdgeGauge_of_transfer` (`TNLean.PEPS.RegionBlock.Algebra`) reads off the
per-edge gauge matrix on the boundary edge `f`. -/

/-- **Region insertion transfer datum from the reconcile.** Given the region
resonate reconcile in both directions, matched bond dimensions, `SameState`, vertex
injectivity, positive bonds, and region/complement blocked injectivity of `B`, the
explicit transfer maps `regionTransferMatrix` assemble into a `RegionInsertionTransfer`
datum.

The two realization bundles come from `regionTransferRealizes_of_reconcile`, and the
datum is `regionInsertionTransfer_of_realizes`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionInsertionTransfer_of_reconcile (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (hrecAB : RegionResonateReconcile (G := G) A B R f hvA hvB)
    (hrecBA : RegionResonateReconcile (G := G) B A R f hvB hvA) :
    RegionInsertionTransfer (G := G) A B R f :=
  regionInsertionTransfer_of_realizes A B R f hvA hvB hAB hRB hCB hposA hposB hDim
    (regionTransferRealizes_of_reconcile A B R f hvA hvB hAB hA hB hposA hposB hrecAB)
    (regionTransferRealizes_of_reconcile B A R f hvB hvA hAB.symm hB hA hposB hposA hrecBA)

/-- **Per-edge gauge from the region resonate reconcile.** Given the region resonate
reconcile in both directions, together with the region/complement blocked injectivity
of both tensors and positive bond dimensions, the per-edge matrix transfer on the
boundary edge `f` is conjugation by an invertible gauge matrix `Z`, and the two bond
dimensions on `f` coincide.

This combines the transfer datum `regionInsertionTransfer_of_reconcile` with the
per-edge gauge read-off `exists_regionEdgeGauge_of_transfer`
(`TNLean.PEPS.RegionBlock.Algebra`), the region-level production of the per-edge gauge
matrix.

Source: arXiv:1804.04964, Section 3, lines 560--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_of_reconcile (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (hrecAB : RegionResonateReconcile (G := G) A B R f hvA hvB)
    (hrecBA : RegionResonateReconcile (G := G) B A R f hvB hvA) :
    ∃ hEdge : A.bondDim f.1 = B.bondDim f.1,
      ∃ Z : GL (Fin (B.bondDim f.1)) ℂ,
        ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
          (regionInsertionTransfer_of_reconcile A B R f hvA hvB hAB hA hB hRB hCB
              hposA hposB hDim hrecAB hrecBA).fwd M =
            (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
                Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :=
  exists_regionEdgeGauge_of_transfer A B R f
    (regionInsertionTransfer_of_reconcile A B R f hvA hvB hAB hA hB hRB hCB
      hposA hposB hDim hrecAB hrecBA)
    hRA hCA hposA hRB hCB hposB

end PEPS
end TNLean
