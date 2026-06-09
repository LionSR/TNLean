import TNLean.PEPS.RegionBlock.Recovery8

/-!
# Region resonate reconcile from the edge Fundamental Theorem

The remaining mathematical content of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3) toward `exists_regionEdgeGauge_of_reconcile`
(`TNLean.PEPS.RegionBlock.Recovery8`) is the region resonate reconcile
`RegionResonateReconcile`: for every inserted matrix `M`, the virtual pullback of
the transferred in-region endpoint operator
`regionInsertionOp A R f hvA M.transpose` is of incident-matrix form on the
boundary leg `f`.

This file discharges that obligation by the observation that the region insertion
operator on a boundary edge `f` *is* an edge insertion operator on the bond `f.1`:
the in-region endpoint `regionBoundaryEdgeInVertex R f` is one endpoint of `f.1`,
and the boundary incidence `regionBoundaryEdgeInIncident R f` is that endpoint's
incidence of `f.1`. Two incidences of the same bond at the same vertex are equal
(both pick out `f.1`), so `regionInsertionOp` reduces to the already-proven
edge insertion operators of `TNLean.PEPS.InsertionAlgebra`. The edge Fundamental
Theorem then supplies the incident-matrix form of the transferred operator's
virtual pullback, with the transfer matrix as the witness `P`.

The in-region endpoint is either the lower endpoint `f.1.1.1` (when `f.1.1.1 ∈ R`)
or the upper endpoint `f.1.1.2`, so the argument splits on orientation. The upper
case reuses `edgeRightInsertionOp_realizes_edgeTransferMatrix`; the lower case uses
the left-endpoint mirror `edgeLeftInsertionOp_realizes_edgeLeftTransferMatrix`
established here from the left clause of `physical_to_virtual_insertion`.

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

/-! ### The left-endpoint insertion operator and its transfer matrix

The left-endpoint mirror of `edgeRightInsertionOp`/`edgeTransferMatrix`
(`TNLean.PEPS.InsertionAlgebra`). The right-endpoint forms realize a matrix `X`
on the upper endpoint `e.1.2`; the left-endpoint forms realize a matrix `Y` on
the lower endpoint `e.1.1`. The two are coupled by transposition: inserting `Y`
on the left is the left clause of `physical_to_virtual_insertion` for the
inserted matrix `Y.transpose`. -/

/-- The physical operator on the lower-endpoint tensor obtained by inserting the
matrix `Y` on the chosen bond and realizing it through the lower endpoint tensor.

This is the lower-endpoint mirror of `edgeRightInsertionOp`. -/
noncomputable def edgeLeftInsertionOp (A : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.1))
    (Y : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  physRealizeLocalOpAt A hvA (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) Y)

/-- The matrix on the second family's bond obtained by transferring the
lower-endpoint insertion operator of the first family and reading it off through
the virtual pullback.

This is the lower-endpoint mirror of `edgeTransferMatrix`. -/
noncomputable def edgeLeftTransferMatrix (A B : Tensor G d) (e : Edge G)
    (hvA : LinearIndependent ℂ (A.component e.1.1))
    (hvB : LinearIndependent ℂ (B.component e.1.1))
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (Y : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ :=
  incidentMatrixOfLocalOp B (edgeLeftIncident (G := G) e)
    (edgeIncidentReferenceResidual B (edgeLeftIncident (G := G) e) hposB)
    (localVirtualOpOfPhysicalOpAt B hvB (edgeLeftInsertionOp A e hvA Y))

/-- The lower-endpoint insertion operator of the first family, transferred to the
second family across `SameState`, is realized by the matrix insertion
`edgeLeftTransferMatrix … Y` on the second family's lower endpoint.

This is the lower-endpoint mirror of `edgeRightInsertionOp_realizes_edgeTransferMatrix`.
It applies the left clause of `physical_to_virtual_insertion` to the second family,
with the inserted matrix `Y.transpose`, so that the lower endpoint realizes
`(Y.transpose).transpose = Y`.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeLeftInsertionOp_realizes_edgeLeftTransferMatrix
    (A B : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B e)
    (hAB : SameState A B)
    (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (Y : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    ∀ c : LocalVirtualConfig B e.1.1 → ℂ,
      edgeLeftInsertionOp A e hA.endpoint_linearIndependent.1 Y
          (localTensorMap B e.1.1 c) =
        localTensorMap B e.1.1
          (localIncidentMatrixOp B (edgeLeftIncident (G := G) e)
            (edgeLeftTransferMatrix A B e hA.endpoint_linearIndependent.1
              hB.endpoint_linearIndependent.1 hposB Y) c) := by
  classical
  obtain ⟨huA, hvA⟩ := hA.endpoint_linearIndependent
  obtain ⟨huB, hvB⟩ := hB.endpoint_linearIndependent
  -- The active lower-endpoint operator, and the auxiliary upper-endpoint operator
  -- for the inserted matrix `Y.transpose`.
  set O₁ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := edgeLeftInsertionOp A e huA Y with hO₁def
  set O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
    physRealizeLocalOpAt A hvA
      (localIncidentMatrixOp A (edgeRightIncident (G := G) e) Y.transpose) with hO₂def
  have hO₁ : ∀ c : LocalVirtualConfig A e.1.1 → ℂ,
      O₁ (localTensorMap A e.1.1 c) =
        localTensorMap A e.1.1
          (localIncidentMatrixOp A (edgeLeftIncident (G := G) e)
            (Y.transpose).transpose c) := by
    intro c
    rw [Matrix.transpose_transpose]
    exact physRealizeLocalOpAt_spec A huA
      (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) Y) c
  have hO₂ : ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
      O₂ (localTensorMap A e.1.2 c) =
        localTensorMap A e.1.2
          (localIncidentMatrixOp A (edgeRightIncident (G := G) e) Y.transpose c) :=
    fun c => physRealizeLocalOpAt_spec A hvA
      (localIncidentMatrixOp A (edgeRightIncident (G := G) e) Y.transpose) c
  -- Both endpoint realizations reproduce the inserted-edge coefficient of `Y.transpose`.
  have hAleft : ∀ σ : V → Fin d,
      edgeInsertedCoeff (G := G) A e σ Y.transpose =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2) := fun σ =>
    edgeInsertedCoeff_eq_sum_left_physicalRealization (G := G) A e σ Y.transpose O₁ hO₁
  have hAright : ∀ σ : V → Fin d,
      edgeInsertedCoeff (G := G) A e σ Y.transpose =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2) := fun σ =>
    edgeInsertedCoeff_eq_sum_right_physicalRealization (G := G) A e σ Y.transpose O₂ hO₂
  have hEqB : ∀ σ : V → Fin d,
      (∑ β : EdgeBoundaryConfig (G := G) B e,
        O₁ (B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
          B.component e.1.2 (edgeRightLocalConfig (G := G) B e β) (σ e.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G) B e,
          B.component e.1.1 (edgeLeftLocalConfig (G := G) B e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) B e σ β.leftResidual β.rightResidual *
            O₂ (B.component e.1.2 (edgeRightLocalConfig (G := G) B e β)) (σ e.1.2) := by
    intro σ
    rw [← edgeRealizationSum_left_sameState hAB e σ O₁,
      ← edgeRealizationSum_right_sameState hAB e σ O₂, ← hAleft σ, ← hAright σ]
  obtain ⟨Y', hY'left, _hY'right⟩ :=
    physical_to_virtual_insertion (G := G) B e hB hposB O₁ O₂ hEqB
  -- The recovered matrix's transpose equals the read-off `edgeLeftTransferMatrix`.
  have hpull : localVirtualOpOfPhysicalOpAt B huB O₁ =
      localIncidentMatrixOp B (edgeLeftIncident (G := G) e) Y'.transpose :=
    localVirtualOpOfPhysicalOpAt_eq_of_realizes B huB O₁
      (localIncidentMatrixOp B (edgeLeftIncident (G := G) e) Y'.transpose) hY'left
  have hYeq : edgeLeftTransferMatrix A B e huA huB hposB Y = Y'.transpose := by
    rw [edgeLeftTransferMatrix, ← hO₁def, hpull,
      incidentMatrixOfLocalOp_localIncidentMatrixOp]
  rw [hYeq]
  exact hY'left

/-! ### Incident-matrix form of the transferred insertion at an arbitrary incidence

The region insertion operator on a boundary edge `f` is, by definition, the
physical realization of an incident-matrix operation on the incidence
`regionBoundaryEdgeInIncident R f` of the bond `f.1`. The following helper works at
an arbitrary incidence `ie` of an arbitrary vertex `v`: it shows that the virtual
pullback of the transferred operator is again of incident-matrix form. Keeping the
vertex `v` a free variable makes the dependence on the orientation
(`v = ie.1.1.1` versus `v = ie.1.1.2`) a clean case split, discharged by the two
edge realizations on the bond `ie.1`. -/

/-- **Incident-matrix form of the transferred incident insertion.** For an incidence
`ie` of a vertex `v` lying on the bond `ie.1`, the virtual pullback of the physical
realization of `localIncidentMatrixOp A ie M`, transferred to `B` across
`SameState`, is of incident-matrix form on the same incidence `ie`.

The two orientations of `v` on the bond `ie.1` are handled by the right and left
edge realizations on `ie.1`. This is the incidence-level core of the region
resonate reconcile.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isIncidentMatrixForm_transferred_incidentInsertion
    (A B : Tensor G d) {v : V} (ie : IncidentEdge G v)
    (hvA : LinearIndependent ℂ (A.component v))
    (hvB : LinearIndependent ℂ (B.component v))
    (hA : EdgeBlockedThreeSiteInjective (G := G) A ie.1)
    (hB : EdgeBlockedThreeSiteInjective (G := G) B ie.1)
    (hAB : SameState A B) (hposB : ∀ f : Edge G, 0 < B.bondDim f)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    ∃ P : Matrix (Fin (B.bondDim ie.1)) (Fin (B.bondDim ie.1)) ℂ,
      localVirtualOpOfPhysicalOpAt B hvB
          (physRealizeLocalOpAt A hvA (localIncidentMatrixOp A ie M)) =
        localIncidentMatrixOp B ie P := by
  obtain ⟨huA, hwA⟩ := hA.endpoint_linearIndependent
  obtain ⟨huB, hwB⟩ := hB.endpoint_linearIndependent
  obtain ⟨e, hmem⟩ := ie
  -- With the incidence destructured, the bond `e` is independent of the vertex `v`,
  -- so the orientation equation eliminates `v` by `subst`.
  rcases hmem with hv | hv
  · -- Lower endpoint: `v = e.1.1`. The incidence is `edgeLeftIncident e`
    -- definitionally, so `edgeLeftInsertionOp` realizes the transfer matrix.
    subst hv
    refine ⟨edgeLeftTransferMatrix A B e huA huB hposB M, ?_⟩
    exact localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB _ _
      (fun c => edgeLeftInsertionOp_realizes_edgeLeftTransferMatrix A B e hA hB hAB hposB M c)
  · -- Upper endpoint: `v = e.1.2`. The incidence is `edgeRightIncident e`
    -- definitionally, so `edgeRightInsertionOp` realizes the transfer matrix.
    subst hv
    refine ⟨edgeTransferMatrix A B e hwA hwB hposB M, ?_⟩
    exact localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB _ _
      (fun c => edgeRightInsertionOp_realizes_edgeTransferMatrix A B e hA hB hAB hposB M c)

/-! ### The region resonate reconcile

Specializing the incidence-level core to the boundary incidence
`regionBoundaryEdgeInIncident R f` discharges the region resonate reconcile. The
bond is `f.1`, the inserted matrix is `M.transpose`, and the in-region endpoint
vertex's edge-blocked three-site injectivity comes from vertex injectivity and
positive bond dimensions through `IsVertexInjective.edgeBlockedThreeSiteInjective`. -/

/-- **The region resonate reconcile holds.** Under `SameState`, vertex injectivity
of both tensors, and positive bond dimensions, the region resonate reconcile
`RegionResonateReconcile A B R f hvA hvB` of `TNLean.PEPS.RegionBlock.Recovery8`
holds: for every inserted matrix `M`, the virtual pullback of the transferred
in-region endpoint operator is of incident-matrix form on the boundary leg `f`.

The region insertion operator on `f` is the physical realization of an
incident-matrix operation on the incidence `regionBoundaryEdgeInIncident R f` of the
bond `f.1`, so `isIncidentMatrixForm_transferred_incidentInsertion` applies
directly, with the bond-`f.1` edge-blocked three-site injectivities supplied by
`IsVertexInjective.edgeBlockedThreeSiteInjective`.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionResonateReconcile_of_sameState (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    RegionResonateReconcile (G := G) A B R f hvA hvB := by
  intro M
  have hAedge : EdgeBlockedThreeSiteInjective (G := G) A
      (regionBoundaryEdgeInIncident (G := G) R f).1 :=
    hA.edgeBlockedThreeSiteInjective hposA _
  have hBedge : EdgeBlockedThreeSiteInjective (G := G) B
      (regionBoundaryEdgeInIncident (G := G) R f).1 :=
    hB.edgeBlockedThreeSiteInjective hposB _
  exact isIncidentMatrixForm_transferred_incidentInsertion A B
    (regionBoundaryEdgeInIncident (G := G) R f) hvA hvB hAedge hBedge hAB hposB M.transpose

/-! ### The per-edge gauge from source-level hypotheses

With the region resonate reconcile now discharged in both directions, the per-edge
gauge read-off `exists_regionEdgeGauge_of_reconcile`
(`TNLean.PEPS.RegionBlock.Recovery8`) is available directly from `SameState`, vertex
injectivity, positive bond dimensions, region/complement blocked injectivity, and
matched bond dimensions, with no remaining reconcile hypothesis. -/

/-- **Per-edge gauge on a boundary edge from source-level hypotheses.** Under
`SameState`, vertex injectivity of both tensors, positive bond dimensions,
region/complement blocked injectivity of both tensors, and matched bond
dimensions, the per-edge matrix transfer on the boundary edge `f` is conjugation by
an invertible gauge matrix, and the two bond dimensions on `f` coincide.

The region resonate reconcile in both directions is supplied by
`regionResonateReconcile_of_sameState`, and the gauge read-off is
`exists_regionEdgeGauge_of_reconcile`.

Source: arXiv:1804.04964, Section 3, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_of_sameState (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim) :
    ∃ hEdge : A.bondDim f.1 = B.bondDim f.1,
      ∃ Z : GL (Fin (B.bondDim f.1)) ℂ,
        ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
          (regionInsertionTransfer_of_reconcile A B R f hvA hvB hAB hA hB hRB hCB
              hposA hposB hDim
              (regionResonateReconcile_of_sameState A B R f hvA hvB hAB hA hB hposA hposB)
              (regionResonateReconcile_of_sameState B A R f hvB hvA hAB.symm hB hA
                hposB hposA)).fwd M =
            (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
                Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :=
  exists_regionEdgeGauge_of_reconcile A B R f hvA hvB hAB hA hB hRA hCA hRB hCB
    hposA hposB hDim
    (regionResonateReconcile_of_sameState A B R f hvA hvB hAB hA hB hposA hposB)
    (regionResonateReconcile_of_sameState B A R f hvB hvA hAB.symm hB hA hposB hposA)

end PEPS
end TNLean
