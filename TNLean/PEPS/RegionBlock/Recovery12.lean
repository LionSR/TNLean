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

end PEPS
end TNLean
