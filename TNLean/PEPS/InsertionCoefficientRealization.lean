import TNLean.PEPS.InsertionRealization

/-!
# Coefficient realizations for edge virtual insertions

This file records the coefficient-level consequences of endpoint physical
realization. A physical realization of a virtual matrix insertion at either
endpoint reproduces the full edge-inserted PEPS coefficient. These formulas are
the endpoint \(X \mapsto O_1,O_2\) part used in the edge-blocked insertion
algebra comparison.

Source: arXiv:1804.04964, Section 3, Lemma \(\mathrm{inj\_isomorph}\), lines
254--582 of `Papers/1804.04964/paper_normal.tex`.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The left-endpoint physical realization of a virtual matrix insertion
reproduces the full inserted-edge coefficient.

This is the coefficient-level part of the local \(X \mapsto O_1,O_2\) step in
Lemma \(\mathrm{inj\_isomorph}\) of arXiv:1804.04964, Section 3, in the
left-endpoint orientation. Since the ordinary edge boundary supplies the right
distinguished-edge index, the left endpoint realizes \(M^{\mathsf T}\), so that
the resulting inserted-edge coefficient has matrix coefficient
\(M_{\mathrm{left},\mathrm{right}}\). -/
theorem edgeInsertedCoeff_eq_sum_left_physicalRealization (A : Tensor G d)
    (e : Edge G) (σ : V → Fin d)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (O₁ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hO₁ : ∀ c : LocalVirtualConfig A e.1.1 → ℂ,
      O₁ (localTensorMap A e.1.1 c) =
        localTensorMap A e.1.1
          (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose c)) :
    edgeInsertedCoeff (G := G) A e σ M =
      ∑ β : EdgeBoundaryConfig (G := G) A e,
        O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2) := by
  classical
  let φ := edgeBoundaryLeftIndexEquivInsertedBoundaryConfig (G := G) A e
  let F : EdgeInsertedBoundaryConfig (G := G) A e → ℂ := fun β =>
    A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      M β.leftEdgeIndex β.rightEdgeIndex *
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e β) (σ e.1.2)
  have hLeft :
      ∀ β : EdgeBoundaryConfig (G := G) A e,
        O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) =
          ∑ y : Fin (A.bondDim e),
            M y β.edgeIndex *
              A.component e.1.1
                (edgeInsertedLeftLocalConfig (G := G) A e
                  { leftEdgeIndex := y
                    rightEdgeIndex := β.edgeIndex
                    leftResidual := β.leftResidual
                    rightResidual := β.rightResidual })
                (σ e.1.1) := by
    intro β
    have h := congrFun
      (hO₁ (Pi.single (edgeLeftLocalConfig (G := G) A e β) (1 : ℂ))) (σ e.1.1)
    rw [localTensorMap_apply_single] at h
    have hTensor := congrFun
      (localTensorMap_localIncidentMatrixOp_single (G := G) A
        (edgeLeftIncident (G := G) e) M.transpose β.edgeIndex β.leftResidual) (σ e.1.1)
    calc
      O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1)
          = (localTensorMap A e.1.1)
              ((localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose)
                (Pi.single (edgeLeftLocalConfig (G := G) A e β) 1)) (σ e.1.1) := h
      _ = ∑ y : Fin (A.bondDim e),
            M y β.edgeIndex *
              A.component e.1.1
                (edgeInsertedLeftLocalConfig (G := G) A e
                  { leftEdgeIndex := y
                    rightEdgeIndex := β.edgeIndex
                    leftResidual := β.leftResidual
                    rightResidual := β.rightResidual })
                (σ e.1.1) := by
          change
            (localTensorMap A e.1.1)
              ((localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose)
                (Pi.single
                  ((localVirtualConfigSplitAt A (edgeLeftIncident (G := G) e)).symm
                    (β.edgeIndex, β.leftResidual)) 1)) (σ e.1.1)
              = ∑ x : Fin (A.bondDim e),
                  M x β.edgeIndex *
                    A.component e.1.1
                      ((localVirtualConfigSplitAt A (edgeLeftIncident (G := G) e)).symm
                        (x, β.leftResidual)) (σ e.1.1)
          calc
            (localTensorMap A e.1.1)
                ((localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose)
                  (Pi.single
                    ((localVirtualConfigSplitAt A (edgeLeftIncident (G := G) e)).symm
                      (β.edgeIndex, β.leftResidual)) 1)) (σ e.1.1)
                = (∑ y : Fin (A.bondDim e),
                    M.transpose β.edgeIndex y •
                      A.component e.1.1
                        ((localVirtualConfigSplitAt A (edgeLeftIncident (G := G) e)).symm
                          (y, β.leftResidual))) (σ e.1.1) := hTensor
            _ = ∑ x : Fin (A.bondDim e),
                  M x β.edgeIndex *
                    A.component e.1.1
                      ((localVirtualConfigSplitAt A (edgeLeftIncident (G := G) e)).symm
                        (x, β.leftResidual)) (σ e.1.1) := by
                simp [Matrix.transpose_apply]
  calc
    edgeInsertedCoeff (G := G) A e σ M = ∑ β : EdgeInsertedBoundaryConfig (G := G) A e,
        F β := by
      rfl
    _ = ∑ x : (Σ β : EdgeBoundaryConfig (G := G) A e, Fin (A.bondDim e)),
        F (φ x) := by
      exact (φ.sum_comp F).symm
    _ = ∑ β : EdgeBoundaryConfig (G := G) A e,
        ∑ y : Fin (A.bondDim e), F (φ ⟨β, y⟩) := by
      exact Fintype.sum_sigma' (fun β y => F (φ ⟨β, y⟩))
    _ = ∑ β : EdgeBoundaryConfig (G := G) A e,
        O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2) := by
      refine Finset.sum_congr rfl ?_
      intro β _
      rw [hLeft β]
      simp [F, φ, edgeBoundaryLeftIndexEquivInsertedBoundaryConfig, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

/-- The right-endpoint physical realization of a virtual matrix insertion
reproduces the full inserted-edge coefficient.

This is the coefficient-level part of the local \(X \mapsto O_1,O_2\) step in
Lemma \(\mathrm{inj\_isomorph}\) of arXiv:1804.04964, Section 3, in the
right-endpoint orientation. The ordinary edge boundary provides the left
distinguished-edge index, while the right physical action supplies the
independent right distinguished-edge index of the inserted-edge coefficient. -/
theorem edgeInsertedCoeff_eq_sum_right_physicalRealization (A : Tensor G d)
    (e : Edge G) (σ : V → Fin d)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hO₂ : ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
      O₂ (localTensorMap A e.1.2 c) =
        localTensorMap A e.1.2
          (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c)) :
    edgeInsertedCoeff (G := G) A e σ M =
      ∑ β : EdgeBoundaryConfig (G := G) A e,
        A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2) := by
  classical
  let φ := edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e
  let F : EdgeInsertedBoundaryConfig (G := G) A e → ℂ := fun β =>
    A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      M β.leftEdgeIndex β.rightEdgeIndex *
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e β) (σ e.1.2)
  have hRight :
      ∀ β : EdgeBoundaryConfig (G := G) A e,
        O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2) =
          ∑ y : Fin (A.bondDim e),
            M β.edgeIndex y *
              A.component e.1.2
                (edgeInsertedRightLocalConfig (G := G) A e
                  { leftEdgeIndex := β.edgeIndex
                    rightEdgeIndex := y
                    leftResidual := β.leftResidual
                    rightResidual := β.rightResidual })
                (σ e.1.2) := by
    intro β
    have h := congrFun
      (hO₂ (Pi.single (edgeRightLocalConfig (G := G) A e β) (1 : ℂ))) (σ e.1.2)
    rw [localTensorMap_apply_single] at h
    have hTensor := congrFun
      (localTensorMap_localIncidentMatrixOp_single (G := G) A
        (edgeRightIncident (G := G) e) M β.edgeIndex β.rightResidual) (σ e.1.2)
    calc
      O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2)
          = (localTensorMap A e.1.2)
              ((localIncidentMatrixOp A (edgeRightIncident (G := G) e) M)
                (Pi.single (edgeRightLocalConfig (G := G) A e β) 1)) (σ e.1.2) := h
      _ = ∑ y : Fin (A.bondDim e),
            M β.edgeIndex y *
              A.component e.1.2
                (edgeInsertedRightLocalConfig (G := G) A e
                  { leftEdgeIndex := β.edgeIndex
                    rightEdgeIndex := y
                    leftResidual := β.leftResidual
                    rightResidual := β.rightResidual })
                (σ e.1.2) := by
          change
            (localTensorMap A e.1.2)
              ((localIncidentMatrixOp A (edgeRightIncident (G := G) e) M)
                (Pi.single
                  ((localVirtualConfigSplitAt A (edgeRightIncident (G := G) e)).symm
                    (β.edgeIndex, β.rightResidual)) 1)) (σ e.1.2)
              = ∑ x : Fin (A.bondDim e),
                  M β.edgeIndex x *
                    A.component e.1.2
                      ((localVirtualConfigSplitAt A (edgeRightIncident (G := G) e)).symm
                        (x, β.rightResidual)) (σ e.1.2)
          calc
            (localTensorMap A e.1.2)
                ((localIncidentMatrixOp A (edgeRightIncident (G := G) e) M)
                  (Pi.single
                    ((localVirtualConfigSplitAt A (edgeRightIncident (G := G) e)).symm
                      (β.edgeIndex, β.rightResidual)) 1)) (σ e.1.2)
                = (∑ y : Fin (A.bondDim e),
                    M β.edgeIndex y •
                      A.component e.1.2
                        ((localVirtualConfigSplitAt A (edgeRightIncident (G := G) e)).symm
                          (y, β.rightResidual))) (σ e.1.2) := hTensor
            _ = ∑ x : Fin (A.bondDim e),
                  M β.edgeIndex x *
                    A.component e.1.2
                      ((localVirtualConfigSplitAt A (edgeRightIncident (G := G) e)).symm
                        (x, β.rightResidual)) (σ e.1.2) := by
                simp
  calc
    edgeInsertedCoeff (G := G) A e σ M = ∑ β : EdgeInsertedBoundaryConfig (G := G) A e,
        F β := by
      rfl
    _ = ∑ x : (Σ β : EdgeBoundaryConfig (G := G) A e, Fin (A.bondDim e)),
        F (φ x) := by
      exact (φ.sum_comp F).symm
    _ = ∑ β : EdgeBoundaryConfig (G := G) A e,
        ∑ y : Fin (A.bondDim e), F (φ ⟨β, y⟩) := by
      exact Fintype.sum_sigma' (fun β y => F (φ ⟨β, y⟩))
    _ = ∑ β : EdgeBoundaryConfig (G := G) A e,
        A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2) := by
      refine Finset.sum_congr rfl ?_
      intro β _
      rw [hRight β]
      simp [F, φ, edgeBoundaryRightIndexEquivInsertedBoundaryConfig, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

/-- Vertex injectivity realizes an inserted edge matrix by physical operators at
the two endpoint tensors.

For an inserted matrix \(M\), the left endpoint realizes \(M^{\mathsf T}\) and
the right endpoint realizes \(M\). Both physical realizations give the same
inserted-edge coefficient after the edge-centered three-site decomposition. -/
theorem edgeInsertedCoeff_endpointPhysicalRealization (A : Tensor G d)
    (hA : IsVertexInjective A) (e : Edge G) (σ : V → Fin d)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    (∃ O₁ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ),
      (∀ c : LocalVirtualConfig A e.1.1 → ℂ,
        O₁ (localTensorMap A e.1.1 c) =
          localTensorMap A e.1.1
            (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose c)) ∧
      edgeInsertedCoeff (G := G) A e σ M =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) ∧
    (∃ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ),
      (∀ c : LocalVirtualConfig A e.1.2 → ℂ,
        O₂ (localTensorMap A e.1.2 c) =
          localTensorMap A e.1.2
            (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c)) ∧
      edgeInsertedCoeff (G := G) A e σ M =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2)) := by
  constructor
  · obtain ⟨O₁, hO₁⟩ := localIncidentMatrixOp_physicalRealization
      (A := A) hA (edgeLeftIncident (G := G) e) M.transpose
    exact ⟨O₁, hO₁, edgeInsertedCoeff_eq_sum_left_physicalRealization
      (G := G) A e σ M O₁ hO₁⟩
  · obtain ⟨O₂, hO₂⟩ := localIncidentMatrixOp_physicalRealization
      (A := A) hA (edgeRightIncident (G := G) e) M
    exact ⟨O₂, hO₂, edgeInsertedCoeff_eq_sum_right_physicalRealization
      (G := G) A e σ M O₂ hO₂⟩

end PEPS
end TNLean
