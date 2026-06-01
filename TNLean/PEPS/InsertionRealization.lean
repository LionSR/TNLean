import TNLean.PEPS.EdgeMiddlePhysical

/-!
# Physical realization of edge virtual insertions

This file records the local \(X \mapsto O_1,O_2\) step used in the
edge-blocked PEPS reduction of arXiv:1804.04964, Section 3. A matrix inserted on
the distinguished edge acts as a virtual operation on either endpoint tensor;
vertex injectivity realizes that operation by a physical operator on the
corresponding endpoint.

## Main result

- `edgeVirtualInsertionPhysicalRealization`: an arbitrary matrix on an edge is
  physically realizable at either endpoint.
- `edgeInsertedCoeff_eq_sum_left_physicalRealization`: the left endpoint
  physical realization, with the transpose convention, gives the inserted-edge
  coefficient.
- `edgeInsertedCoeff_eq_sum_right_physicalRealization`: the right endpoint
  physical realization gives the inserted-edge coefficient.
- `edgePhysicalToVirtualInsertion_of_projected_realization_eq`: projected
  endpoint realizations and image preservation imply the endpoint conclusion
  of physical-to-virtual insertion.
- `physical_to_virtual_insertion`: equal neighboring physical insertions in the
  edge-blocked three-site chain come from one matrix on the shared virtual bond.
- `edgeInsertedCoeff_endpointPhysicalRealization`: vertex injectivity gives
  endpoint physical realizations of the inserted-edge coefficient.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- A virtual matrix inserted on an edge is physically realizable on either
neighboring endpoint tensor, provided the PEPS tensor is vertex-injective.

This is the local \(X \mapsto O_1,O_2\) step in the proof of
Lemma \(\mathrm{inj\_isomorph}\) in arXiv:1804.04964, Section 3. The left and
right physical operators realize the same matrix on the distinguished incident
edge of the corresponding endpoint tensor.

**Companion coefficient statement:** This theorem proves the local endpoint
realization. The corresponding equality with the edge-inserted three-site
coefficient is recorded in `edgeInsertedCoeff_endpointPhysicalRealization`. -/
theorem edgeVirtualInsertionPhysicalRealization (A : Tensor G d)
    (hA : IsVertexInjective A) (e : Edge G)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    (∃ O₁ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ),
      ∀ c : LocalVirtualConfig A e.1.1 → ℂ,
        O₁ (localTensorMap A e.1.1 c) =
          localTensorMap A e.1.1
            (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M c)) ∧
    (∃ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ),
      ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
        O₂ (localTensorMap A e.1.2 c) =
          localTensorMap A e.1.2
            (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c)) := by
  constructor
  · exact localIncidentMatrixOp_physicalRealization
      (A := A) hA (edgeLeftIncident (G := G) e) M
  · exact localIncidentMatrixOp_physicalRealization
      (A := A) hA (edgeRightIncident (G := G) e) M

/-- Projected recovery at the left endpoint of an edge.

For the left endpoint, the matrix inserted on the edge is represented by
\(M^{\mathsf T}\) on the distinguished incident edge. This is the endpoint
specialization of the local \(O_1,O_2 \mapsto W\) recovery step in
Lemma \(\mathrm{inj\_isomorph}\) of arXiv:1804.04964, Section 3. -/
theorem edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (e : Edge G)
    (O₁ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    localVirtualOpOfPhysicalOp A hA e.1.1 O₁ =
        localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose ↔
      (localProjector A hA e.1.1).comp (O₁.comp (localProjector A hA e.1.1)) =
        physRealizeLocalOp A hA e.1.1
          (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose) :=
  localVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq A hA e.1.1 O₁
    (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose)

/-- Projected recovery at the right endpoint of an edge.

For the right endpoint, the inserted matrix acts directly on the distinguished
incident edge. This is the endpoint specialization of the local
\(O_1,O_2 \mapsto W\) recovery step in Lemma \(\mathrm{inj\_isomorph}\) of
arXiv:1804.04964, Section 3. -/
theorem edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (e : Edge G)
    (O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    localVirtualOpOfPhysicalOp A hA e.1.2 O₂ =
        localIncidentMatrixOp A (edgeRightIncident (G := G) e) M ↔
      (localProjector A hA e.1.2).comp (O₂.comp (localProjector A hA e.1.2)) =
        physRealizeLocalOp A hA e.1.2
          (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M) :=
  localVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq A hA e.1.2 O₂
    (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M)

/-- Projected endpoint physical realizations recover the corresponding virtual
matrix insertion on both endpoints.

This is the local endpoint part of the $O_1,O_2\mapsto W$ step in
Lemma $\mathrm{inj\_isomorph}$: once the compressed physical actions are the
canonical realizations of the same bond matrix, injectivity recovers the
virtual insertion on the distinguished bond. The full three-site theorem still
has to prove that such a common matrix is forced by equality of the two
physical actions on the blocked state.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 363--486
of the local paper source. -/
theorem edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (e : Edge G)
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (hO₁ : (localProjector A hA e.1.1).comp (O₁.comp (localProjector A hA e.1.1)) =
      physRealizeLocalOp A hA e.1.1
        (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose))
    (hO₂ : (localProjector A hA e.1.2).comp (O₂.comp (localProjector A hA e.1.2)) =
      physRealizeLocalOp A hA e.1.2
        (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M)) :
    localVirtualOpOfPhysicalOp A hA e.1.1 O₁ =
        localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose ∧
      localVirtualOpOfPhysicalOp A hA e.1.2 O₂ =
        localIncidentMatrixOp A (edgeRightIncident (G := G) e) M := by
  constructor
  · exact (edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq
      A hA e O₁ M).2 hO₁
  · exact (edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq
      A hA e O₂ M).2 hO₂

/-- Projected endpoint realizations of a common bond matrix give the endpoint
conclusion of physical-to-virtual insertion once the endpoint physical actions
preserve the local tensor images.

This records the local endpoint part of the \(O_1,O_2\mapsto W\) step in
Lemma \(\mathrm{inj\_isomorph}\). It does not prove the three-site statement:
the remaining source step is to derive the common projected realizations, and
the required image preservation, from equality of the two endpoint physical
actions on the edge-blocked state.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 363--486
of the local paper source. -/
theorem edgePhysicalToVirtualInsertion_of_projected_realization_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (e : Edge G)
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (hO₁ : (localProjector A hA e.1.1).comp (O₁.comp (localProjector A hA e.1.1)) =
      physRealizeLocalOp A hA e.1.1
        (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose))
    (hO₂ : (localProjector A hA e.1.2).comp (O₂.comp (localProjector A hA e.1.2)) =
      physRealizeLocalOp A hA e.1.2
        (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M))
    (hO₁_image : ∀ c : LocalVirtualConfig A e.1.1 → ℂ,
      localProjector A hA e.1.1 (O₁ (localTensorMap A e.1.1 c)) =
        O₁ (localTensorMap A e.1.1 c))
    (hO₂_image : ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
      localProjector A hA e.1.2 (O₂ (localTensorMap A e.1.2 c)) =
        O₂ (localTensorMap A e.1.2 c)) :
    ∃ M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
      (∀ c : LocalVirtualConfig A e.1.1 → ℂ,
        O₁ (localTensorMap A e.1.1 c) =
          localTensorMap A e.1.1
            (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose c)) ∧
        ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
          O₂ (localTensorMap A e.1.2 c) =
            localTensorMap A e.1.2
              (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c) := by
  obtain ⟨hLeft, hRight⟩ :=
    edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eq
      A hA e O₁ O₂ M hO₁ hO₂
  refine ⟨M, ?_, ?_⟩
  · intro c
    have hrealize :=
      localVirtualOpOfPhysicalOp_realizes_of_projector A hA e.1.1 O₁ hO₁_image c
    rw [hLeft] at hrealize
    exact hrealize.symm
  · intro c
    have hrealize :=
      localVirtualOpOfPhysicalOp_realizes_of_projector A hA e.1.2 O₂ hO₂_image c
    rw [hRight] at hrealize
    exact hrealize.symm

/-- Equal neighboring physical insertions recover a common virtual matrix on the
shared edge.

This is the edge-blocked PEPS form of the $O_1,O_2\mapsto W$ step in
Lemma $\mathrm{inj\_isomorph}$. If inserting $O_1$ at the left endpoint and
inserting $O_2$ at the right endpoint give the same three-block coefficient for
every physical configuration, then there is a matrix $M$ on the shared bond such
that $O_1\Phi_u=\Phi_uT_{u,e}(M^{\mathsf T})$ and
$O_2\Phi_v=\Phi_vT_{v,e}(M)$.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, equations
eq:resonate--eq:O->X, lines 355--486 of the local paper source.

**Proof status:** This declaration states the source recovery step used by the
insertion-algebra theorem. The current formal status is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem physical_to_virtual_insertion
    (A : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hEq : ∀ σ : V → Fin d,
      (∑ β : EdgeBoundaryConfig (G := G) A e,
        O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2)) :
    ∃ M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
      (∀ c : LocalVirtualConfig A e.1.1 → ℂ,
        O₁ (localTensorMap A e.1.1 c) =
          localTensorMap A e.1.1
            (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose c)) ∧
        ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
          O₂ (localTensorMap A e.1.2 c) =
            localTensorMap A e.1.2
              (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c) := by
  sorry

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
    simpa [edgeLeftLocalConfig, edgeInsertedLeftLocalConfig, Matrix.transpose_apply]
      using h.trans hTensor
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
    simpa [edgeRightLocalConfig, edgeInsertedRightLocalConfig] using h.trans hTensor
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
