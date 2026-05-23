import TNLean.PEPS.Blocking

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

**Scope restriction (endpoint realization):** This theorem proves the local
endpoint realization, not yet the coefficient-level equality with
the edge-inserted three-site coefficient in the full edge-blocked three-site
contraction. The remaining step is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
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

end PEPS
end TNLean
