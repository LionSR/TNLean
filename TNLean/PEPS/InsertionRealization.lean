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

## Status

The endpoint theorem
`edgePhysicalToVirtualInsertion_of_projected_realization_eq` is a
proof-complete consequence once the common matrix, projected realizations, and
image preservation are supplied. The source-level theorem
`physical_to_virtual_insertion` still records the remaining
\(O_1,O_2 \mapsto W\) obligation: deriving those hypotheses from equality of
the two endpoint physical actions on the edge-blocked three-site state.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The edge-blocked three-site injectivity hypothesis already carries linear
independence of the tensor families at the two endpoints of the chosen edge.

The endpoint fields `left_injective`/`right_injective` are injectivity of the
local tensor maps `localTensorMap A e.1.1`/`localTensorMap A e.1.2`, which equal
the `Fintype.linearCombination` of the endpoint component families. Injectivity
of that linear combination is exactly linear independence of the family. -/
theorem EdgeBlockedThreeSiteInjective.endpoint_linearIndependent {A : Tensor G d}
    {e : Edge G} (hA : EdgeBlockedThreeSiteInjective (G := G) A e) :
    LinearIndependent ℂ (A.component e.1.1) ∧
      LinearIndependent ℂ (A.component e.1.2) :=
  ⟨linearIndependent_iff_injective_fintypeLinearCombination.2 hA.left_injective,
    linearIndependent_iff_injective_fintypeLinearCombination.2 hA.right_injective⟩

/-! ### The middle-block left inverse

The middle block of the edge-centered three-site chain is injective
(`EdgeMiddleTensorInjective`), so the associated linear-combination map
`edgeMiddleTensorMap` admits a left inverse. This is the middle-block analogue of
the endpoint construction `localLeftInverseAt`: where `localLeftInverseAt`
inverts a single vertex tensor from `LinearIndependent ℂ (A.component v)`, here
`edgeMiddleLeftInverse` inverts the whole blocked middle tensor from
`EdgeMiddleTensorInjective`. It is the "invert $B_2$" half of the
$D_{23}^{-1}$ contraction-inverse in `eq:inj_O->X_argument`.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, `eq:inj_O->X_argument`,
lines 377--457 of the local paper source. -/

/-- The middle-block tensor map: the linear-combination map of the edge-middle
tensor family over the residual boundary labels.

This is the middle-block analogue of `localTensorMap`: it sends a coefficient
family on the residual boundary labels to the corresponding middle physical
vector. -/
noncomputable abbrev edgeMiddleTensorMap (A : Tensor G d) (e : Edge G) :
    (EdgeMiddleBoundaryLabel (G := G) A e → ℂ) →ₗ[ℂ]
      (EdgeMiddlePhysicalConfig (G := G) (d := d) e → ℂ) :=
  Fintype.linearCombination ℂ (edgeMiddleTensorFamily (G := G) A e)

/-- Middle-block injectivity makes the middle tensor map injective. This is the
middle-block analogue of `localTensorMap_injective_of_linearIndependent`. -/
theorem edgeMiddleTensorMap_injective_of_injective {A : Tensor G d} {e : Edge G}
    (hMid : EdgeMiddleTensorInjective (G := G) A e) :
    Function.Injective (edgeMiddleTensorMap (G := G) A e) :=
  hMid.fintypeLinearCombination_injective

/-- Kernel form of `edgeMiddleTensorMap_injective_of_injective`. -/
theorem edgeMiddleTensorMap_ker_eq_bot_of_injective {A : Tensor G d} {e : Edge G}
    (hMid : EdgeMiddleTensorInjective (G := G) A e) :
    LinearMap.ker (edgeMiddleTensorMap (G := G) A e) = ⊥ :=
  LinearMap.ker_eq_bot.mpr <| edgeMiddleTensorMap_injective_of_injective hMid

/-- A chosen left inverse of the middle tensor map under middle-block
injectivity. This is the middle-block analogue of `localLeftInverseAt`, built the
same way from `LinearMap.exists_leftInverse_of_injective`. It is the
contraction-inverse of the blocked middle tensor used in the $O_1,O_2\mapsto W$
step.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, `eq:inj_O->X_argument`,
lines 377--457 of the local paper source. -/
noncomputable def edgeMiddleLeftInverse (A : Tensor G d) {e : Edge G}
    (hMid : EdgeMiddleTensorInjective (G := G) A e) :
    (EdgeMiddlePhysicalConfig (G := G) (d := d) e → ℂ) →ₗ[ℂ]
      (EdgeMiddleBoundaryLabel (G := G) A e → ℂ) :=
  ((edgeMiddleTensorMap (G := G) A e).exists_leftInverse_of_injective
    (edgeMiddleTensorMap_ker_eq_bot_of_injective hMid)).choose

@[simp] theorem edgeMiddleLeftInverse_comp_edgeMiddleTensorMap (A : Tensor G d)
    {e : Edge G} (hMid : EdgeMiddleTensorInjective (G := G) A e) :
    (edgeMiddleLeftInverse (G := G) A hMid).comp (edgeMiddleTensorMap (G := G) A e) =
      LinearMap.id :=
  ((edgeMiddleTensorMap (G := G) A e).exists_leftInverse_of_injective
    (edgeMiddleTensorMap_ker_eq_bot_of_injective hMid)).choose_spec

@[simp] theorem edgeMiddleLeftInverse_apply_edgeMiddleTensorMap (A : Tensor G d)
    {e : Edge G} (hMid : EdgeMiddleTensorInjective (G := G) A e)
    (c : EdgeMiddleBoundaryLabel (G := G) A e → ℂ) :
    edgeMiddleLeftInverse (G := G) A hMid (edgeMiddleTensorMap (G := G) A e c) = c := by
  change ((edgeMiddleLeftInverse (G := G) A hMid).comp
    (edgeMiddleTensorMap (G := G) A e)) c = c
  rw [edgeMiddleLeftInverse_comp_edgeMiddleTensorMap]
  rfl

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

/-- Projected recovery at the left endpoint of an edge, under linear
independence of the tensor family at that single endpoint.

This is the per-endpoint form of
`edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq`: it requires
only `LinearIndependent ℂ (A.component e.1.1)`, the fact that
`EdgeBlockedThreeSiteInjective` already supplies via
`EdgeBlockedThreeSiteInjective.endpoint_linearIndependent`. -/
theorem edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt
    (A : Tensor G d) (e : Edge G)
    (hu : LinearIndependent ℂ (A.component e.1.1))
    (O₁ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    localVirtualOpOfPhysicalOpAt A hu O₁ =
        localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose ↔
      (localProjectorAt A hu).comp (O₁.comp (localProjectorAt A hu)) =
        physRealizeLocalOpAt A hu
          (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose) :=
  localVirtualOpOfPhysicalOpAt_eq_iff_projected_realization_eq A hu O₁
    (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose)

/-- Projected recovery at the right endpoint of an edge, under linear
independence of the tensor family at that single endpoint.

This is the per-endpoint form of
`edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq`: it
requires only `LinearIndependent ℂ (A.component e.1.2)`, the fact that
`EdgeBlockedThreeSiteInjective` already supplies via
`EdgeBlockedThreeSiteInjective.endpoint_linearIndependent`. -/
theorem edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt
    (A : Tensor G d) (e : Edge G)
    (hv : LinearIndependent ℂ (A.component e.1.2))
    (O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    localVirtualOpOfPhysicalOpAt A hv O₂ =
        localIncidentMatrixOp A (edgeRightIncident (G := G) e) M ↔
      (localProjectorAt A hv).comp (O₂.comp (localProjectorAt A hv)) =
        physRealizeLocalOpAt A hv
          (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M) :=
  localVirtualOpOfPhysicalOpAt_eq_iff_projected_realization_eq A hv O₂
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
Lemma \(\mathrm{inj\_isomorph}\). It is a conditional consequence of a common
bond matrix and projected endpoint realizations. It does not prove the
three-site source theorem: the remaining source step is to derive the common
matrix, the projected realizations, and image preservation from equality of the
two endpoint physical actions on the edge-blocked state.

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
  constructor
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

/-- Projected endpoint physical realizations recover the corresponding virtual
matrix insertion on both endpoints, under linear independence at the two
endpoints only.

This is the endpoint-injective form of
`edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eq`: it takes
the two endpoint linear-independence facts (the pair supplied by
`EdgeBlockedThreeSiteInjective.endpoint_linearIndependent`) instead of the global
`IsVertexInjective` hypothesis, so it applies directly under the edge-blocked
three-site injectivity hypothesis of `physical_to_virtual_insertion`.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 363--486
of the local paper source. -/
theorem edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eqAt
    (A : Tensor G d) (e : Edge G)
    (hu : LinearIndependent ℂ (A.component e.1.1))
    (hv : LinearIndependent ℂ (A.component e.1.2))
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (hO₁ : (localProjectorAt A hu).comp (O₁.comp (localProjectorAt A hu)) =
      physRealizeLocalOpAt A hu
        (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose))
    (hO₂ : (localProjectorAt A hv).comp (O₂.comp (localProjectorAt A hv)) =
      physRealizeLocalOpAt A hv
        (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M)) :
    localVirtualOpOfPhysicalOpAt A hu O₁ =
        localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose ∧
      localVirtualOpOfPhysicalOpAt A hv O₂ =
        localIncidentMatrixOp A (edgeRightIncident (G := G) e) M := by
  constructor
  · exact (edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt
      A e hu O₁ M).2 hO₁
  · exact (edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt
      A e hv O₂ M).2 hO₂

/-- Projected endpoint realizations of a common bond matrix give the endpoint
conclusion of physical-to-virtual insertion, under linear independence at the
two endpoints only.

This is the endpoint-injective form of
`edgePhysicalToVirtualInsertion_of_projected_realization_eq`: it takes the two
endpoint linear-independence facts (the pair supplied by
`EdgeBlockedThreeSiteInjective.endpoint_linearIndependent`) instead of the global
`IsVertexInjective` hypothesis. The conclusion is exactly the per-`M` body of the
existential in `physical_to_virtual_insertion`, so wiring that source theorem
through this lemma reduces it to supplying the common matrix, the projected
realizations, and image preservation from equality of the two endpoint physical
actions on the edge-blocked state.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, lines 363--486
of the local paper source. -/
theorem edgePhysicalToVirtualInsertion_of_endpointInjective
    (A : Tensor G d) (e : Edge G)
    (hu : LinearIndependent ℂ (A.component e.1.1))
    (hv : LinearIndependent ℂ (A.component e.1.2))
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (hO₁ : (localProjectorAt A hu).comp (O₁.comp (localProjectorAt A hu)) =
      physRealizeLocalOpAt A hu
        (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose))
    (hO₂ : (localProjectorAt A hv).comp (O₂.comp (localProjectorAt A hv)) =
      physRealizeLocalOpAt A hv
        (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M))
    (hO₁_image : ∀ c : LocalVirtualConfig A e.1.1 → ℂ,
      localProjectorAt A hu (O₁ (localTensorMap A e.1.1 c)) =
        O₁ (localTensorMap A e.1.1 c))
    (hO₂_image : ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
      localProjectorAt A hv (O₂ (localTensorMap A e.1.2 c)) =
        O₂ (localTensorMap A e.1.2 c)) :
    (∀ c : LocalVirtualConfig A e.1.1 → ℂ,
      O₁ (localTensorMap A e.1.1 c) =
        localTensorMap A e.1.1
          (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose c)) ∧
      ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
        O₂ (localTensorMap A e.1.2 c) =
          localTensorMap A e.1.2
            (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c) := by
  obtain ⟨hLeft, hRight⟩ :=
    edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eqAt
      A e hu hv O₁ O₂ M hO₁ hO₂
  constructor
  · intro c
    have hrealize :=
      localVirtualOpOfPhysicalOpAt_realizes_of_projector A hu O₁ hO₁_image c
    rw [hLeft] at hrealize
    exact hrealize.symm
  · intro c
    have hrealize :=
      localVirtualOpOfPhysicalOpAt_realizes_of_projector A hv O₂ hO₂_image c
    rw [hRight] at hrealize
    exact hrealize.symm

/-! ### Decoupling the three physical legs and inverting the middle block

The two endpoints `e.1.1`, `e.1.2` and the middle region `V \ {u, v}` are
pairwise disjoint, so a global physical configuration factors as three
independent legs. The merge map below reassembles them, and the
specialization of the resonate hypothesis at a merged configuration, combined
with the middle-block left inverse, removes the middle dependence. This is the
"invert $B_2$" reduction of `eq:inj_O->X_argument`.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, `eq:resonate`--
`eq:inj_O->X_argument`, lines 355--457 of the local paper source. -/

open Classical in
/-- Reassemble independent physical legs on the two endpoints and the middle
region into a global physical configuration. -/
noncomputable def edgeMergeConfig (e : Edge G)
    (τl τr : Fin d) (τm : EdgeMiddlePhysicalConfig (G := G) (d := d) e) : V → Fin d :=
  fun w => if w = e.1.1 then τl else if w = e.1.2 then τr
    else if h : w ∈ edgeMiddleVertices e then τm ⟨w, h⟩ else τl

omit [DecidableRel G.Adj] in
@[simp] theorem edgeMergeConfig_left (e : Edge G) (τl τr : Fin d)
    (τm : EdgeMiddlePhysicalConfig (G := G) (d := d) e) :
    edgeMergeConfig (G := G) (d := d) e τl τr τm e.1.1 = τl := by
  simp [edgeMergeConfig]

omit [DecidableRel G.Adj] in
@[simp] theorem edgeMergeConfig_right (e : Edge G) (τl τr : Fin d)
    (τm : EdgeMiddlePhysicalConfig (G := G) (d := d) e) :
    edgeMergeConfig (G := G) (d := d) e τl τr τm e.1.2 = τr := by
  have h : e.1.2 ≠ e.1.1 := (edgeLeft_ne_edgeRight e).symm
  simp [edgeMergeConfig, h]

omit [DecidableRel G.Adj] in
@[simp] theorem edgeMergeConfig_middle (e : Edge G) (τl τr : Fin d)
    (τm : EdgeMiddlePhysicalConfig (G := G) (d := d) e) :
    edgeMiddlePhysicalConfigOf (G := G) (d := d) e
        (edgeMergeConfig (G := G) (d := d) e τl τr τm) = τm := by
  funext w
  obtain ⟨w, hw⟩ := w
  have h1 : w ≠ e.1.1 := ((mem_edgeMiddleVertices_iff e w).mp hw).1
  have h2 : w ≠ e.1.2 := ((mem_edgeMiddleVertices_iff e w).mp hw).2
  simp [edgeMiddlePhysicalConfigOf, edgeMergeConfig, h1, h2, hw]

/-- At a merged physical configuration the open middle weight is the middle
tensor family evaluated on the chosen middle physical leg. -/
theorem edgeOpenMiddleWeight_merge (A : Tensor G d) (e : Edge G) (τl τr : Fin d)
    (τm : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (ρl : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (ρr : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    edgeOpenMiddleWeight (G := G) A e (edgeMergeConfig (G := G) (d := d) e τl τr τm) ρl ρr =
      edgeMiddleTensorFamily (G := G) A e (ρl, ρr) τm := by
  rw [edgeOpenMiddleWeight_eq_on, edgeMergeConfig_middle]
  rfl

/-- A sum over edge boundary configurations of a summand `f β` times the middle
tensor family is the middle tensor map applied to the per-residual-label
bond-index sum of `f`. This is the algebraic shape that the middle left inverse
peels. -/
theorem sum_edgeBoundary_eq_edgeMiddleTensorMap (A : Tensor G d) (e : Edge G)
    (τm : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (f : EdgeBoundaryConfig (G := G) A e → ℂ) :
    (∑ β : EdgeBoundaryConfig (G := G) A e,
        f β *
          edgeMiddleTensorFamily (G := G) A e (β.leftResidual, β.rightResidual) τm) =
      edgeMiddleTensorMap (G := G) A e
        (fun ρ => ∑ k : Fin (A.bondDim e),
          f { edgeIndex := k, leftResidual := ρ.1, rightResidual := ρ.2 }) τm := by
  classical
  rw [edgeMiddleTensorMap, Fintype.linearCombination_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [← Equiv.sum_comp (edgeBoundaryConfigEquivProd (G := G) A e).symm
        (fun β => f β *
          edgeMiddleTensorFamily (G := G) A e (β.leftResidual, β.rightResidual) τm)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => rfl

/-- The middle-inverted resonate identity.

After inverting the middle block of the edge-blocked three-site chain, the
equality of the two neighboring physical insertions (`hEq`) becomes, for each
choice of endpoint physical legs `τl, τr` and residual boundary labels
`ρl, ρr`, an equality of bond-contracted products of the two endpoint tensors.
The shared bond index `k` is summed on both sides; the left side carries the
left-endpoint physical operator `O₁`, the right side the right-endpoint operator
`O₂`.

This is the formal content of the first equality in `eq:inj_O->X_argument`: the
$D_{23}^{-1}$ middle contraction-inverse strips the middle block off
`eq:resonate`. The middle left inverse `edgeMiddleLeftInverse` is exactly the
inverse applied here.

Source: arXiv:1804.04964, Section 3, Lemma inj_isomorph, `eq:resonate`--
`eq:inj_O->X_argument`, lines 355--457 of the local paper source. -/
theorem resonate_middle_inverted (A : Tensor G d) (e : Edge G)
    (hMid : EdgeMiddleTensorInjective (G := G) A e)
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (hEq : ∀ σ : V → Fin d,
      (∑ β : EdgeBoundaryConfig (G := G) A e,
        O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2))
    (τl τr : Fin d)
    (ρl : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (ρr : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    (∑ k : Fin (A.bondDim e),
      O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e
        { edgeIndex := k, leftResidual := ρl, rightResidual := ρr })) τl *
        A.component e.1.2 (edgeRightLocalConfig (G := G) A e
          { edgeIndex := k, leftResidual := ρl, rightResidual := ρr }) τr) =
      ∑ k : Fin (A.bondDim e),
        A.component e.1.1 (edgeLeftLocalConfig (G := G) A e
          { edgeIndex := k, leftResidual := ρl, rightResidual := ρr }) τl *
          O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e
            { edgeIndex := k, leftResidual := ρl, rightResidual := ρr })) τr := by
  classical
  set fL : EdgeBoundaryConfig (G := G) A e → ℂ := fun β =>
    O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) τl *
      A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) τr with hfL
  set fR : EdgeBoundaryConfig (G := G) A e → ℂ := fun β =>
    A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) τl *
      O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) τr with hfR
  have hmapEq :
      edgeMiddleTensorMap (G := G) A e
          (fun ρ => ∑ k,
            fL { edgeIndex := k, leftResidual := ρ.1, rightResidual := ρ.2 }) =
        edgeMiddleTensorMap (G := G) A e
          (fun ρ => ∑ k,
            fR { edgeIndex := k, leftResidual := ρ.1, rightResidual := ρ.2 }) := by
    funext τm
    rw [← sum_edgeBoundary_eq_edgeMiddleTensorMap,
      ← sum_edgeBoundary_eq_edgeMiddleTensorMap]
    have h := hEq (edgeMergeConfig (G := G) (d := d) e τl τr τm)
    rw [edgeMergeConfig_left, edgeMergeConfig_right] at h
    simp only [edgeOpenMiddleWeight_merge] at h
    rw [hfL, hfR]
    refine Eq.trans ?_ (h.trans ?_)
    · exact Finset.sum_congr rfl fun β _ => by ring
    · exact Finset.sum_congr rfl fun β _ => by ring
  have hcoeff := edgeMiddleTensorMap_injective_of_injective hMid hmapEq
  have := congrFun hcoeff (ρl, ρr)
  simpa [hfL, hfR] using this

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

**Positive-bond hypothesis (faithfulness fix).** Without `hpos` the statement is
false: a zero-dimensional edge incident to an endpoint empties the edge boundary
configuration, so `hEq` holds vacuously while the recovery conclusion remains a
genuine constraint that fails for a nontrivial right-endpoint operator. The
checked counterexample is `PhysicalToVirtualInsertionStatement_false` in
`TNLean/PEPS/PhysicalToVirtualCounterexample.lean`. The hypothesis `hpos` (every
bond dimension positive) is the source's standing assumption that injective PEPS
have nonzero virtual bond spaces; the same defect was corrected for the
edge-blocked three-site injectivity (issue #1366).

**Proof status:** open (`sorry`). The middle-block half of
`eq:inj_O->X_argument` is now formalized: `edgeMiddleLeftInverse` is the
contraction-inverse of the blocked middle tensor, and `resonate_middle_inverted`
applies it to `hEq` to strip the middle block, leaving the bond-contracted
endpoint identity. The remaining step is the endpoint inversion: inverting the
right endpoint (resp. left endpoint) to read off `M` (resp. `V`) as a bond
matrix and reconciling them by full three-site injectivity. The current formal
status is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem physical_to_virtual_insertion
    (A : Tensor G d) (e : Edge G)
    (hA : EdgeBlockedThreeSiteInjective (G := G) A e)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f)
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
