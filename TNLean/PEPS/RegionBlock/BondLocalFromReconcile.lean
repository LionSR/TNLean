import TNLean.PEPS.RegionBlock.ThreeBlockTransfer

/-!
# Bond locality of the transfer kernel from the region resonate reconcile

This file connects the two tracks of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, Lemma `inj_isomorph`) around the boundary edge `f`
of the red region `R`:

* the **block-frame predicate** `IsBondLocalTransferKernel`
  (`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`): for every inserted matrix `M`,
  the transfer kernel `transferCoeff A B R hRB hCB f M` is the incident-matrix
  kernel of some bond matrix on `f`; this is the residual open content of the
  block-frame coefficient transfer that the per-edge gauge consumes, and
* the **virtual-pullback predicate** `RegionResonateReconcile`
  (`TNLean.PEPS.RegionBlock.Recovery8`): for every inserted matrix `M`, the virtual
  pullback `localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA
  M.transpose)` of the transferred in-region endpoint operator is of incident-matrix
  form on the boundary leg `f`.

The bridge `isBondLocalTransferKernel_of_regionResonateReconcile` shows the first
follows from the second: the read-off
`transferCoeff_eq_incidentForm_of_virtualPullback_incidentForm`
(`TNLean.PEPS.RegionBlock.Recovery11`) turns the incident-matrix form of the virtual
pullback into the incident-matrix coupling form of the transfer kernel, which is
exactly `IsBondLocalTransferKernel`.

## What this does and does not settle

The virtual-pullback predicate `RegionResonateReconcile` and the read-off it feeds
are available only in the **vertex-injective** regime: they need the in-region
endpoint vertex `v` of `f` to be single-vertex linearly independent (`hvA`, `hvB`)
and both tensors vertex injective (`IsVertexInjective A`, `IsVertexInjective B`),
because the spanning of the closed state-vector coefficients at `v`
(`span_stateOpenCoeff_eq_top`, `TNLean.PEPS.RegionBlock.Recovery3`) — the
image-preservation root — is currently derived only from
`vertexComplementTensorInjective_of_isVertexInjective`. A single boundary vertex of
a normal (region-injective, not vertex-injective) tensor need not be injective, so
this bridge does **not** discharge `IsBondLocalTransferKernel` in the general normal
setting. It records the precise meeting point of the two tracks: in the
vertex-injective specialization the block-frame predicate is reachable, and the
remaining content of the general normal theorem is exactly the endpoint-vertex
spanning derived from blocked-region injectivity rather than single-vertex
injectivity. This obstruction is documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

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

/-! ### The block-frame predicate from the virtual-pullback predicate

The virtual-pullback predicate `RegionResonateReconcile` gives, for each inserted
matrix `M`, a matrix `P` on the second tensor's bond with
`localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose) =
localIncidentMatrixOp B (regionBoundaryEdgeInIncident R f) P`. Taking
`N := P.transpose`, the read-off
`transferCoeff_eq_incidentForm_of_virtualPullback_incidentForm`
(`TNLean.PEPS.RegionBlock.Recovery11`) turns this into the incident-matrix coupling
form of the transfer kernel, which is `transferCoeff A B R hRB hCB f M =
incidentKernel B R f N`, the body of `IsBondLocalTransferKernel`. -/

/-- **Bond locality from the region resonate reconcile.** If, for every inserted
matrix `M`, the virtual pullback of the transferred in-region endpoint operator is of
incident-matrix form on the boundary leg `f` (the predicate `RegionResonateReconcile`),
then the transfer kernel `transferCoeff A B R hRB hCB f M` is the incident-matrix
kernel of some bond matrix `N` on `f` for every `M`, that is,
`IsBondLocalTransferKernel A B R hRB hCB f` holds.

For each `M`, the reconcile supplies a matrix `P` with
`localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose) =
localIncidentMatrixOp B (regionBoundaryEdgeInIncident R f) P`; with `N := P.transpose`
the read-off `transferCoeff_eq_incidentForm_of_virtualPullback_incidentForm` gives the
incident-matrix coupling form of `transferCoeff`, which is exactly
`incidentKernel B R f N`.

The hypotheses `hvA`, `hvB`, `IsVertexInjective A`, `IsVertexInjective B` are those of
the read-off; they are the vertex-injective regime in which `RegionResonateReconcile`
itself is available. In the general normal setting these are absent, so this is the
meeting point of the two tracks, not a discharge of the block-frame predicate; see
the module docstring and `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
254--582 of `Papers/1804.04964/paper_normal.tex`. -/
theorem isBondLocalTransferKernel_of_regionResonateReconcile (A B : Tensor G d)
    (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (hrec : RegionResonateReconcile (G := G) A B R f hvA hvB) :
    IsBondLocalTransferKernel (G := G) A B R hRB hCB f := by
  classical
  intro M
  obtain ⟨P, hP⟩ := hrec M
  refine ⟨P.transpose, ?_⟩
  -- The reconcile's incident form, with `N := P.transpose`, feeds the read-off.
  have hform : localVirtualOpOfPhysicalOpAt B hvB
      (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f)
        P.transpose.transpose := by
    rw [Matrix.transpose_transpose]; exact hP
  funext μ ν'
  rw [transferCoeff_eq_incidentForm_of_virtualPullback_incidentForm A B R hRB hCB f
      hvA hvB hvAout hAB hA hB hposA hposB hDim M P.transpose hform μ ν',
    incidentKernel]

/-! ### The coefficient transfer from the region resonate reconcile

Composing the bond-locality bridge with `coeffTransfer_of_bondLocal`
(`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`) gives the coefficient transfer
directly from the region resonate reconcile, in the vertex-injective regime. This
is the form the per-edge gauge consumes. -/

/-- **The coefficient transfer from the region resonate reconcile.** In the
vertex-injective regime, the region resonate reconcile yields, for every inserted
matrix `M`, a bond matrix `N` on the second tensor whose region-inserted coefficient
matches the first tensor's at every physical configuration.

The reconcile gives `IsBondLocalTransferKernel`
(`isBondLocalTransferKernel_of_regionResonateReconcile`), which the bond-locality
bridge `coeffTransfer_of_bondLocal` turns into the coefficient transfer.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coeffTransfer_of_regionResonateReconcile (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (hrec : RegionResonateReconcile (G := G) A B R f hvA hvB) :
    ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
          regionInsertedCoeff (G := G) A R f M σ τ =
            regionInsertedCoeff (G := G) B R f N σ τ :=
  coeffTransfer_of_bondLocal A B R hRA hRB hCA hCB hAB hposA hposB f
    (isBondLocalTransferKernel_of_regionResonateReconcile A B R hRB hCB f
      hvA hvB hvAout hAB hA hB hposA hposB hDim hrec)

end PEPS
end TNLean
