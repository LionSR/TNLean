import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.Algebra
import TNLean.PEPS.InsertionAlgebra

/-!
# Region physical realization and the region insertion transfer

For a boundary edge `f` of an arbitrary finite region `R`, with single in-region
endpoint vertex `v`, this file realizes the region-inserted matrix insertion on
`f` as a physical operator at `v` and transfers it across `SameState` to build the
region analogue of `edgeTransferMatrix`. This supplies the data of a
`RegionInsertionTransfer` on `f`, the last gating ingredient of the per-edge gauge
for the normal PEPS Fundamental Theorem.

The development mirrors `TNLean.PEPS.InsertionAlgebra` piece by piece, with the
single in-region endpoint vertex `v` playing the role of the edge's right
endpoint:

* `regionBoundaryEdgeInVertex` is the in-region endpoint of a boundary edge; the
  edge is read as an incident edge `regionBoundaryEdgeInIncident` at that vertex.
* `regionRealizationSum_eq_regionInsertedCoeff` is the region analogue of
  `edgeRealizationSum_right_eq_sum_edgeBlockedCoeff`: the region-inserted
  coefficient equals a realization sum over physical configurations at `v`, with
  the inserted matrix carried by a physical operator at `v`.
* `regionRightInsertionOp` is the region analogue of `edgeRightInsertionOp`: the
  physical operator at `v` realizing the matrix insertion on `f`.
* `regionTransferMatrix` is the region analogue of `edgeTransferMatrix`: the
  matrix read off after transferring the realization across `SameState`.

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

/-! ### The in-region endpoint vertex of a boundary edge

A boundary edge of `R` has exactly one endpoint in `R`. That endpoint is the
vertex at which a matrix insertion on the edge is realized as a physical operator.
The edge, read as an incident edge at that vertex, is the distinguished bond of
the insertion. -/

/-- The in-region endpoint of a boundary edge `f` of `R`: the unique endpoint
lying in `R`. -/
noncomputable def regionBoundaryEdgeInVertex (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : V :=
  if f.1.1.1 ∈ R then f.1.1.1 else f.1.1.2

omit [Fintype V] [DecidableRel G.Adj] in
/-- The in-region endpoint of a boundary edge lies in `R`. -/
theorem regionBoundaryEdgeInVertex_mem (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeInVertex (G := G) R f ∈ R := by
  unfold regionBoundaryEdgeInVertex
  split_ifs with h
  · exact h
  · rcases f.2 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 h
    · exact h2

omit [Fintype V] [DecidableRel G.Adj] in
/-- The boundary edge `f` is incident to its in-region endpoint. -/
theorem regionBoundaryEdgeInVertex_incident (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    f.1.1.1 = regionBoundaryEdgeInVertex (G := G) R f ∨
      f.1.1.2 = regionBoundaryEdgeInVertex (G := G) R f := by
  unfold regionBoundaryEdgeInVertex
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The boundary edge `f` as an incident edge at its in-region endpoint vertex. -/
noncomputable def regionBoundaryEdgeInIncident (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    IncidentEdge G (regionBoundaryEdgeInVertex (G := G) R f) :=
  ⟨f.1, regionBoundaryEdgeInVertex_incident (G := G) R f⟩

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem regionBoundaryEdgeInIncident_edge (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    (regionBoundaryEdgeInIncident (G := G) R f).1 = f.1 := rfl

/-! ### Factoring the blocked-region weight through the in-region vertex tensor

The blocked-region weight reads its in-region endpoint vertex `v` only through
`v`'s tensor `A.component v`. Grouping the constrained global-configuration sum by
the local virtual configuration at `v`, the weight factors as the local tensor map
of `v` applied to a coefficient function (`regionOpenCoeff`) carrying the rest of
the region, evaluated at the physical leg `σ v`. This is the region analogue of
the right-endpoint factoring behind
`edgeRealizationSum_right_eq_sum_edgeBlockedCoeff`: the in-region endpoint vertex
plays the role of the edge's right endpoint, and the blocked-region weight of the
rest of `R` plays the role of the open middle weight. -/

/-- The local virtual configuration at the in-region vertex `v`, read off a global
virtual configuration. -/
noncomputable def regionVertexLocalConfig (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) (ζ : VirtualConfig A) :
    LocalVirtualConfig A (regionBoundaryEdgeInVertex (G := G) R f) :=
  fun ie => ζ ie.1

omit [Fintype V] in
@[simp] theorem regionVertexLocalConfig_apply (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) (ζ : VirtualConfig A)
    (ie : IncidentEdge G (regionBoundaryEdgeInVertex (G := G) R f)) :
    regionVertexLocalConfig (G := G) A R f ζ ie = ζ ie.1 := rfl

open scoped Classical in
/-- The product of the tensors at the region vertices other than the in-region
endpoint `v`, at a fixed global virtual configuration. -/
noncomputable def regionRestProd (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R) (ζ : VirtualConfig A) : ℂ :=
  ∏ w ∈ ({⟨regionBoundaryEdgeInVertex (G := G) R f,
        regionBoundaryEdgeInVertex_mem (G := G) R f⟩} :
      Finset {w : V // w ∈ R})ᶜ,
    A.component w.1 (fun ie => ζ ie.1) (σ w)

open scoped Classical in
/-- The coefficient function on local virtual configurations at the in-region
endpoint `v` through which the blocked-region weight factors: at each local
configuration `η` at `v`, the sum over global configurations restricting to `μ` on
the boundary and to `η` at `v`, of the product of the tensors at the remaining
region vertices. -/
noncomputable def regionOpenCoeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    LocalVirtualConfig A (regionBoundaryEdgeInVertex (G := G) R f) → ℂ :=
  fun η =>
    ∑ ζ ∈ Finset.univ.filter
      (fun ζ : VirtualConfig A =>
        regionBoundaryLabel (G := G) A R ζ = μ ∧
          regionVertexLocalConfig (G := G) A R f ζ = η),
      regionRestProd (G := G) A R f σ ζ

open scoped Classical in
/-- **Factoring the blocked-region weight through the in-region vertex tensor.**
The blocked-region weight equals the local tensor map of the in-region endpoint
`v`, applied to `regionOpenCoeff`, evaluated at the physical leg `σ v`. -/
theorem regionBlockedWeight_eq_localTensorMap (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedWeight (G := G) A R μ σ =
      localTensorMap A (regionBoundaryEdgeInVertex (G := G) R f)
          (regionOpenCoeff (G := G) A R f μ σ)
        (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩) := by
  classical
  set v := regionBoundaryEdgeInVertex (G := G) R f with hv
  set vmem : {w : V // w ∈ R} := ⟨v, regionBoundaryEdgeInVertex_mem (G := G) R f⟩ with hvmem
  -- Evaluate the local tensor map at `σ v`.
  rw [localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, regionOpenCoeff, Finset.sum_mul]
  -- The blocked-region weight, with the in-region vertex factored out of the product.
  rw [regionBlockedWeight]
  -- Group the constrained global sum by the local configuration at `v`.
  rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ))
    (fun ζ => regionVertexLocalConfig (G := G) A R f ζ)
    (fun ζ => ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w))]
  -- Swap to the local-config-indexed sum and match term by term.
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [Finset.filter_filter]
  refine Finset.sum_congr (by ext ζ; simp) (fun ζ hζ => ?_)
  -- On a fiber the vertex factor is constant, equal to `A.component v η (σ v)`.
  rw [Finset.mem_filter] at hζ
  obtain ⟨_, _, hηζ⟩ := hζ
  rw [regionRestProd,
    Fintype.prod_eq_mul_prod_compl vmem
      (fun w : {w : V // w ∈ R} => A.component w.1 (fun ie => ζ ie.1) (σ w))]
  -- The factored vertex term reads `η` through `regionVertexLocalConfig`.
  have hvterm : A.component vmem.1 (fun ie => ζ ie.1) (σ vmem) =
      A.component v η (σ vmem) := by
    have : (fun ie : IncidentEdge G v => ζ ie.1) = η := hηζ
    rw [hvmem, this]
  rw [hvterm]
  ring

end PEPS
end TNLean
