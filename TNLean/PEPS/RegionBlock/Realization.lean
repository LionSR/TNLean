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

/-! ### The vertex-opened state vector and its physical realization

The realization sum that transfers across `SameState` is built from the closed
state coefficient, viewed as a vector in the physical leg of the in-region
endpoint vertex `v`. As a function of that leg, the closed state coefficient
factors through `v`'s tensor, so it lies in the image of the local tensor map at
`v`. A physical operator realizing a matrix insertion on the boundary edge `f`
then acts on this vector, and the resulting realization sum equals the
region-inserted coefficient. The state vector is tensor-independent up to
`SameState`, which is what carries the realization sum from one tensor to the
other. -/

/-- The closed state vector at the in-region endpoint vertex `v`: the closed state
coefficient of the assembled physical configuration as a function of the physical
leg at `v`. -/
noncomputable def regionStateVec (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : Fin d → ℂ :=
  fun a =>
    stateCoeff A (assembleRegionσ (V := V) (d := d) R
      (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
        regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) τ)

omit [DecidableRel G.Adj] in
/-- Updating the in-region physical configuration at the endpoint vertex `v` and
then assembling equals assembling and then updating the global configuration at
`v`. -/
theorem assembleRegionσ_update (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    {v : V} (hv : v ∈ R) (a : Fin d) :
    assembleRegionσ (V := V) (d := d) R (Function.update σ ⟨v, hv⟩ a) τ =
      Function.update (assembleRegionσ (V := V) (d := d) R σ τ) v a := by
  funext w
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self]
    have : assembleRegionσ (V := V) (d := d) R (Function.update σ ⟨w, hv⟩ a) τ w =
        (Function.update σ ⟨w, hv⟩ a) ⟨w, hv⟩ :=
      assembleRegionσ_mem (V := V) (d := d) R (Function.update σ ⟨w, hv⟩ a) τ ⟨w, hv⟩
    rw [this, Function.update_self]
  · rw [Function.update_of_ne hw]
    unfold assembleRegionσ
    by_cases hwR : w ∈ R
    · rw [dif_pos hwR, dif_pos hwR, Function.update_of_ne]
      intro hc
      exact hw (congrArg Subtype.val hc)
    · rw [dif_neg hwR, dif_neg hwR]

open scoped Classical in
/-- The coefficient function on local virtual configurations at the in-region
endpoint `v` through which the closed state vector factors: the closed state
coefficient grouped by the local configuration at `v`, with `v`'s tensor factor
removed and `v`'s physical leg left open. -/
noncomputable def stateOpenCoeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    LocalVirtualConfig A (regionBoundaryEdgeInVertex (G := G) R f) → ℂ :=
  fun η =>
    ∑ ζ ∈ Finset.univ.filter
      (fun ζ : VirtualConfig A =>
        (fun ie : IncidentEdge G (regionBoundaryEdgeInVertex (G := G) R f) => ζ ie.1) = η),
      ∏ w ∈ ({regionBoundaryEdgeInVertex (G := G) R f} : Finset V)ᶜ,
        A.component w (fun ie => ζ ie.1)
          (assembleRegionσ (V := V) (d := d) R σ τ w)

open scoped Classical in
/-- **Factoring the closed state vector through the in-region vertex tensor.** The
closed state vector at the in-region endpoint `v` equals the local tensor map of
`v` applied to `stateOpenCoeff`. -/
theorem regionStateVec_eq_localTensorMap (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionStateVec (G := G) A R f σ τ =
      localTensorMap A (regionBoundaryEdgeInVertex (G := G) R f)
        (stateOpenCoeff (G := G) A R f σ τ) := by
  classical
  set v := regionBoundaryEdgeInVertex (G := G) R f with hv
  set vmem : {w : V // w ∈ R} := ⟨v, regionBoundaryEdgeInVertex_mem (G := G) R f⟩ with hvmem
  funext a
  rw [regionStateVec, localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, stateOpenCoeff, Finset.sum_mul]
  -- Expand the closed state coefficient over global configurations.
  rw [stateCoeff]
  -- Update at `v` then assemble equals assemble then update globally.
  rw [show assembleRegionσ (V := V) (d := d) R (Function.update σ vmem a) τ =
        Function.update (assembleRegionσ (V := V) (d := d) R σ τ) v a from
      assembleRegionσ_update (V := V) (d := d) R σ τ vmem.2 a]
  -- Group the global sum by the local configuration at `v`.
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (VirtualConfig A))
    (fun ζ => (fun ie : IncidentEdge G v => ζ ie.1))
    (fun ζ => ∏ w : V, A.component w (fun ie => ζ ie.1)
      (Function.update (assembleRegionσ (V := V) (d := d) R σ τ) v a w))]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  refine Finset.sum_congr rfl (fun ζ hζ => ?_)
  rw [Finset.mem_filter] at hζ
  obtain ⟨_, hηζ⟩ := hζ
  -- Factor the in-region vertex out of the global product.
  rw [Fintype.prod_eq_mul_prod_compl v
      (fun w : V => A.component w (fun ie => ζ ie.1)
        (Function.update (assembleRegionσ (V := V) (d := d) R σ τ) v a w))]
  -- The vertex factor reads `a` and the local configuration `η`.
  have hvterm : A.component v (fun ie => ζ ie.1)
        (Function.update (assembleRegionσ (V := V) (d := d) R σ τ) v a v) =
      A.component v η a := by
    rw [Function.update_self]
    have : (fun ie : IncidentEdge G v => ζ ie.1) = η := hηζ
    rw [this]
  -- The remaining product reads the unchanged physical legs away from `v`.
  have hrest : (∏ w ∈ ({v} : Finset V)ᶜ,
        A.component w (fun ie => ζ ie.1)
          (Function.update (assembleRegionσ (V := V) (d := d) R σ τ) v a w)) =
      ∏ w ∈ ({v} : Finset V)ᶜ,
        A.component w (fun ie => ζ ie.1)
          (assembleRegionσ (V := V) (d := d) R σ τ w) := by
    refine Finset.prod_congr rfl (fun w hw => ?_)
    rw [Finset.mem_compl, Finset.mem_singleton] at hw
    rw [Function.update_of_ne hw]
  rw [hvterm, hrest]
  ring

end PEPS
end TNLean
