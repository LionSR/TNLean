import TNLean.PEPS.RegionBlock.CoarseThreeSite6

/-!
# The inserted-coefficient descent for the normal PEPS theorem

The fiber-collapse `TNLean.PEPS.stateCoeff_coarseTensor_collapse` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite5` glues the coarse three-site closed state to
the original closed state. This file mirrors that collapse with a matrix inserted on
the coarse red-to-blue super-bond, descending the coarse edge-inserted coefficient
`TNLean.PEPS.edgeInsertedCoeff` of the coarse tensor at its `r-b` edge to the
whole-bundle red inserted coefficient `TNLean.PEPS.redBundleInsertedCoeff` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite6`.

The coarse `r-b` super-bond carries the whole bundle of red-to-blue crossing edges
(`TNLean.PEPS.CrossingConfig`), so a matrix on that super-bond couples every
red-to-blue crossing. The descent therefore lands on the whole-crossing-bundle
inserted coefficient, the analogue of `regionInsertedCoeff` whose inserted matrix
acts on the whole red-to-blue crossing bundle.

The route first records a tensor-agnostic expansion of `edgeInsertedCoeff` at an
edge `e` as a sum over *pairs* of global virtual configurations agreeing on every
edge other than `e`, with the inserted matrix coupling their two values on `e`
(`edgeInsertedCoeff_eq_pairSum`). This is the open-bond generalization of
`TNLean.PEPS.edgeBlockedCoeff_eq_stateCoeff`, where the single distinguished-edge
index is split into an independent left and right index.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 254--583 (the injective three-site comparison) and 1205--1210,
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Two global configurations agreeing off an edge

The open-bond expansion of the edge-inserted coefficient couples two global virtual
configurations that carry the same value on every edge other than the distinguished
one. The inserted matrix couples their two values on the distinguished edge. -/

/-- Two global virtual configurations agree off the edge `e` when they carry the same
value on every edge other than `e`. -/
def AgreeOffEdge (A : Tensor G d) (e : Edge G) (ζL ζR : VirtualConfig A) : Prop :=
  ∀ f : Edge G, f ≠ e → ζL f = ζR f

instance (A : Tensor G d) (e : Edge G) (ζL ζR : VirtualConfig A) :
    Decidable (AgreeOffEdge (G := G) A e ζL ζR) := by
  unfold AgreeOffEdge; infer_instance

omit [DecidableRel G.Adj] in
/-- An edge incident to a middle vertex of `e` is not `e` itself. -/
theorem incidentMiddle_ne (e : Edge G) {v : V} (hv : v ∈ edgeMiddleVertices e)
    (ie : IncidentEdge G v) : ie.1 ≠ e := by
  intro hie
  have hvne := (mem_edgeMiddleVertices_iff e v).mp hv
  rcases ie.2 with hleft | hright
  · exact hvne.1 (hleft.symm.trans (congrArg (fun f : Edge G => f.1.1) hie))
  · exact hvne.2 (hright.symm.trans (congrArg (fun f : Edge G => f.1.2) hie))

/-- On any edge incident to a middle vertex of `e`, two configurations agreeing off
`e` coincide. -/
theorem AgreeOffEdge.middle (A : Tensor G d) (e : Edge G) {ζL ζR : VirtualConfig A}
    (h : AgreeOffEdge (G := G) A e ζL ζR) {v : V} (hv : v ∈ edgeMiddleVertices e)
    (ie : IncidentEdge G v) : ζL ie.1 = ζR ie.1 :=
  h ie.1 (incidentMiddle_ne (G := G) e hv ie)

/-! ### The open-bond expansion of the edge-inserted coefficient

The edge-inserted coefficient is the closed-state contraction with the distinguished
bond `e` cut into an independent left and right index coupled by the inserted matrix.
The left index is carried by a full global virtual configuration `ζL`; the right
index `y` overrides the value of `ζL` on `e` for the right endpoint only. The middle
and the left endpoint read `ζL`; the right endpoint reads `ζL` with `e` set to `y`.
This is the open-bond generalization of `edgeBlockedCoeff_eq_stateCoeff`. -/

/-- The right-side reading of a global virtual configuration with the distinguished
edge index overridden by `y`: it equals `ζL` everywhere except on `e`, where it is
`y`. -/
noncomputable def overrideEdge (A : Tensor G d) (e : Edge G) (ζL : VirtualConfig A)
    (y : Fin (A.bondDim e)) : VirtualConfig A :=
  Function.update ζL e y

omit [Fintype V] in
@[simp] theorem overrideEdge_edge (A : Tensor G d) (e : Edge G) (ζL : VirtualConfig A)
    (y : Fin (A.bondDim e)) : overrideEdge (G := G) A e ζL y e = y := by
  simp [overrideEdge]

omit [Fintype V] in
@[simp] theorem overrideEdge_ne (A : Tensor G d) (e : Edge G) (ζL : VirtualConfig A)
    (y : Fin (A.bondDim e)) {f : Edge G} (hf : f ≠ e) :
    overrideEdge (G := G) A e ζL y f = ζL f := by
  simp [overrideEdge, hf]

omit [Fintype V] in
/-- The override agrees with `ζL` off `e`. -/
theorem agreeOffEdge_overrideEdge (A : Tensor G d) (e : Edge G) (ζL : VirtualConfig A)
    (y : Fin (A.bondDim e)) : AgreeOffEdge (G := G) A e ζL (overrideEdge (G := G) A e ζL y) :=
  fun _ hf => (overrideEdge_ne (G := G) A e ζL y hf).symm

omit [Fintype V] in
/-- The right endpoint local configuration reconstructed from the right index `y` and
a full configuration's right residual is the right-incident reading of the override of
that configuration with `y` on `e`. -/
theorem edgeRightLocalConfig_override (A : Tensor G d) (e : Edge G) (ζL : VirtualConfig A)
    (y : Fin (A.bondDim e)) :
    edgeRightLocalConfig (G := G) A e
        { edgeIndex := y
          leftResidual := (edgeBoundaryOfVirtualConfig (G := G) A e ζL).leftResidual
          rightResidual := (edgeBoundaryOfVirtualConfig (G := G) A e ζL).rightResidual } =
      (fun ie : IncidentEdge G e.1.2 => overrideEdge (G := G) A e ζL y ie.1) := by
  funext ie
  by_cases hie : ie = edgeRightIncident (G := G) e
  · subst ie
    rw [edgeRightLocalConfig_edgeIndex]
    simp only [edgeRightIncident, overrideEdge, Function.update_self]
  · rw [edgeRightLocalConfig_residual (G := G) A e _ ⟨ie, hie⟩]
    have hne : ie.1 ≠ e := fun h => hie (Subtype.ext h)
    rw [overrideEdge_ne (G := G) A e ζL y hne]
    rfl

/-- **The open-bond expansion of the edge-inserted coefficient.** The edge-inserted
coefficient is the sum, over a global virtual configuration `ζL` and an independent
right-endpoint index `y` on the distinguished edge `e`, of the inserted matrix
coupling `ζL`'s edge value to `y`, times the left endpoint and middle product read
from `ζL` and the right endpoint read from `ζL` with its `e`-value overridden by `y`.

This is the open-bond generalization of `edgeBlockedCoeff_eq_stateCoeff`: cutting the
distinguished bond into an independent left value (`ζL e`) and right value (`y`)
coupled by the inserted matrix, with everything off `e` shared.

Source: arXiv:1804.04964, Section 3, the matrix insertion on the distinguished edge,
lines 254--583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem edgeInsertedCoeff_eq_pairSum (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := G) A e σ M =
      ∑ ζL : VirtualConfig A, ∑ y : Fin (A.bondDim e),
        A.component e.1.1 (fun ie => ζL ie.1) (σ e.1.1) *
          M (ζL e) y *
          (∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => ζL ie.1) (σ v)) *
          A.component e.1.2 (fun ie => overrideEdge (G := G) A e ζL y ie.1) (σ e.1.2) := by
  classical
  rw [edgeInsertedCoeff]
  -- Reindex `EdgeInsertedBoundaryConfig` as `(EdgeBoundaryConfig × right index y)` and
  -- rewrite each summand into boundary form, restoring the ordinary middle weight.
  rw [← Equiv.sum_comp (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e)
    (fun β => A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      M β.leftEdgeIndex β.rightEdgeIndex *
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e β) (σ e.1.2)),
    Fintype.sum_sigma' (fun (β0 : EdgeBoundaryConfig (G := G) A e) (y : Fin (A.bondDim e)) =>
      A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e
            (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩))
          (σ e.1.1) *
        M (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).leftEdgeIndex
          (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).rightEdgeIndex *
        edgeOpenMiddleWeight (G := G) A e σ
          (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).leftResidual
          (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).rightResidual *
        A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e
            (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩))
          (σ e.1.2))]
  have hsummand : ∀ (β0 : EdgeBoundaryConfig (G := G) A e) (y : Fin (A.bondDim e)),
      A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e
            (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩))
          (σ e.1.1) *
        M (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).leftEdgeIndex
          (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).rightEdgeIndex *
        edgeOpenMiddleWeight (G := G) A e σ
          (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).leftResidual
          (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩).rightResidual *
        A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e
            (edgeBoundaryRightIndexEquivInsertedBoundaryConfig (G := G) A e ⟨β0, y⟩))
          (σ e.1.2) =
      A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β0) (σ e.1.1) *
        M β0.edgeIndex y *
        edgeMiddleWeight (G := G) A e σ β0 *
        A.component e.1.2 (edgeRightLocalConfig (G := G) A e
          { edgeIndex := y, leftResidual := β0.leftResidual,
            rightResidual := β0.rightResidual }) (σ e.1.2) := by
    intro β0 y
    rw [edgeMiddleWeight_eq_edgeOpenMiddleWeight]
    rfl
  rw [Finset.sum_congr rfl (fun β0 _ => Finset.sum_congr rfl (fun y _ => hsummand β0 y))]
  -- Expand the middle weight and reindex `(β0, middle config)` to a full config `ζL`.
  -- Both sides are brought to `y` outer, `(β0 / ζL)` inner.
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  calc
    (∑ β0 : EdgeBoundaryConfig (G := G) A e,
        A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β0) (σ e.1.1) *
          M β0.edgeIndex y *
          edgeMiddleWeight (G := G) A e σ β0 *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e
            { edgeIndex := y, leftResidual := β0.leftResidual,
              rightResidual := β0.rightResidual }) (σ e.1.2))
        = ∑ β0 : EdgeBoundaryConfig (G := G) A e,
            ∑ η : EdgeMiddleConfig (G := G) A e β0,
              A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β0) (σ e.1.1) *
                M β0.edgeIndex y *
                (∏ v ∈ edgeMiddleVertices e,
                  A.component v (fun ie => η.1 ie.1) (σ v)) *
                A.component e.1.2 (edgeRightLocalConfig (G := G) A e
                  { edgeIndex := y, leftResidual := β0.leftResidual,
                    rightResidual := β0.rightResidual }) (σ e.1.2) := by
          refine Finset.sum_congr rfl (fun β0 _ => ?_)
          rw [edgeMiddleWeight, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ x : (Σ β0 : EdgeBoundaryConfig (G := G) A e, EdgeMiddleConfig (G := G) A e β0),
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e x.1) (σ e.1.1) *
            M x.1.edgeIndex y *
            (∏ v ∈ edgeMiddleVertices e,
              A.component v (fun ie => x.2.1 ie.1) (σ v)) *
            A.component e.1.2 (edgeRightLocalConfig (G := G) A e
              { edgeIndex := y, leftResidual := x.1.leftResidual,
                rightResidual := x.1.rightResidual }) (σ e.1.2) := by
        rw [← Fintype.sum_sigma']
    _ = ∑ ζL : VirtualConfig A,
          A.component e.1.1 (fun ie => ζL ie.1) (σ e.1.1) *
            M (ζL e) y *
            (∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => ζL ie.1) (σ v)) *
            A.component e.1.2 (fun ie => overrideEdge (G := G) A e ζL y ie.1) (σ e.1.2) := by
        let φ := virtualConfigEquivEdgeBoundary (G := G) A e
        rw [← Equiv.sum_comp φ]
        refine Finset.sum_congr rfl (fun ζL _ => ?_)
        have hmatch : edgeBoundaryMatches (G := G) A e
            (edgeBoundaryOfVirtualConfig (G := G) A e ζL) ζL := by simp
        have hleft := edgeLeftLocalConfig_eq_of_boundaryMatches
          (G := G) A e (edgeBoundaryOfVirtualConfig (G := G) A e ζL) ζL hmatch
        have hright := edgeRightLocalConfig_override (G := G) A e ζL y
        simp only [φ, virtualConfigEquivEdgeBoundary, Equiv.coe_fn_mk]
        rw [hleft, hright]
        rfl

end PEPS
end TNLean
