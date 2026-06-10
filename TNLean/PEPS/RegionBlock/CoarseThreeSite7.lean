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

/-! ### The M-coupled three-region expansion of the coarse edge-inserted coefficient

Specializing the open-bond expansion to the coarse three-site tensor at its `r-b`
edge: the coarse super-site components are the original blocked-region weights, the
coarse middle super-site (the complement) is the only middle vertex, and the inserted
matrix couples the red super-site's `r-b` super-bond value to the blue super-site's.
The red and complement super-sites read the configuration `ηL`; the blue super-site
reads `ηL` with its `r-b` super-bond overridden by the free index `y`. -/

variable {A : Tensor G d}

/-- **The M-coupled three-region expansion.** The coarse edge-inserted coefficient at
the `r-b` super-bond is the sum, over a coarse virtual configuration `ηL` and a free
right `r-b` super-bond index `y`, of the inserted matrix coupling the two `r-b`
super-bond values, times the red weight read from `ηL`, the complement weight read
from `ηL`, and the blue weight read from `ηL` with its `r-b` super-bond overridden
by `y`.

Source: arXiv:1804.04964, Section 3, the matrix insertion on the distinguished edge,
lines 254--583 and 1449--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem edgeInsertedCoeff_coarseTensor_eq_threeRegionSum
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (s : Fin 3 → Fin (coarseDim V d))
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ) :
    edgeInsertedCoeff (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB s M =
      ∑ ηL : VirtualConfig (F.frame.coarseTensor),
        ∑ y : Fin (F.frame.coarseBondDim coarseEdgeRB),
          M (ηL coarseEdgeRB) y *
            regionBlockedWeight (G := G) A F.frame.red
              (F.frame.legEquivRed (fun ie => ηL ie.1)) (coarseProj F.frame.red (s 0)) *
            regionBlockedWeight (G := G) A F.frame.complement
              (F.frame.legEquivComplement (fun ie => ηL ie.1))
                (coarseProj F.frame.complement (s 2)) *
            regionBlockedWeight (G := G) A F.frame.blue
              (F.frame.legEquivBlue
                (fun ie => overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB
                  ηL y ie.1)) (coarseProj F.frame.blue (s 1)) := by
  classical
  rw [edgeInsertedCoeff_eq_pairSum]
  refine Finset.sum_congr rfl (fun ηL _ => Finset.sum_congr rfl (fun y _ => ?_))
  -- The coarse super-site components are the three original blocked-region weights.
  have hred : (F.frame.coarseTensor).component coarseEdgeRB.1.1
        (fun ie => ηL ie.1) (s coarseEdgeRB.1.1) =
      regionBlockedWeight (G := G) A F.frame.red
        (F.frame.legEquivRed (fun ie => ηL ie.1)) (coarseProj F.frame.red (s 0)) :=
    F.frame.coarseTensor_component_red _ _
  have hblue : (F.frame.coarseTensor).component coarseEdgeRB.1.2
        (fun ie => overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y ie.1)
        (s coarseEdgeRB.1.2) =
      regionBlockedWeight (G := G) A F.frame.blue
        (F.frame.legEquivBlue
          (fun ie => overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB
            ηL y ie.1)) (coarseProj F.frame.blue (s 1)) :=
    F.frame.coarseTensor_component_blue _ _
  have hmiddle : (∏ v ∈ edgeMiddleVertices (G := coarseGraph) coarseEdgeRB,
        (F.frame.coarseTensor).component v (fun ie => ηL ie.1) (s v)) =
      regionBlockedWeight (G := G) A F.frame.complement
        (F.frame.legEquivComplement (fun ie => ηL ie.1))
          (coarseProj F.frame.complement (s 2)) := by
    rw [show edgeMiddleVertices (G := coarseGraph) coarseEdgeRB = {2} from by decide,
      Finset.prod_singleton]
    exact F.frame.coarseTensor_component_complement _ _
  rw [hred, hblue, hmiddle]
  ring

/-! ### The override reads the alternate `r-b` super-bond

Overriding a coarse virtual configuration on the `r-b` super-edge changes only the
`r-b` super-bond value; every other super-bond is untouched. The blue super-site's
leg identification reads the `r-b` crossings through the overridden value and the
`b-c` crossings unchanged. -/

/-- The override of a coarse configuration agrees with it on the `r-c` and `b-c`
super-edges. -/
theorem overrideEdge_coarse_rc (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ηL : VirtualConfig (F.frame.coarseTensor)) (y : Fin (F.frame.coarseBondDim coarseEdgeRB)) :
    overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y coarseEdgeRC =
      ηL coarseEdgeRC :=
  overrideEdge_ne (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y
    (by decide)

/-- The override of a coarse configuration agrees with it on the `b-c` super-edge. -/
theorem overrideEdge_coarse_bc (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ηL : VirtualConfig (F.frame.coarseTensor)) (y : Fin (F.frame.coarseBondDim coarseEdgeRB)) :
    overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y coarseEdgeBC =
      ηL coarseEdgeBC :=
  overrideEdge_ne (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y
    (by decide)

/-- The override of a coarse configuration reads the alternate value on the `r-b`
super-edge. -/
@[simp] theorem overrideEdge_coarse_rb (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ηL : VirtualConfig (F.frame.coarseTensor)) (y : Fin (F.frame.coarseBondDim coarseEdgeRB)) :
    overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y coarseEdgeRB = y :=
  overrideEdge_edge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y

/-! ### The blue boundary configuration of the override

The blue super-site's leg identification of the override reads the `r-b` crossings
through the alternate super-bond value `y` and the `b-c` crossings through the
unchanged value. The blue boundary configuration the override induces is therefore
the one whose `r-b` crossings come from `y` and whose `b-c` crossings come from
`ηL`. -/

variable [DecidableEq V]

/-- **The blue leg identification of the override.** The blue super-site reads the
override on a blue boundary edge crossing to red through the alternate `r-b`
super-bond value `y`, and on a blue boundary edge crossing to the complement through
the unchanged `b-c` super-bond value. -/
theorem legEquivBlue_overrideEdge_apply
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (ηL : VirtualConfig (F.frame.coarseTensor)) (y : Fin (F.frame.coarseBondDim coarseEdgeRB))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G) F.frame.blue b}) :
    (F.frame.legEquivBlue
        (fun ie => overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y ie.1)
        b : Fin (A.bondDim b.1)) =
      if hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1 then
        (F.bondModel coarseEdgeRB y ⟨b.1, hb⟩ : Fin (A.bondDim b.1))
      else
        (F.bondModel coarseEdgeBC (ηL coarseEdgeBC)
          ⟨b.1, (F.frame.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb⟩ :
          Fin (A.bondDim b.1)) := by
  rw [F.legEquivBlue_apply_eq hP _ b]
  simp only [overrideEdge, Function.update_self,
    Function.update_of_ne (show coarseEdgeBC ≠ coarseEdgeRB by decide)]

/-! ### The bond-model-conjugated matrix on the red-to-blue crossing bundle

A matrix on the coarse `r-b` super-bond is carried, through the `r-b` bond model, to a
matrix on the whole red-to-blue crossing bundle. This is the inserted matrix the
whole-bundle red inserted coefficient `redBundleInsertedCoeff` reads. -/

/-- **The bond-model-conjugated matrix.** A matrix on the coarse `r-b` super-bond,
conjugated by the `r-b` bond model into a matrix on the red-to-blue crossing
configurations. -/
noncomputable def bondModelMatrix (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ) :
    Matrix (CrossingConfig (G := G) A F.frame.red F.frame.blue)
      (CrossingConfig (G := G) A F.frame.red F.frame.blue) ℂ :=
  fun p q => M ((F.bondModel coarseEdgeRB).symm p) ((F.bondModel coarseEdgeRB).symm q)

omit [DecidableEq V] in
/-- The conjugated matrix reads the coarse matrix at the bond-model preimages of the
two crossing labels. -/
theorem bondModelMatrix_apply (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ)
    (p q : CrossingConfig (G := G) A F.frame.red F.frame.blue) :
    bondModelMatrix (G := G) F M p q =
      M ((F.bondModel coarseEdgeRB).symm p) ((F.bondModel coarseEdgeRB).symm q) := rfl

omit [DecidableEq V] in
/-- The conjugated matrix at the bond-model images of two coarse super-bond values is
the coarse matrix at those values. -/
theorem bondModelMatrix_bondModel (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ)
    (a b : Fin (F.frame.coarseBondDim coarseEdgeRB)) :
    bondModelMatrix (G := G) F M (F.bondModel coarseEdgeRB a) (F.bondModel coarseEdgeRB b) =
      M a b := by
  rw [bondModelMatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ### The `r-b` super-bond value read from a blue crossing label

The free right index `y` of the open-bond expansion is recovered, through the `r-b`
bond model, from a blue configuration's red-to-blue crossing label: the coarse `r-b`
super-bond value whose bond model reads that crossing label. -/

/-- The coarse `r-b` super-bond value whose `r-b` bond model is a blue configuration's
red-to-blue crossing label. -/
noncomputable def blueRBIndex (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζb : VirtualConfig A) : Fin (F.frame.coarseBondDim coarseEdgeRB) :=
  (F.bondModel coarseEdgeRB).symm
    (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue)

omit [DecidableEq V] in
/-- The `r-b` bond model of `blueRBIndex` is the blue configuration's red-to-blue
crossing label. -/
@[simp] theorem bondModel_blueRBIndex (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζb : VirtualConfig A) :
    F.bondModel coarseEdgeRB (blueRBIndex (G := G) F ζb) =
      (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue) := by
  rw [blueRBIndex, Equiv.apply_symm_apply]

/-! ### The blue-override boundary recovery

A coarse configuration `ηL` and a free right index `y` induce, through the override,
the blue boundary configuration of a global configuration `ζb` exactly when the `r-b`
bond model reads `y` as `ζb`'s red-to-blue crossing label and the `b-c` bond model
reads `ηL`'s `b-c` super-bond as `ζb`'s blue-to-complement crossing label. This is the
override analogue of `legEquivBlue_eq_of_bondModel`. -/

/-- **Blue-override boundary recovery.** If the `r-b` bond model of `y` reads `ζb`'s
red-to-blue crossing label and the `b-c` bond model of `ηL`'s `b-c` super-bond reads
`ζb`'s blue-to-complement crossing label, the blue boundary configuration the override
induces is `ζb`'s blue boundary label. -/
theorem legEquivBlue_overrideEdge_eq_of_bondModel
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (ηL : VirtualConfig (F.frame.coarseTensor)) (y : Fin (F.frame.coarseBondDim coarseEdgeRB))
    (ζb : VirtualConfig A)
    (hrb : F.bondModel coarseEdgeRB y =
      (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue))
    (hbc : F.bondModel coarseEdgeBC (ηL coarseEdgeBC) =
      crossingLabel (G := G) A F.frame.blue F.frame.complement ζb) :
    F.frame.legEquivBlue
        (fun ie => overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB ηL y ie.1) =
      regionBoundaryLabel (G := G) A F.frame.blue ζb := by
  funext b
  rw [legEquivBlue_overrideEdge_apply F hP ηL y b]
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1
  · rw [dif_pos hb]
    have := congrFun hrb ⟨b.1, hb⟩; rw [this]; rfl
  · rw [dif_neg hb]
    have hc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb
    have := congrFun hbc ⟨b.1, hc⟩
    rw [crossingLabel_apply] at this; rw [this]; rfl

/-! ### The constraint set of the M-coupled descent

For a fixed triple `(ζr, ζb, ζc)`, the pairs `(ηL, y)` whose three induced region
boundary configurations equal the triple's region boundary labels (with the blue one
read from the override) form a singleton when the triple agrees away from the
red-to-blue crossings, and are empty otherwise. The realizing pair is the coarse
configuration realising the crossing labels of `(ζr, ζc)` together with the right
index recovered from `ζb`'s red-to-blue crossing label. -/

/-- The realizing pair of the M-coupled constraint set: the coarse configuration
realising the crossing labels of the red and complement configurations, together with
the right index recovered from the blue configuration's red-to-blue crossing label. -/
noncomputable def pairToEtaY (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζc : VirtualConfig A) (ζb : VirtualConfig A) :
    VirtualConfig (F.frame.coarseTensor) × Fin (F.frame.coarseBondDim coarseEdgeRB) :=
  (tripleToEta F ζr ζc, blueRBIndex (G := G) F ζb)

/-- The realizing pair's coarse configuration reads `ζr`'s red boundary label. -/
theorem legEquivRed_pairToEtaY (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (ζr ζc ζb : VirtualConfig A) :
    F.frame.legEquivRed (fun ie => (pairToEtaY (G := G) F ζr ζc ζb).1 ie.1) =
      regionBoundaryLabel (G := G) A F.frame.red ζr :=
  legEquivRed_eq_of_bondModel F hP _ ζr (tripleToEta_rb F ζr ζc) (tripleToEta_rc F ζr ζc)

/-- The realizing pair's coarse configuration reads `ζc`'s complement boundary label. -/
theorem legEquivComplement_pairToEtaY (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (ζr ζc ζb : VirtualConfig A)
    (hrc : crossingLabel (G := G) A F.frame.red F.frame.complement ζr =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.red F.frame.complement)) :
    F.frame.legEquivComplement (fun ie => (pairToEtaY (G := G) F ζr ζc ζb).1 ie.1) =
      regionBoundaryLabel (G := G) A F.frame.complement ζc := by
  show F.frame.legEquivComplement (fun ie => (tripleToEta F ζr ζc) ie.1) =
    regionBoundaryLabel (G := G) A F.frame.complement ζc
  refine legEquivComplement_eq_of_bondModel F hP _ ζc ?_ ?_
  · rw [tripleToEta_rc]; exact hrc
  · rw [tripleToEta_bc]; rfl

/-- The realizing pair reads, through the override, `ζb`'s blue boundary label,
provided the blue and complement configurations agree on the blue-to-complement
crossings. -/
theorem legEquivBlue_override_pairToEtaY (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (ζr ζc ζb : VirtualConfig A)
    (hbc : crossingLabel (G := G) A F.frame.blue F.frame.complement ζb =
      (fun g => ζc g.1 : CrossingConfig (G := G) A F.frame.blue F.frame.complement)) :
    F.frame.legEquivBlue
        (fun ie => overrideEdge (G := coarseGraph) (F.frame.coarseTensor) coarseEdgeRB
          (pairToEtaY (G := G) F ζr ζc ζb).1 (pairToEtaY (G := G) F ζr ζc ζb).2 ie.1) =
      regionBoundaryLabel (G := G) A F.frame.blue ζb := by
  refine legEquivBlue_overrideEdge_eq_of_bondModel F hP _ _ ζb (bondModel_blueRBIndex F ζb) ?_
  show F.bondModel coarseEdgeBC ((tripleToEta F ζr ζc) coarseEdgeBC) =
    crossingLabel (G := G) A F.frame.blue F.frame.complement ζb
  rw [tripleToEta_bc, hbc]; rfl

end PEPS
end TNLean
