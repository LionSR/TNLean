import TNLean.PEPS.FundamentalTheorem.EdgeInsertion
import TNLean.PEPS.TwoInjectiveComparison
import TNLean.PEPS.VertexComplement.KernelDescent

/-!
# One-vertex comparison for the PEPS Fundamental Theorem

This file blocks one vertex against its complement and compares the resulting
two-block insertion with the edge-inserted PEPS coefficient.  It supplies the
coefficient identities used in the one-vertex-versus-complement step of
arXiv:1804.04964, Section 3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### One-vertex two-block wrapping -/

/-- The single-vertex tensor at a vertex \(v\), viewed as an abstract two-block
tensor over the bonds incident to \(v\), with a one-point external boundary and
the physical alphabet.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`: the comparison after Lemma
inj_equal_tensors_2 blocks one vertex against its complement, with the chosen
vertex playing the role of the first block. The shared bonds are the edges
incident to `v`. -/
def vertexTwoBlock (A : Tensor G d) (v : V) :
    TwoBlockTensor (Bond := IncidentEdge G v)
      (fun ie => Fin (A.bondDim ie.1)) PUnit (Fin d) :=
  fun _ η σ => A.component v η σ

omit [Fintype V] in
@[simp] theorem vertexTwoBlock_apply (A : Tensor G d) (v : V)
    (u : PUnit) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d) :
    vertexTwoBlock (G := G) A v u η σ = A.component v η σ := rfl

omit [Fintype V] in
/-- The single-vertex two-block tensor is injective whenever \(A\) is
vertex-injective.

Vertex injectivity is linear independence of the vertex-local coefficient family
of \(A\) at \(v\).  Reindexing the auxiliary one-point boundary together with
the local virtual configuration turns this into the abstract two-block
injectivity of the single-vertex tensor.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_vertexTwoBlock (A : Tensor G d)
    (hA : IsVertexInjective A) (v : V) :
    IsTwoBlockInjective (Bond := IncidentEdge G v)
      (bondDim := fun ie => Fin (A.bondDim ie.1)) (vertexTwoBlock (G := G) A v) := by
  have he : LinearIndependent ℂ
      (fun η : PUnit × ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) =>
        fun σ : Fin d => A.component v η.2 σ) := by
    have hequiv : (fun η : PUnit × ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) =>
          fun σ : Fin d => A.component v η.2 σ) =
        (A.component v) ∘ (Equiv.punitProd _) := by
      funext η; rfl
    rw [hequiv]
    exact (hA v).comp _ (Equiv.punitProd _).injective
  exact he

/-! ### Vertex-complement two-block wrapping -/

/-- The complement region \(V\setminus\{v\}\), viewed as an abstract two-block
tensor over the bonds incident to \(v\), with a one-point external
boundary and the physical leg on $V\setminus\{v\}$.

This is the second block in the one-vertex-versus-complement comparison: the
selected vertex supplies the single-vertex two-block tensor, and this is its
complement. The shared bonds are the \(v\)-star edges read at the complement
endpoints.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def complementTwoBlock (A : Tensor G d) (v : V) :
    TwoBlockTensor (Bond := IncidentEdge G v)
      (fun ie => Fin (A.bondDim ie.1)) PUnit
      (VertexComplementPhysicalConfig (V := V) (d := d) v) :=
  fun _ starCfg τ => vertexComplementWeight (G := G) A v starCfg τ

@[simp] theorem complementTwoBlock_apply (A : Tensor G d) (v : V)
    (u : PUnit) (starCfg : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
    (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) :
    complementTwoBlock (G := G) A v u starCfg τ =
      vertexComplementWeight (G := G) A v starCfg τ := rfl

/-- The vertex-complement two-block tensor is injective whenever \(A\) is
vertex-injective and has positive bond dimensions.

The complement injectivity is a contraction of injective tensors over
\(V\setminus\{v\}\). Reindexing the auxiliary one-point boundary together with
the local virtual configuration turns it into the abstract two-block
injectivity of the complement two-block tensor.

**Positive-bond hypothesis (faithfulness fix).** The complement contraction can
degenerate when an interior virtual space is empty; the hypothesis
\(\forall e,\ 0 < D_A(e)\) is the source's standing assumption that injective PEPS
have nonzero virtual bond spaces, recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 and 205--250 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTwoBlockInjective_complementTwoBlock (A : Tensor G d)
    (hA : IsVertexInjective A) (hpos : ∀ e : Edge G, 0 < A.bondDim e) (v : V) :
    IsTwoBlockInjective (Bond := IncidentEdge G v)
      (bondDim := fun ie => Fin (A.bondDim ie.1)) (complementTwoBlock (G := G) A v) := by
  have hInj : VertexComplementTensorInjective (G := G) A v :=
    vertexComplementTensorInjective_of_isVertexInjective (G := G) A v hA hpos
  have hequiv : (fun η : PUnit × ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) =>
        fun τ : VertexComplementPhysicalConfig (V := V) (d := d) v =>
          complementTwoBlock (G := G) A v η.1 η.2 τ) =
      (vertexComplementTensorFamily (G := G) A v) ∘ (Equiv.punitProd _) := by
    funext η; rfl
  rw [IsTwoBlockInjective, hequiv]
  exact hInj.comp _ (Equiv.punitProd _).injective

/-! ### Two-block coefficient identity

The two-block inserted coefficient of the vertex/complement split equals an
edge-inserted coefficient of the full PEPS. This is the first translation step of
`gaugeConsistency`: it turns the abstract two-injective comparison into a
statement about `edgeInsertedCoeff`, which the post-absorption insertion identity
controls.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`: the comparison after Lemma
inj_equal_tensors_2 inserts a matrix on a v-star bond and reads off the
edge-centred contraction. -/

/-- Glue the physical index at `v` and a complement physical configuration into a
global physical configuration on all vertices. -/
def assembleσ (v : V) (σ₁ : Fin d)
    (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) : V → Fin d :=
  fun w => if h : w = v then σ₁ else τ ⟨w, h⟩

omit [Fintype V] in
@[simp] theorem assembleσ_self (v : V) (σ₁ : Fin d)
    (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) :
    assembleσ (V := V) (d := d) v σ₁ τ v = σ₁ := by
  simp [assembleσ]

omit [Fintype V] in
theorem assembleσ_of_ne (v : V) (σ₁ : Fin d)
    (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) {w : V} (h : w ≠ v) :
    assembleσ (V := V) (d := d) v σ₁ τ w = τ ⟨w, h⟩ := by
  simp [assembleσ, h]

open scoped Classical in
/-- The vertex/complement two-block inserted coefficient, with the abstract
shared-bond sums of `twoBlockInsertedCoeff` rewritten over the local virtual
configuration `Fintype` instance.

`twoBlockInsertedCoeff` sums over `SharedBondConfig` using `Pi.instFintype`;
this lemma transports both sums to `LocalVirtualConfig A v` so the downstream
fiberwise collapse over the global virtual configuration is instance-aligned. -/
theorem twoBlockInsertedCoeff_vertex_complement (A : Tensor G d) (v : V)
    (ie : IncidentEdge G v) (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (σ₁ : Fin d) (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) :
    twoBlockInsertedCoeff (Bond := IncidentEdge G v)
        (bondDim := fun ie => Fin (A.bondDim ie.1))
        (vertexTwoBlock (G := G) A v) (complementTwoBlock (G := G) A v)
        ie M PUnit.unit PUnit.unit σ₁ τ =
      ∑ μ : LocalVirtualConfig A v, ∑ ν : LocalVirtualConfig A v,
        (if SameAwayFromBond ie μ ν then M (μ ie) (ν ie) else 0) *
          A.component v μ σ₁ * vertexComplementWeight (G := G) A v ν τ := by
  rw [twoBlockInsertedCoeff]
  simp only [vertexTwoBlock_apply, complementTwoBlock_apply]
  refine Finset.sum_congr (by ext x; simp) (fun μ _ => ?_)
  refine Finset.sum_congr (by ext x; simp) (fun ν _ => rfl)

open scoped Classical in
/-- The vertex/complement two-block inserted coefficient as a sum over global
virtual configurations.

The complement weight is a fibered sum over global virtual configurations whose
v-star equals the second block boundary; collapsing that fiber identifies the
second block configuration `ν` with `vertexStarLabel ζ` and leaves a sum over
the global configuration `ζ` and the v-star configuration `μ` of the first
block.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem twoBlock_lhs_global (A : Tensor G d) (v : V) (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (σ₁ : Fin d) (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) :
    twoBlockInsertedCoeff (Bond := IncidentEdge G v)
        (bondDim := fun ie => Fin (A.bondDim ie.1))
        (vertexTwoBlock (G := G) A v) (complementTwoBlock (G := G) A v)
        ie M PUnit.unit PUnit.unit σ₁ τ =
      ∑ ζ : VirtualConfig A,
        ∑ μ : LocalVirtualConfig A v,
          (if SameAwayFromBond ie μ (vertexStarLabel (G := G) A v ζ) then
            M (μ ie) (ζ ie.1) else 0) *
            A.component v μ σ₁ *
            ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w) := by
  rw [twoBlockInsertedCoeff_vertex_complement]
  -- Move the second-block boundary `ν` outermost.
  rw [Finset.sum_comm]
  -- Expand the complement weight as a fibered sum over global configurations and
  -- distribute it into each summand.
  simp only [vertexComplementWeight, Finset.mul_sum]
  -- Un-fiber the right-hand global sum over the v-star label.
  conv_rhs =>
    rw [← Finset.sum_fiberwise Finset.univ
      (fun ζ : VirtualConfig A => vertexStarLabel (G := G) A v ζ)
      (fun ζ => ∑ μ : LocalVirtualConfig A v,
        (if SameAwayFromBond ie μ (vertexStarLabel (G := G) A v ζ) then
            M (μ ie) (ζ ie.1) else 0) * A.component v μ σ₁ *
          ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w))]
  -- Both sides now sum over `ν` and the fiber `ζ`; reconcile the summands,
  -- replacing `ν` by `vertexStarLabel ζ` on the fiber.
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ζ hζ => ?_
  rw [Finset.mem_filter] at hζ
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← hζ.2, vertexStarLabel_apply]

omit [Fintype V] in
/-- `SameAwayFromBond ie μ ρ` is equivalent to `μ` being `ρ` with the value on `ie`
overwritten by `μ ie`. -/
theorem sameAwayFromBond_iff_update (A : Tensor G d) (v : V) (ie : IncidentEdge G v)
    (μ ρ : LocalVirtualConfig A v) :
    SameAwayFromBond ie μ ρ ↔ μ = Function.update ρ ie (μ ie) := by
  classical
  constructor
  · intro h
    funext c
    by_cases hc : c = ie
    · subst hc; simp
    · rw [Function.update_of_ne hc]; exact h c hc
  · intro h c hc
    rw [h, Function.update_of_ne hc]

open scoped Classical in
/-- Collapse a sum over local virtual configurations constrained to agree with a
fixed configuration off the distinguished bond `ie` into a sum over the value on
`ie`. -/
theorem constrained_mu_sum_collapse (A : Tensor G d) (v : V) (ie : IncidentEdge G v)
    (ρ : LocalVirtualConfig A v) (F : LocalVirtualConfig A v → ℂ) :
    (∑ μ : LocalVirtualConfig A v, (if SameAwayFromBond ie μ ρ then F μ else 0)) =
      ∑ j : Fin (A.bondDim ie.1), F (Function.update ρ ie j) := by
  classical
  rw [← Finset.sum_filter]
  let φ : {μ : LocalVirtualConfig A v // SameAwayFromBond ie μ ρ} ≃
      Fin (A.bondDim ie.1) := {
    toFun := fun μ => μ.1 ie
    invFun := fun j =>
      ⟨Function.update ρ ie j, fun c hc => Function.update_of_ne hc _ _⟩
    left_inv := fun μ => by
      apply Subtype.ext
      exact ((sameAwayFromBond_iff_update A v ie μ.1 ρ).mp μ.2).symm
    right_inv := fun j => by
      simp }
  rw [← Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (f := F)
    (p := fun μ => SameAwayFromBond ie μ ρ)]
  simpa using Fintype.sum_equiv φ
    (fun μ : {μ : LocalVirtualConfig A v // SameAwayFromBond ie μ ρ} => F μ.1)
    (fun j : Fin (A.bondDim ie.1) => F (Function.update ρ ie j)) (by
      intro μ
      change F μ.1 = F (Function.update ρ ie (μ.1 ie))
      exact congrArg F ((sameAwayFromBond_iff_update A v ie μ.1 ρ).mp μ.2))

/-- Split a global virtual configuration into the value on a chosen edge and the
configuration on all remaining edges. -/
noncomputable def virtualConfigSplitAt (A : Tensor G d) (e : Edge G) :
    VirtualConfig A ≃ Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e :=
  Equiv.piSplitAt e (fun f : Edge G => Fin (A.bondDim f))

omit [Fintype V] in
@[simp] theorem virtualConfigSplitAt_symm_edge (A : Tensor G d) (e : Edge G)
    (x : Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e) :
    (virtualConfigSplitAt (G := G) A e).symm x e = x.1 := by
  simp [virtualConfigSplitAt, Equiv.piSplitAt_symm_apply]

omit [Fintype V] in
@[simp] theorem virtualConfigSplitAt_symm_ne (A : Tensor G d) (e : Edge G)
    (x : Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e)
    (f : {f : Edge G // f ≠ e}) :
    (virtualConfigSplitAt (G := G) A e).symm x f.1 = x.2 f := by
  simp [virtualConfigSplitAt, Equiv.piSplitAt_symm_apply, f.2]


/-! ### Edge-inserted coefficient and the two-block identity

The two-block inserted coefficient of the vertex/complement split equals an
edge-inserted coefficient of the full PEPS, transposed at the right endpoint.
This is the coefficient identity feeding `SameTwoBlockInsertions` in
`gaugeConsistency`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/

open scoped Classical in
/-- The edge-inserted coefficient as a sum over the two open edge indices and a
complement configuration, with the per-vertex tensors contracted along the
edge-doubled configuration. -/
theorem edgeInsertedCoeff_eq_doubled (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := G) A e σ N =
      ∑ x : Fin (A.bondDim e) × Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e,
          N x.1 x.2.1 *
            ∏ v : V, A.component v (localOfDoubled (G := G) A e x.1 x.2.1 x.2.2 v) (σ v) := by
  classical
  rw [edgeInsertedCoeff_eq_sum_local]
  -- Collapse the deltas to the consistency-off-e filter, restrict, then reindex the
  -- consistent configurations to the doubled data.
  set F : OpenLocalConfig (G := G) A → ℂ := fun ξ =>
    N (ξ e.1.1 (edgeLeftIncident (G := G) e)) (ξ e.1.2 (edgeRightIncident (G := G) e)) *
      ∏ v : V, A.component v (ξ v) (σ v) with hF
  have hcollapse :
      (∑ ξ : OpenLocalConfig (G := G) A,
        (∏ f : {f : Edge G // f ≠ e},
          if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
              ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
          N (ξ e.1.1 (edgeLeftIncident (G := G) e))
            (ξ e.1.2 (edgeRightIncident (G := G) e)) *
          ∏ v : V, A.component v (ξ v) (σ v)) =
        ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ}, F ξ.1 := by
    calc
      (∑ ξ : OpenLocalConfig (G := G) A,
        (∏ f : {f : Edge G // f ≠ e},
          if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
              ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
          N (ξ e.1.1 (edgeLeftIncident (G := G) e))
            (ξ e.1.2 (edgeRightIncident (G := G) e)) *
          ∏ v : V, A.component v (ξ v) (σ v))
          = ∑ ξ : OpenLocalConfig (G := G) A,
              if IsConsistentOff (G := G) A e ξ then F ξ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ξ _
            rw [prod_off_delta_eq]
            by_cases h : IsConsistentOff (G := G) A e ξ <;> simp [h, hF]
      _ = ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ},
            F ξ.1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
            rw [← Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (OpenLocalConfig (G := G) A)))
              (f := F) (p := IsConsistentOff (G := G) A e)]
            simp
  rw [hcollapse]
  refine Fintype.sum_equiv (consistentOffEquivDoubled (G := G) A e) (fun ξ => F ξ.1) _ ?_
  rintro ⟨ξ, hξ⟩
  set p := consistentOffEquivDoubled (G := G) A e ⟨ξ, hξ⟩ with hp
  obtain ⟨i, k, ζ⟩ := p
  have hξeq : ξ = localOfDoubled (G := G) A e i k ζ := by
    have := (consistentOffEquivDoubled (G := G) A e).symm_apply_apply ⟨ξ, hξ⟩
    rw [← hp] at this
    exact congrArg Subtype.val this.symm
  subst hξeq
  simp only [hF]
  rw [localOfDoubled_left_e, localOfDoubled_right_e]

omit [Fintype V] in
/-- At a non-`v` vertex (`v = e.1.1` the left endpoint), the edge-doubled local
configuration reads the global configuration `ζ = (k, ζc)` directly. -/
theorem localOfDoubled_eq_global_off_left (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζc : EdgeComplementConfig (G := G) A e)
    {w : V} (hw : w ≠ e.1.1) (je : IncidentEdge G w) :
    localOfDoubled (G := G) A e i k ζc w je =
      (virtualConfigSplitAt (G := G) A e).symm (k, ζc) je.1 := by
  classical
  by_cases hje : je.1 = e
  · -- je is the edge `e`; since `w ≠ e.1.1`, `w = e.1.2`, so `je` is the right
    -- incidence and the doubled value is `k`.
    have hwv : w = e.1.2 := by
      rcases je.2 with hl | hr
      · exact absurd (hl.symm.trans (congrArg (fun f : Edge G => f.1.1) hje)) hw
      · exact (hr.symm.trans (congrArg (fun f : Edge G => f.1.2) hje))
    subst hwv
    have hje' : je = edgeRightIncident (G := G) e := Subtype.ext hje
    subst hje'
    rw [localOfDoubled_right_e]
    simp only [edgeRightIncident_edge, virtualConfigSplitAt_symm_edge]
  · -- je is some other edge `g ≠ e`; both sides read the complement configuration.
    rw [virtualConfigSplitAt_symm_ne A e (k, ζc) ⟨je.1, hje⟩]
    unfold localOfDoubled
    rw [dif_neg hje]

omit [Fintype V] in
/-- At the left endpoint `v = e.1.1`, the edge-doubled local configuration is the
v-star configuration of `ζ = (k, ζc)` with the value on the distinguished edge
overwritten by the left open index `i`. -/
theorem localOfDoubled_eq_update_at_left (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζc : EdgeComplementConfig (G := G) A e) :
    localOfDoubled (G := G) A e i k ζc e.1.1 =
      Function.update
        (vertexStarLabel (G := G) A e.1.1 ((virtualConfigSplitAt (G := G) A e).symm (k, ζc)))
        (edgeLeftIncident (G := G) e) i := by
  classical
  funext je
  by_cases hje : je = edgeLeftIncident (G := G) e
  · subst hje
    rw [Function.update_self, localOfDoubled_left_e]
  · rw [Function.update_of_ne hje]
    have hjne : je.1 ≠ e := fun h => hje (Subtype.ext h)
    rw [vertexStarLabel_apply, virtualConfigSplitAt_symm_ne A e (k, ζc) ⟨je.1, hjne⟩]
    unfold localOfDoubled
    rw [dif_neg hjne]

open scoped Classical in
/-- The vertex/complement two-block inserted coefficient as a sum over global
virtual configurations and the open value `j` on the distinguished bond. -/
theorem twoBlock_lhs_collapsed (A : Tensor G d) (v : V) (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (σ₁ : Fin d) (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) :
    twoBlockInsertedCoeff (Bond := IncidentEdge G v)
        (bondDim := fun ie => Fin (A.bondDim ie.1))
        (vertexTwoBlock (G := G) A v) (complementTwoBlock (G := G) A v)
        ie M PUnit.unit PUnit.unit σ₁ τ =
      ∑ ζ : VirtualConfig A, ∑ j : Fin (A.bondDim ie.1),
        M j (ζ ie.1) *
          A.component v (Function.update (vertexStarLabel (G := G) A v ζ) ie j) σ₁ *
          ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w) := by
  rw [twoBlock_lhs_global]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  -- Pull the `if` over the whole summand, then collapse the constrained `μ`-sum.
  rw [show (∑ μ : LocalVirtualConfig A v,
        (if SameAwayFromBond ie μ (vertexStarLabel (G := G) A v ζ) then
            M (μ ie) (ζ ie.1) else 0) * A.component v μ σ₁ *
          ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w)) =
      ∑ μ : LocalVirtualConfig A v,
        if SameAwayFromBond ie μ (vertexStarLabel (G := G) A v ζ) then
          (M (μ ie) (ζ ie.1) * A.component v μ σ₁ *
            ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w))
        else 0 from by
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases h : SameAwayFromBond ie μ (vertexStarLabel (G := G) A v ζ) <;> simp [h]]
  rw [constrained_mu_sum_collapse A v ie (vertexStarLabel (G := G) A v ζ)
    (fun μ => M (μ ie) (ζ ie.1) * A.component v μ σ₁ *
      ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Function.update_self]

/-- Product over all vertices, split off the chosen vertex. -/
theorem prod_split_off_vertex {M : Type*} [CommMonoid M] (v₀ : V) (f : V → M) :
    ∏ v : V, f v = f v₀ * ∏ w : {w : V // w ≠ v₀}, f w.1 := by
  classical
  rw [← Finset.prod_subtype (Finset.univ.erase v₀)
    (by intro x; simp [Finset.mem_erase]) f]
  rw [Finset.mul_prod_erase Finset.univ f (Finset.mem_univ v₀)]

open scoped Classical in
/-- The edge-inserted coefficient on the left-incidence-oriented edge equals the
vertex/complement two-block inserted coefficient at the left endpoint.

Here `v = e.1.1` is the left endpoint, the distinguished v-star bond is
`edgeLeftIncident e`, and no transpose appears. -/
theorem edgeInsertedCoeff_eq_twoBlock_left (A : Tensor G d) (e : Edge G)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (σ₁ : Fin d) (τ : VertexComplementPhysicalConfig (V := V) (d := d) e.1.1) :
    edgeInsertedCoeff (G := G) A e (assembleσ (V := V) (d := d) e.1.1 σ₁ τ) M =
      twoBlockInsertedCoeff (Bond := IncidentEdge G e.1.1)
        (bondDim := fun ie => Fin (A.bondDim ie.1))
        (vertexTwoBlock (G := G) A e.1.1) (complementTwoBlock (G := G) A e.1.1)
        (edgeLeftIncident (G := G) e) M PUnit.unit PUnit.unit σ₁ τ := by
  classical
  rw [twoBlock_lhs_collapsed, edgeInsertedCoeff_eq_doubled]
  simp only [edgeLeftIncident_edge]
  -- Convert the RHS double sum into a single product-type sum over `VirtualConfig × Fin`.
  conv_rhs => rw [← Fintype.sum_prod_type']
  -- Reindex the doubled `(i,k,ζc)` sum onto `(ζ, j)` by `(i,k,ζc) ↦ ((split).symm (k,ζc), i)`.
  refine Fintype.sum_equiv
    (Equiv.trans (Equiv.prodComm _ _)
      ((virtualConfigSplitAt (G := G) A e).symm.prodCongr (Equiv.refl (Fin (A.bondDim e))))) _ _
    (fun x => ?_)
  obtain ⟨i, k, ζc⟩ := x
  -- the image is `((split).symm (k, ζc), i)`
  set ζ := (virtualConfigSplitAt (G := G) A e).symm (k, ζc) with hζ
  have hζe : ζ e = k := by rw [hζ]; exact virtualConfigSplitAt_symm_edge A e (k, ζc)
  change M i k * ∏ v : V, A.component v (localOfDoubled (G := G) A e i k ζc v)
        (assembleσ (V := V) (d := d) e.1.1 σ₁ τ v) =
      M i (ζ e) *
        A.component e.1.1 (Function.update (vertexStarLabel (G := G) A e.1.1 ζ)
          (edgeLeftIncident (G := G) e) i) σ₁ *
        ∏ w : {w : V // w ≠ e.1.1}, A.component w.1 (fun ie => ζ ie.1) (τ w)
  -- Split the doubled product over all vertices off the left endpoint.
  rw [prod_split_off_vertex e.1.1
    (fun v => A.component v (localOfDoubled (G := G) A e i k ζc v)
      (assembleσ (V := V) (d := d) e.1.1 σ₁ τ v))]
  -- Identify the left-endpoint factor and the complement factors.
  rw [show localOfDoubled (G := G) A e i k ζc e.1.1 =
        Function.update (vertexStarLabel (G := G) A e.1.1 ζ)
          (edgeLeftIncident (G := G) e) i from
    localOfDoubled_eq_update_at_left A e i k ζc]
  rw [assembleσ_self, hζe]
  -- The complement factors agree pointwise with `fun ie => ζ ie.1` and `τ`.
  have hprod :
      (∏ w : {w : V // w ≠ e.1.1},
        A.component w.1 (localOfDoubled (G := G) A e i k ζc w.1)
          (assembleσ (V := V) (d := d) e.1.1 σ₁ τ w.1)) =
      ∏ w : {w : V // w ≠ e.1.1}, A.component w.1 (fun ie => ζ ie.1) (τ w) := by
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [assembleσ_of_ne e.1.1 σ₁ τ w.2]
    congr 1
    funext je
    exact localOfDoubled_eq_global_off_left A e i k ζc w.2 je
  rw [hprod]
  ring

omit [Fintype V] in
/-- At a non-`v` vertex (`v = e.1.2` the right endpoint), the edge-doubled local
configuration reads the global configuration `ζ = (i, ζc)` directly. -/
theorem localOfDoubled_eq_global_off_right (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζc : EdgeComplementConfig (G := G) A e)
    {w : V} (hw : w ≠ e.1.2) (je : IncidentEdge G w) :
    localOfDoubled (G := G) A e i k ζc w je =
      (virtualConfigSplitAt (G := G) A e).symm (i, ζc) je.1 := by
  classical
  by_cases hje : je.1 = e
  · have hwv : w = e.1.1 := by
      rcases je.2 with hl | hr
      · exact (hl.symm.trans (congrArg (fun f : Edge G => f.1.1) hje))
      · exact absurd (hr.symm.trans (congrArg (fun f : Edge G => f.1.2) hje)) hw
    subst hwv
    have hje' : je = edgeLeftIncident (G := G) e := Subtype.ext hje
    subst hje'
    rw [localOfDoubled_left_e]
    simp only [edgeLeftIncident_edge, virtualConfigSplitAt_symm_edge]
  · rw [virtualConfigSplitAt_symm_ne A e (i, ζc) ⟨je.1, hje⟩]
    unfold localOfDoubled
    rw [dif_neg hje]

omit [Fintype V] in
/-- At the right endpoint `v = e.1.2`, the edge-doubled local configuration is the
v-star configuration of `ζ = (i, ζc)` with the value on the distinguished edge
overwritten by the right open index `k`. -/
theorem localOfDoubled_eq_update_at_right (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζc : EdgeComplementConfig (G := G) A e) :
    localOfDoubled (G := G) A e i k ζc e.1.2 =
      Function.update
        (vertexStarLabel (G := G) A e.1.2 ((virtualConfigSplitAt (G := G) A e).symm (i, ζc)))
        (edgeRightIncident (G := G) e) k := by
  classical
  funext je
  by_cases hje : je = edgeRightIncident (G := G) e
  · subst hje
    rw [Function.update_self, localOfDoubled_right_e]
  · rw [Function.update_of_ne hje]
    have hjne : je.1 ≠ e := fun h => hje (Subtype.ext h)
    rw [vertexStarLabel_apply, virtualConfigSplitAt_symm_ne A e (i, ζc) ⟨je.1, hjne⟩]
    unfold localOfDoubled
    rw [dif_neg hjne]

open scoped Classical in
/-- The edge-inserted coefficient on the right-incidence-oriented edge equals the
vertex/complement two-block inserted coefficient at the right endpoint.

Here `v = e.1.2` is the right endpoint, the distinguished v-star bond is
`edgeRightIncident e`, and the inserted matrix appears transposed. -/
theorem edgeInsertedCoeff_eq_twoBlock_right (A : Tensor G d) (e : Edge G)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (σ₁ : Fin d) (τ : VertexComplementPhysicalConfig (V := V) (d := d) e.1.2) :
    edgeInsertedCoeff (G := G) A e (assembleσ (V := V) (d := d) e.1.2 σ₁ τ) Mᵀ =
      twoBlockInsertedCoeff (Bond := IncidentEdge G e.1.2)
        (bondDim := fun ie => Fin (A.bondDim ie.1))
        (vertexTwoBlock (G := G) A e.1.2) (complementTwoBlock (G := G) A e.1.2)
        (edgeRightIncident (G := G) e) M PUnit.unit PUnit.unit σ₁ τ := by
  classical
  rw [twoBlock_lhs_collapsed, edgeInsertedCoeff_eq_doubled]
  simp only [edgeRightIncident_edge]
  conv_rhs => rw [← Fintype.sum_prod_type']
  -- Reindex `(i,k,ζc) ↦ ((split).symm (i,ζc), k)`.
  refine Fintype.sum_equiv
    (Equiv.trans ((Equiv.refl (Fin (A.bondDim e))).prodCongr (Equiv.prodComm _ _))
      (Equiv.trans (Equiv.prodAssoc _ _ _).symm
        ((virtualConfigSplitAt (G := G) A e).symm.prodCongr (Equiv.refl (Fin (A.bondDim e)))))) _ _
    (fun x => ?_)
  obtain ⟨i, k, ζc⟩ := x
  set ζ := (virtualConfigSplitAt (G := G) A e).symm (i, ζc) with hζ
  have hζe : ζ e = i := by rw [hζ]; exact virtualConfigSplitAt_symm_edge A e (i, ζc)
  change (Mᵀ) i k * ∏ v : V, A.component v (localOfDoubled (G := G) A e i k ζc v)
        (assembleσ (V := V) (d := d) e.1.2 σ₁ τ v) =
      M k (ζ e) *
        A.component e.1.2 (Function.update (vertexStarLabel (G := G) A e.1.2 ζ)
          (edgeRightIncident (G := G) e) k) σ₁ *
        ∏ w : {w : V // w ≠ e.1.2}, A.component w.1 (fun ie => ζ ie.1) (τ w)
  rw [prod_split_off_vertex e.1.2
    (fun v => A.component v (localOfDoubled (G := G) A e i k ζc v)
      (assembleσ (V := V) (d := d) e.1.2 σ₁ τ v))]
  rw [show localOfDoubled (G := G) A e i k ζc e.1.2 =
        Function.update (vertexStarLabel (G := G) A e.1.2 ζ)
          (edgeRightIncident (G := G) e) k from
    localOfDoubled_eq_update_at_right A e i k ζc]
  rw [assembleσ_self, hζe, Matrix.transpose_apply]
  have hprod :
      (∏ w : {w : V // w ≠ e.1.2},
        A.component w.1 (localOfDoubled (G := G) A e i k ζc w.1)
          (assembleσ (V := V) (d := d) e.1.2 σ₁ τ w.1)) =
      ∏ w : {w : V // w ≠ e.1.2}, A.component w.1 (fun ie => ζ ie.1) (τ w) := by
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [assembleσ_of_ne e.1.2 σ₁ τ w.2]
    congr 1
    funext je
    exact localOfDoubled_eq_global_off_right A e i k ζc w.2 je
  rw [hprod]
  ring

/-! ### Two-block coefficient identity (unified) -/

/-- The oriented inserted matrix: `M` at the left endpoint of the incident edge,
`Mᵀ` at the right endpoint.  This is the matrix inserted on the full PEPS edge
that realizes a v-star insertion of `M` at the vertex `v`. -/
noncomputable def orientedInsert (A : Tensor G d) (v : V) (ie : IncidentEdge G v)
    (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :
    Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ :=
  if ie.1.1.1 = v then M else Mᵀ

open scoped Classical in
/-- **Two-block coefficient identity.** The vertex/complement two-block inserted
coefficient at any incident edge equals the edge-inserted coefficient of the full
PEPS, transposed at the right endpoint.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem twoBlockInsertedCoeff_eq_edgeInsertedCoeff (A : Tensor G d) (v : V)
    (ie : IncidentEdge G v) (M : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (σ₁ : Fin d) (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) :
    twoBlockInsertedCoeff (Bond := IncidentEdge G v)
        (bondDim := fun ie => Fin (A.bondDim ie.1))
        (vertexTwoBlock (G := G) A v) (complementTwoBlock (G := G) A v)
        ie M PUnit.unit PUnit.unit σ₁ τ =
      edgeInsertedCoeff (G := G) A ie.1 (assembleσ (V := V) (d := d) v σ₁ τ)
        (orientedInsert A v ie M) := by
  classical
  obtain ⟨e, hor⟩ := ie
  rcases hor with h | h
  · -- left endpoint: `e.1.1 = v`
    subst h
    rw [orientedInsert]
    rw [if_pos (by rfl : (⟨e, Or.inl rfl⟩ : IncidentEdge G e.1.1).1.1.1 = e.1.1)]
    exact (edgeInsertedCoeff_eq_twoBlock_left A e M σ₁ τ).symm
  · -- right endpoint: `e.1.2 = v`
    subst h
    rw [orientedInsert]
    rw [if_neg (by exact ne_of_lt e.2.1 :
      ¬ (⟨e, Or.inr rfl⟩ : IncidentEdge G e.1.2).1.1.1 = e.1.2)]
    exact (edgeInsertedCoeff_eq_twoBlock_right A e M σ₁ τ).symm


/-! ### Bond-dimension reindex and same two-block insertions -/

/-- Reindex a PEPS tensor along a bond-dimension equality, producing a tensor
whose bond dimensions are the left side of the equality. -/
noncomputable def reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) : Tensor G d where
  bondDim := bd
  component v η σ := B.component v (fun ie => Fin.cast (congr_fun h ie.1) (η ie)) σ

omit [Fintype V] in
@[simp] theorem reindexTensor_bondDim (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) : (reindexTensor (G := G) B h).bondDim = bd := rfl

omit [Fintype V] in
@[simp] theorem reindexTensor_component (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (v : V)
    (η : (ie : IncidentEdge G v) → Fin (bd ie.1)) (σ : Fin d) :
    (reindexTensor (G := G) B h).component v η σ =
      B.component v (fun ie => Fin.cast (congr_fun h ie.1) (η ie)) σ := rfl

omit [Fintype V] in
/-- The edge-doubled configuration of a reindexed tensor, cast to the original
bond dimensions, is the edge-doubled configuration of the original tensor with the
indices cast. -/
theorem localOfDoubled_reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (e : Edge G)
    (i k : Fin (bd e)) (ζc : EdgeComplementConfig (G := G) (reindexTensor (G := G) B h) e)
    (v : V) (ie : IncidentEdge G v) :
    Fin.cast (congr_fun h ie.1)
        (localOfDoubled (G := G) (reindexTensor (G := G) B h) e i k ζc v ie) =
      localOfDoubled (G := G) B e (Fin.cast (congr_fun h e) i) (Fin.cast (congr_fun h e) k)
        (fun f => Fin.cast (congr_fun h f.1) (ζc f)) v ie := by
  unfold localOfDoubled
  by_cases hie : ie.1 = e
  · rw [dif_pos hie, dif_pos hie]
    by_cases hv : v = e.1.1 <;> simp [hv]
  · rw [dif_neg hie, dif_neg hie]

open scoped Classical in
/-- `edgeInsertedCoeff` transports along a bond-dimension reindex by conjugating
the inserted matrix with the corresponding reindexing algebra equivalence. -/
theorem edgeInsertedCoeff_reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (e : Edge G) (σ : V → Fin d)
    (N : Matrix (Fin (bd e)) (Fin (bd e)) ℂ) :
    edgeInsertedCoeff (G := G) (reindexTensor (G := G) B h) e σ N =
      edgeInsertedCoeff (G := G) B e σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun h e)) N) := by
  classical
  rw [edgeInsertedCoeff_eq_doubled, edgeInsertedCoeff_eq_doubled]
  -- Reindex the doubled `(i,k,ζc)` sum by `finCongr` on every bond.
  refine Fintype.sum_equiv
    ((finCongr (congr_fun h e)).prodCongr
      ((finCongr (congr_fun h e)).prodCongr
        (Equiv.piCongr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
          (fun f => finCongr (congr_fun h f.1))))) _ _ (fun x => ?_)
  obtain ⟨i, k, ζc⟩ := x
  -- Match the summands.
  simp only [Equiv.prodCongr_apply, finCongr_apply, Prod.map]
  -- The matrix entry: `(reindexAlgEquiv (finCongr) N) (cast i) (cast k) = N i k`.
  have hN : (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun h e)) N)
      (Fin.cast (congr_fun h e) i) (Fin.cast (congr_fun h e) k) = N i k := by
    rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp
  rw [hN]
  -- The product factor reindexes the doubled configuration through the cast.
  refine congrArg (N i k * ·) ?_
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [reindexTensor_component]
  congr 1
  funext ie
  rw [localOfDoubled_reindexTensor B h e i k ζc v ie]
  simp only [Equiv.piCongr, Equiv.subtypeEquivRight, Equiv.coe_trans, Function.comp]
  rfl

open scoped Classical in
/-- **Same two-block insertions from an edge-insertion equality.** If two PEPS
tensors share their bond dimensions and have equal edge-inserted coefficients
(after the appropriate oriented matrix), then the vertex/complement two-block
insertions of the two tensors coincide.

This is the abstract reduction from equality of all edge-inserted PEPS
coefficients to equality of all one-bond insertions for the two-block
decomposition of one vertex against its complement, after transporting the
second tensor to the first tensor's bond family. -/
theorem sameTwoBlockInsertions_of_edgeInsertedCoeff_eq (A B : Tensor G d) (v : V)
    (hbd : A.bondDim = B.bondDim)
    (hedge : ∀ (ie : IncidentEdge G v)
      (N : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) (σ : V → Fin d),
      edgeInsertedCoeff (G := G) A ie.1 σ N =
        edgeInsertedCoeff (G := G) B ie.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd ie.1)) N)) :
    SameTwoBlockInsertions (Bond := IncidentEdge G v)
      (bondDim := fun ie => Fin (A.bondDim ie.1))
      (vertexTwoBlock (G := G) A v)
      (vertexTwoBlock (G := G) (reindexTensor (G := G) B hbd) v)
      (complementTwoBlock (G := G) A v)
      (complementTwoBlock (G := G) (reindexTensor (G := G) B hbd) v) := by
  rintro ie M ⟨⟩ ⟨⟩ σ₁ τ
  -- LHS as an edge-inserted coefficient of `A`.
  rw [twoBlockInsertedCoeff_eq_edgeInsertedCoeff A v ie M σ₁ τ]
  -- RHS chain: two-block of the reindexed tensor → its edge-inserted coefficient →
  -- the edge-inserted coefficient of `B` after reindexing.
  refine Eq.trans (hedge ie (orientedInsert A v ie M) (assembleσ (V := V) (d := d) v σ₁ τ)) ?_
  refine Eq.trans
    (edgeInsertedCoeff_reindexTensor B hbd ie.1 (assembleσ (V := V) (d := d) v σ₁ τ)
      (orientedInsert A v ie M)).symm ?_
  -- `orientedInsert` of the reindexed tensor agrees with that of `A`.
  have hoI : orientedInsert A v ie M = orientedInsert (reindexTensor (G := G) B hbd) v ie M := rfl
  rw [hoI]
  exact (twoBlockInsertedCoeff_eq_edgeInsertedCoeff (reindexTensor (G := G) B hbd) v ie M σ₁ τ).symm

end PEPS
end TNLean
