import TNLean.PEPS.FundamentalTheorem

/-!
# Uniqueness modulo balanced edge scalars

The uniqueness clause of the injective PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, Theorem 2): two gauge families relating the same
injective PEPS tensor to the same target differ by a vertex-balanced edge-scalar
family. Split out of `TNLean.PEPS.FundamentalTheorem` to keep file lengths
bounded; the existence clause and the gauge-action infrastructure live there.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Balanced edge scalars -/

/-- The scalar contributed by an edge-scalar family at a chosen endpoint.

For an edge `(u, w)` with `u < w` and scalar `c_e`, the lower endpoint carries
`c_e` and the upper endpoint carries `c_e⁻¹`, mirroring `edgeGaugeAt`. -/
def edgeScalarAt (c : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) : ℂ :=
  if ie.1.1.1 = v then (c ie.1 : ℂ) else ↑((c ie.1)⁻¹)

/-- A scalar edge family is vertex-balanced if the oriented product of its
endpoint scalars is `1` at every vertex. -/
def IsVertexBalanced (c : (e : Edge G) → Units ℂ) : Prop :=
  ∀ v : V, ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie = 1

omit [Fintype V] [DecidableRel G.Adj] in
/-- Endpoint scalars multiply pointwise under multiplication of edge scalars.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; endpoint factors are
defined by the oriented edge scalar and its inverse. -/
theorem edgeScalarAt_mul (c d : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeScalarAt (G := G) (fun e => c e * d e) v ie =
      edgeScalarAt (G := G) c v ie * edgeScalarAt (G := G) d v ie := by
  by_cases h : ie.1.1.1 = v
  · simp [edgeScalarAt, h]
  · simpa [edgeScalarAt, h] using
      (mul_comm (((d ie.1 : Units ℂ) : ℂ)⁻¹) (((c ie.1 : Units ℂ) : ℂ)⁻¹))

omit [Fintype V] [DecidableRel G.Adj] in
/-- Endpoint scalars invert pointwise under inversion of edge scalars.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
uses nonzero edge scalars and the inverse endpoint action on the opposite end
of each oriented edge. -/
theorem edgeScalarAt_inv (c : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeScalarAt (G := G) (fun e => (c e)⁻¹) v ie =
      (edgeScalarAt (G := G) c v ie)⁻¹ := by
  by_cases h : ie.1.1.1 = v
  · simp [edgeScalarAt, h]
  · simp [edgeScalarAt, h]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Endpoint scalar factors are nonzero.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; edge scalars are
nonzero and the opposite endpoint uses their inverse. -/
theorem edgeScalarAt_ne_zero (c : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeScalarAt (G := G) c v ie ≠ 0 := by
  by_cases h : ie.1.1.1 = v
  · simp [edgeScalarAt, h]
  · simp [edgeScalarAt, h]

/-- Vertex-balanced edge scalars are closed under pointwise multiplication.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
uses the multiplicative group of edge scalars whose oriented product is `1` at
each vertex. -/
theorem IsVertexBalanced.mul {c d : (e : Edge G) → Units ℂ}
    (hc : IsVertexBalanced (G := G) c)
    (hd : IsVertexBalanced (G := G) d) :
    IsVertexBalanced (G := G) (fun e => c e * d e) := by
  intro v
  calc
    ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) (fun e => c e * d e) v ie =
        ∏ ie : IncidentEdge G v,
          edgeScalarAt (G := G) c v ie * edgeScalarAt (G := G) d v ie := by
          refine Finset.prod_congr rfl ?_
          intro ie _
          simp [edgeScalarAt_mul]
    _ =
        (∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie) *
          ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) d v ie := by
          rw [Finset.prod_mul_distrib]
    _ = 1 := by simp [hc v, hd v]

/-- Vertex-balanced edge scalars are closed under pointwise inversion.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
uses invertible edge scalars, and the inverse family again has oriented product
`1` at every vertex. -/
theorem IsVertexBalanced.inv {c : (e : Edge G) → Units ℂ}
    (hc : IsVertexBalanced (G := G) c) :
    IsVertexBalanced (G := G) (fun e => (c e)⁻¹) := by
  intro v
  calc
    ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) (fun e => (c e)⁻¹) v ie =
        ∏ ie : IncidentEdge G v, (edgeScalarAt (G := G) c v ie)⁻¹ := by
          refine Finset.prod_congr rfl ?_
          intro ie _
          simp [edgeScalarAt_inv]
    _ = (∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie)⁻¹ := by
          rw [Finset.prod_inv_distrib]
    _ = 1 := by simp [hc v]

/-- Two PEPS gauge families are equivalent modulo balanced edge scalars if,
after inserting the corresponding endpoint scalars, they induce the same
oriented edge action on every incident half-edge. -/
def GaugeEquivModEdgeScalars (A : Tensor G d)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) : Prop :=
  ∃ c : (e : Edge G) → Units ℂ,
    IsVertexBalanced (G := G) c ∧
      ∀ (v : V) (ie : IncidentEdge G v),
        edgeGaugeAt A X v ie =
          edgeScalarAt (G := G) c v ie • edgeGaugeAt A Y v ie

/-- Gauge equivalence modulo balanced edge scalars is reflexive.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the identity edge-scalar
family is vertex-balanced and leaves every oriented endpoint action unchanged. -/
theorem GaugeEquivModEdgeScalars.refl (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) :
    GaugeEquivModEdgeScalars (G := G) A X X := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro v
    simp [edgeScalarAt]
  · intro v ie
    simp [edgeScalarAt]

/-- Gauge equivalence modulo balanced edge scalars is symmetric.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; reversing a balanced
edge-scalar reweighting uses the inverse edge-scalar family. -/
theorem GaugeEquivModEdgeScalars.symm {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y) :
    GaugeEquivModEdgeScalars (G := G) A Y X := by
  rcases hXY with ⟨c, hc, hXY⟩
  refine ⟨fun e => (c e)⁻¹, IsVertexBalanced.inv (G := G) hc, ?_⟩
  intro v ie
  set s : ℂ := edgeScalarAt (G := G) c v ie with hs_def
  have hs : s ≠ 0 := by
    rw [hs_def]
    exact edgeScalarAt_ne_zero (G := G) c v ie
  calc
    edgeGaugeAt A Y v ie = s⁻¹ • (s • edgeGaugeAt A Y v ie) := by
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    _ = s⁻¹ • edgeGaugeAt A X v ie := by
      rw [← hXY v ie]
    _ =
        edgeScalarAt (G := G) (fun e => (c e)⁻¹) v ie •
          edgeGaugeAt A X v ie := by
          rw [edgeScalarAt_inv, ← hs_def]

/-- Gauge equivalence modulo balanced edge scalars is transitive.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; composing two balanced
edge-scalar reweightings multiplies their edge scalars, and the balancing
condition is multiplicatively closed at every vertex. -/
theorem GaugeEquivModEdgeScalars.trans {A : Tensor G d}
    {X Y Z : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y)
    (hYZ : GaugeEquivModEdgeScalars (G := G) A Y Z) :
    GaugeEquivModEdgeScalars (G := G) A X Z := by
  rcases hXY with ⟨c, hc, hXY⟩
  rcases hYZ with ⟨d, hd, hYZ⟩
  refine ⟨fun e => c e * d e, IsVertexBalanced.mul (G := G) hc hd, ?_⟩
  intro v ie
  calc
    edgeGaugeAt A X v ie =
        edgeScalarAt (G := G) c v ie • edgeGaugeAt A Y v ie := hXY v ie
    _ =
        edgeScalarAt (G := G) c v ie •
          (edgeScalarAt (G := G) d v ie • edgeGaugeAt A Z v ie) := by
          rw [hYZ v ie]
    _ =
        (edgeScalarAt (G := G) c v ie * edgeScalarAt (G := G) d v ie) •
          edgeGaugeAt A Z v ie := by
          rw [smul_smul]
    _ =
        edgeScalarAt (G := G) (fun e => c e * d e) v ie •
          edgeGaugeAt A Z v ie := by
          rw [edgeScalarAt_mul]

/-- Gauge equivalence modulo balanced edge scalars is an equivalence relation.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
is the quotient of edge gauges by the vertex-balanced scalar action. -/
theorem GaugeEquivModEdgeScalars.equivalence (A : Tensor G d) :
    Equivalence (GaugeEquivModEdgeScalars (G := G) A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact GaugeEquivModEdgeScalars.refl (G := G) A X
  · intro X Y hXY
    exact GaugeEquivModEdgeScalars.symm (G := G) hXY
  · intro X Y Z hXY hYZ
    exact GaugeEquivModEdgeScalars.trans (G := G) hXY hYZ

/-- The quotient relation on gauge families modulo balanced edge scalars.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; this packages the
corrected balanced edge-scalar quotient as a formal equivalence relation. -/
def GaugeEquivModEdgeScalars.setoid (A : Tensor G d) :
    Setoid ((e : Edge G) → GL (Fin (A.bondDim e)) ℂ) where
  r := GaugeEquivModEdgeScalars (G := G) A
  iseqv := GaugeEquivModEdgeScalars.equivalence (G := G) A

/-- Balanced edge-scalar reweightings do not change the gauged tensor at a
vertex. -/
theorem GaugeEquivModEdgeScalars.gaugeVertex_eq
    {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
    (σ : Fin d) :
    gaugeVertex A X v η σ = gaugeVertex A Y v η σ := by
  rcases hXY with ⟨c, hc, hedge⟩
  unfold gaugeVertex
  refine Finset.sum_congr rfl ?_
  intro η' _
  have hprod :
      ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie) =
        ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
    calc
      ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie) =
          ∏ ie : IncidentEdge G v,
            edgeScalarAt (G := G) c v ie *
              edgeGaugeAt A Y v ie (η ie) (η' ie) := by
            refine Finset.prod_congr rfl ?_
            intro ie _
            have hEntry := congrArg (fun M => M (η ie) (η' ie)) (hedge v ie)
            simpa [Matrix.smul_apply, smul_eq_mul] using hEntry
      _ = (∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie) *
            ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
            rw [hc v, one_mul]
  rw [hprod]

/-- Balanced edge-scalar equivalent gauges define the same gauged PEPS tensor.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; balanced endpoint
scalars leave every local gauged tensor unchanged, hence the whole gauged
tensor is unchanged. -/
theorem GaugeEquivModEdgeScalars.applyGauge_eq
    {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y) :
    applyGauge A X = applyGauge A Y := by
  change Tensor.mk A.bondDim (fun v => gaugeVertex A X v) =
    Tensor.mk A.bondDim (fun v => gaugeVertex A Y v)
  congr
  funext v η σ
  exact GaugeEquivModEdgeScalars.gaugeVertex_eq (G := G) hXY v η σ

/-- Balanced edge-scalar equivalent gauges give the same PEPS state.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the balanced quotient
acts trivially on every local gauged tensor, and hence on the contracted state. -/
theorem GaugeEquivModEdgeScalars.applyGauge_sameState
    {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y) :
    SameState (applyGauge A X) (applyGauge A Y) := by
  intro σ
  rw [GaugeEquivModEdgeScalars.applyGauge_eq (G := G) hXY]

/-! ### Uniqueness modulo balanced edge scalars -/

/-- If the gauged vertex tensors produced by two gauge families agree pointwise
at a vertex \(v\), then, by linear independence of the coefficient family at
\(v\), the products of incident edge-gauge matrix entries coincide for every
pair of virtual configurations.

This reduces the remaining step in `gauge_unique_mod_edge_scalars` from the
functional equality of gauged vertex tensors to an equality of scalar products
of incident edge-gauge entries, which is the proper input to the pending
tensor-factor uniqueness argument. -/
private lemma edgeGaugeProduct_eq_of_gaugeVertex_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (v : V)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (h : ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
      gaugeVertex A X v η σ = gaugeVertex A Y v η σ)
    (η η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) :
    (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie)) =
      ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
  refine (hA v).eq_coords_of_eq
    (f := fun ξ => ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (ξ ie))
    (g := fun ξ => ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (ξ ie))
    ?_ η'
  funext σ
  simpa [gaugeVertex, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h η σ

/-- **Gauge uniqueness modulo balanced edge scalars** (arXiv:1804.04964,
Theorem 2, uniqueness clause, corrected graph quotient).

If `X` and `Y` are two gauge families relating the same injective PEPS tensor
`A` to the same tensor `B`, then their oriented endpoint actions differ by
edge scalars `c_e` whose product around every vertex is `1`.

**Local fix (balanced edge scalars):** The source states that the gauges
are unique up to a multiplicative constant. On a general graph the connected
triangle with one-dimensional bonds refutes uniqueness modulo one global scalar.
The graph-correct quotient is uniqueness modulo vertex-balanced edge scalars;
see `docs/paper-gaps/peps_gauge_edge_scalars.tex`.

**Scope restriction (positive bond dimensions):** The hypothesis
`hpos : ∀ e, 0 < A.bondDim e` is the paper's standing normal-PEPS convention
that every bond space is nonzero (it matches `hposA` in the existence direction
`fundamentalTheorem_PEPS`). It is genuinely needed: if a bond space is empty the
local virtual configurations at its endpoints vanish, the linear-independence
hypothesis becomes vacuous there, and the gauges on a positive-dimensional bond
adjacent to such an endpoint are left unconstrained, so the conclusion can fail.
This restriction is recorded in `docs/paper-gaps/peps_gauge_edge_scalars.tex`.

The proof extracts, at every vertex `v`, the local scalar ratios relating the
two oriented edge-gauge families via `piProduct_forms_scalar`, then assembles
them into one edge-scalar family `c` whose oriented product is `1` at every
vertex (`IsVertexBalanced c`). -/
theorem gauge_unique_mod_edge_scalars (A B : Tensor G d)
    (hA : IsVertexInjective A)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (hX : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex A X v η σ)
    (hY : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex A Y v η σ) :
    GaugeEquivModEdgeScalars (G := G) A X Y := by
  -- Step 1: combine `hX` and `hY` to obtain vertex-wise equality of the
  -- gauged tensors `gaugeVertex A X v η σ = gaugeVertex A Y v η σ`.
  have hGauge : ∀ (v : V)
      (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      gaugeVertex A X v η σ = gaugeVertex A Y v η σ :=
    fun v η σ => (hX v η σ).symm.trans (hY v η σ)
  -- Step 2: linear independence at v promotes this to equality of incident
  -- edge-gauge products for every configuration pair.
  have hProd : ∀ (v : V)
      (η η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)),
      (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie)) =
        ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) :=
    fun v η η' =>
      edgeGaugeProduct_eq_of_gaugeVertex_eq (G := G) A hA v X Y (hGauge v) η η'
  -- Each oriented endpoint gauge is invertible.
  have hUnitX : ∀ (v : V) (ie : IncidentEdge G v), IsUnit (edgeGaugeAt A X v ie) :=
    fun v ie => ⟨⟨_, _, edgeGaugeAt_mul_inv A X v ie, edgeGaugeAtInv_mul A X v ie⟩, rfl⟩
  have hUnitY : ∀ (v : V) (ie : IncidentEdge G v), IsUnit (edgeGaugeAt A Y v ie) :=
    fun v ie => ⟨⟨_, _, edgeGaugeAt_mul_inv A Y v ie, edgeGaugeAtInv_mul A Y v ie⟩, rfl⟩
  -- Bond spaces are nonempty under positive bond dimensions.
  have hneVertex : ∀ (v : V) (ie : IncidentEdge G v), Nonempty (Fin (A.bondDim ie.1)) :=
    fun _ ie => ⟨⟨0, hpos ie.1⟩⟩
  -- Step 3: at every vertex, extract the local proportionality scalars whose
  -- oriented product is one (`piProduct_forms_scalar`).
  have hvertex : ∀ v : V, ∃ cv : IncidentEdge G v → ℂ,
      (∀ ie : IncidentEdge G v,
          edgeGaugeAt A X v ie = cv ie • edgeGaugeAt A Y v ie) ∧
        (∏ ie : IncidentEdge G v, cv ie) = 1 := by
    intro v
    have hne : ∀ ie : IncidentEdge G v, Nonempty (Fin (A.bondDim ie.1)) := hneVertex v
    exact piProduct_forms_scalar (ι := IncidentEdge G v)
      (n := fun ie => Fin (A.bondDim ie.1))
      (M := fun ie => edgeGaugeAt A X v ie) (N := fun ie => edgeGaugeAt A Y v ie)
      (hUnitY v) (hne := hne) (fun η η' => hProd v η η')
  choose cvFun hcvProp hcvProd using hvertex
  -- Scalar relating each oriented endpoint gauge to the other is unique, since
  -- the second gauge matrix is invertible (hence nonzero).
  have huniq : ∀ (v : V) (ie : IncidentEdge G v) (a b : ℂ),
      edgeGaugeAt A X v ie = a • edgeGaugeAt A Y v ie →
      edgeGaugeAt A X v ie = b • edgeGaugeAt A Y v ie → a = b := by
    intro v ie a b ha hb
    have hNne : edgeGaugeAt A Y v ie ≠ 0 := by
      rintro h0
      have hu : IsUnit (0 : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :=
        h0 ▸ hUnitY v ie
      obtain ⟨i⟩ := hneVertex v ie
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_zero ⟨i⟩] at hu
      exact not_isUnit_zero hu
    have hab : a • edgeGaugeAt A Y v ie = b • edgeGaugeAt A Y v ie := ha ▸ hb
    exact sub_eq_zero.mp (by
      by_contra hsub
      apply hNne
      have hsmul : (a - b) • edgeGaugeAt A Y v ie = 0 := by
        rw [sub_smul, hab, sub_self]
      exact (smul_eq_zero.mp hsmul).resolve_left hsub)
  -- Define the global edge scalar from the lower-endpoint extraction.
  -- For an edge `e`, the lower endpoint `e.1.1` carries the incident edge `e`
  -- with `edgeGaugeAt A X (e.1.1) ie = ↑(X e)`.
  have hloIncX : ∀ e : Edge G,
      edgeGaugeAt A X e.1.1 ⟨e, Or.inl rfl⟩ = (↑(X e) : Matrix _ _ ℂ) := by
    intro e; simp [edgeGaugeAt]
  have hloIncY : ∀ e : Edge G,
      edgeGaugeAt A Y e.1.1 ⟨e, Or.inl rfl⟩ = (↑(Y e) : Matrix _ _ ℂ) := by
    intro e; simp [edgeGaugeAt]
  -- The lower-endpoint scalar of each edge is nonzero.
  have hlamne : ∀ e : Edge G, cvFun e.1.1 ⟨e, Or.inl rfl⟩ ≠ 0 := by
    intro e h0
    have hrel := hcvProp e.1.1 ⟨e, Or.inl rfl⟩
    rw [hloIncX, hloIncY, h0, zero_smul] at hrel
    have hXunit : IsUnit (X e).val := (X e).isUnit
    obtain ⟨i⟩ := hneVertex e.1.1 ⟨e, Or.inl rfl⟩
    rw [hrel, Matrix.isUnit_iff_isUnit_det, Matrix.det_zero ⟨i⟩] at hXunit
    exact not_isUnit_zero hXunit
  -- The edge-scalar family.
  set c : (e : Edge G) → Units ℂ :=
    fun e => Units.mk0 _ (hlamne e) with hc_def
  -- The lower-endpoint proportionality `↑(X e) = c e • ↑(Y e)`.
  have hprop : ∀ e : Edge G, (X e).val = (c e : ℂ) • (Y e).val := by
    intro e
    have := hcvProp e.1.1 ⟨e, Or.inl rfl⟩
    rwa [hloIncX, hloIncY] at this
  -- The corresponding relation between the inverse gauges, used at the upper
  -- endpoint of each edge: `↑(X e)⁻¹ = (c e)⁻¹ • ↑(Y e)⁻¹`.
  have hpropInv : ∀ e : Edge G,
      ((X e)⁻¹).val = ((c e)⁻¹ : ℂ) • ((Y e)⁻¹).val := by
    intro e
    have hcne : (c e : ℂ) ≠ 0 := (c e).ne_zero
    have hYdet : IsUnit (Y e).val.det := (Matrix.isUnit_iff_isUnit_det _).mp (Y e).isUnit
    rw [Matrix.coe_units_inv, Matrix.coe_units_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [hprop e, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hcne, one_smul, Matrix.mul_nonsing_inv _ hYdet]
  refine ⟨c, ?_, ?_⟩
  · -- `IsVertexBalanced c`: the oriented product at each vertex is one.
    intro v
    -- `edgeScalarAt c v ie` equals the local extraction `cvFun v ie` by uniqueness.
    have hmatch : ∀ ie : IncidentEdge G v,
        edgeScalarAt (G := G) c v ie = cvFun v ie := by
      intro ie
      refine huniq v ie _ _ ?_ (hcvProp v ie)
      unfold edgeScalarAt edgeGaugeAt
      by_cases h : ie.1.1.1 = v
      · simp only [if_pos h]; rw [hprop ie.1]
      · simp only [if_neg h]
        rw [hpropInv ie.1, Matrix.transpose_smul, Units.val_inv_eq_inv_val]
    calc (∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie)
        = ∏ ie : IncidentEdge G v, cvFun v ie :=
          Finset.prod_congr rfl (fun ie _ => hmatch ie)
      _ = 1 := hcvProd v
  · -- The oriented relation between the two gauge families at every endpoint.
    intro v ie
    unfold edgeScalarAt edgeGaugeAt
    by_cases h : ie.1.1.1 = v
    · simp only [if_pos h]; rw [hprop ie.1]
    · simp only [if_neg h]
      rw [hpropInv ie.1, Matrix.transpose_smul, Units.val_inv_eq_inv_val]


end PEPS
end TNLean
