import TNLean.PEPS.FundamentalTheorem.OneVertexComparison
import TNLean.PEPS.EdgeGaugeFamily
import TNLean.PEPS.LocalGauge
import TNLean.PEPS.TwoInjectiveComparison
import TNLean.PEPS.VertexComplement.KernelDescent
import TNLean.PEPS.EdgeScalarSolve
import TNLean.PEPS.TensorFactorScalar
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- The contraction algebra is proved. The remaining converse ingredients are
-- separated by mathematical role in
-- `docs/paper-gaps/peps_injective_ft_section3_route.tex` and
-- `docs/paper-gaps/peps_gauge_edge_scalars.tex`. The hypothesis
-- `IsVertexInjective` is the linear-independence formulation from `PEPS.Defs`,
-- which gives the local left inverses used below.

/-!
# Fundamental Theorem for injective PEPS

This root-only capstone records the full statement of the PEPS Fundamental
Theorem (arXiv:1804.04964, Section 3, Theorem 2), with the forward
bond-dimension obligation and converse gaps documented in the paper-gap notes
cited below. The separate root-only audit is tracked by issue #1512.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Local gauge extraction -/

/-- The local tensor evaluated at vertex `v` with virtual-index weighting `f`.

This computes `∑_η (∏_{ie} f(ie)(η(ie))) · A_v(η, σ)`. The map is
*multilinear* in the components of `f` (one factor per incident edge), not
linear in the full tuple — hence this is a plain function, not a `LinearMap`. -/
noncomputable def localTensorEval (A : Tensor G d) (v : V)
    (f : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1) → ℂ)
    (σ : Fin d) : ℂ :=
  ∑ η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
    (∏ ie : IncidentEdge G v, f ie (η ie)) * A.component v η σ

/-- Under the sharper local hypothesis `HasFactorizedLocalGauge`, one obtains a
factorized local gauge relation at `v`.

The local left inverse and the canonical local gauge map are defined in
`PEPS/LocalGauge`. It remains to derive `BlockedMiddleGaugeFormula` from
`SameState` by comparing the edge-blocked coefficient from `PEPS/Blocking` with
the three-site MPS reduction, then convert it to `HasFactorizedLocalGauge` by
`hasFactorizedLocalGauge_of_blockedMiddleGaugeFormula`. -/
theorem localGauge_exists (A B : Tensor G d)
    (hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (hFactorized : HasFactorizedLocalGauge A B hA hDim v) :
    ∃ (Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
            (∏ ie : IncidentEdge G v,
              (↑(Xv ie.1) : Matrix _ _ ℂ) (η ie) (η' ie)) *
              A.component v η' σ :=
  localGauge_exists_of_factorizedLocalGauge A B hA hDim v hFactorized

/-! ### Vertex injectivity of the absorbed tensor family -/

/-- Recombining a linearly independent family by an invertible matrix preserves
linear independence.

If `f` is linearly independent and `K` is an invertible square matrix indexed by
the same finite type, then the recombined family `i ↦ ∑ j, K i j • f j` is again
linearly independent: a vanishing combination `∑ i c i • (∑ j K i j • f j) = 0`
rearranges to `∑ j (c ᵥ* K) j • f j = 0`, whose coefficient vector `c ᵥ* K` is
zero by independence of `f`, and right-multiplying by `K⁻¹` forces `c = 0`. -/
theorem linearIndependent_recombine {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}
    [AddCommGroup M] [Module ℂ M]
    (f : ι → M) (hf : LinearIndependent ℂ f)
    (K : Matrix ι ι ℂ) (hK : IsUnit K) :
    LinearIndependent ℂ (fun i => ∑ j, K i j • f j) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc
  have hexpand : ∑ j, (Matrix.vecMul c K) j • f j = ∑ i, c i • ∑ j, K i j • f j := by
    calc ∑ j, (Matrix.vecMul c K) j • f j
        = ∑ j, (∑ i, c i * K i j) • f j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rfl
      _ = ∑ j, ∑ i, (c i * K i j) • f j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.sum_smul]
      _ = ∑ i, ∑ j, (c i * K i j) • f j := Finset.sum_comm
      _ = ∑ i, c i • ∑ j, K i j • f j := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [smul_smul]
  have hc' : ∑ j, (Matrix.vecMul c K) j • f j = 0 := by rw [hexpand, hc]
  have hzero := hf (Matrix.vecMul c K) hc'
  have hvz : Matrix.vecMul c K = 0 := funext hzero
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK
  have hround : Matrix.vecMul (Matrix.vecMul c K) K⁻¹ = 0 := by rw [hvz]; simp
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv K hdet, Matrix.vecMul_one] at hround
  exact fun i => congrFun hround i

/-- The product over a finite index of two per-leg matrices, summed over the
intermediate configuration, factorizes leg by leg into the per-leg products.

This is the matrix-multiplication form of the contraction `∑_{η'} ∏_i M_i(η, η')
· N_i(η', ξ) = ∏_i (M_i · N_i)(η, ξ)` used to invert the per-edge gauge kernel. -/
theorem piProductKernel_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (M Minv : (i : ι) → Matrix (n i) (n i) ℂ)
    (hMl : ∀ i, M i * Minv i = 1) :
    (Matrix.of (fun η η' : (i : ι) → n i => ∏ i, M i (η i) (η' i))) *
      (Matrix.of (fun η η' : (i : ι) → n i => ∏ i, Minv i (η i) (η' i))) = 1 := by
  classical
  ext η ξ
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  have hmerge :
      (∑ η' : (i : ι) → n i, (∏ i, M i (η i) (η' i)) * ∏ i, Minv i (η' i) (ξ i)) =
        ∑ η' : (i : ι) → n i, ∏ i, M i (η i) (η' i) * Minv i (η' i) (ξ i) := by
    refine Finset.sum_congr rfl ?_
    intro η' _
    rw [Finset.prod_mul_distrib]
  rw [hmerge]
  have hstep :
      (∑ η' : (i : ι) → n i, ∏ i, M i (η i) (η' i) * Minv i (η' i) (ξ i)) =
        ∏ i, ∑ k : n i, M i (η i) k * Minv i k (ξ i) := by
    simpa [Fintype.piFinset_univ] using
      (Finset.prod_univ_sum (fun _ : ι => Finset.univ)
        (fun i k => M i (η i) k * Minv i k (ξ i))).symm
  rw [hstep]
  have heach : ∀ i, (∑ k : n i, M i (η i) k * Minv i k (ξ i)) =
      if η i = ξ i then 1 else 0 := by
    intro i
    have hmm : (∑ k : n i, M i (η i) k * Minv i k (ξ i)) = (M i * Minv i) (η i) (ξ i) := by
      rw [Matrix.mul_apply]
    rw [hmm, hMl i, Matrix.one_apply]
  simp_rw [heach]
  rw [Fintype.prod_boole, Matrix.one_apply]
  by_cases h : η = ξ
  · subst h; simp
  · rw [if_neg h, if_neg (fun hall => h (funext hall))]

/-- The per-leg product kernel built from per-leg invertible matrices is
invertible, with inverse the product kernel of the per-leg inverses. -/
theorem piProductKernel_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (M Minv : (i : ι) → Matrix (n i) (n i) ℂ)
    (hMl : ∀ i, M i * Minv i = 1) (hMr : ∀ i, Minv i * M i = 1) :
    IsUnit (Matrix.of (fun η η' : (i : ι) → n i => ∏ i, M i (η i) (η' i))) :=
  ⟨⟨Matrix.of (fun η η' : (i : ι) → n i => ∏ i, M i (η i) (η' i)),
    Matrix.of (fun η η' : (i : ι) → n i => ∏ i, Minv i (η i) (η' i)),
    piProductKernel_mul M Minv hMl, piProductKernel_mul Minv M hMr⟩, rfl⟩

/-- The pointwise inverse of the oriented endpoint gauge `edgeGaugeAt`.

At the lower endpoint it is `(Z_e)⁻¹`; at the upper endpoint it is `(Z_e)ᵀ`,
inverting the `(Z_e⁻¹)ᵀ` used by `edgeGaugeAt`. -/
noncomputable def edgeGaugeAtInv (B : Tensor G d)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (v : V) (ie : IncidentEdge G v) :
    Matrix (Fin (B.bondDim ie.1)) (Fin (B.bondDim ie.1)) ℂ :=
  if ie.1.1.1 = v then (↑((Z ie.1)⁻¹)) else (↑(Z ie.1))ᵀ

omit [Fintype V] in
/-- `edgeGaugeAtInv` is a right inverse of `edgeGaugeAt`. -/
theorem edgeGaugeAt_mul_inv (B : Tensor G d) (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeGaugeAt B Z v ie * edgeGaugeAtInv (G := G) B Z v ie = 1 := by
  unfold edgeGaugeAt edgeGaugeAtInv
  by_cases h : ie.1.1.1 = v
  · simp only [if_pos h]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · simp only [if_neg h]
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

omit [Fintype V] in
/-- `edgeGaugeAtInv` is a left inverse of `edgeGaugeAt`. -/
theorem edgeGaugeAtInv_mul (B : Tensor G d) (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeGaugeAtInv (G := G) B Z v ie * edgeGaugeAt B Z v ie = 1 := by
  unfold edgeGaugeAt edgeGaugeAtInv
  by_cases h : ie.1.1.1 = v
  · simp only [if_pos h]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  · simp only [if_neg h]
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]

/-- Vertex injectivity is preserved by absorbing oriented edge gauges.

Each `gaugeVertex B Z v` recombines the linearly independent family
`B.component v` by the per-edge gauge kernel, which is invertible because every
oriented endpoint gauge `edgeGaugeAt B Z v ie` is invertible. Linear
independence is therefore preserved (`linearIndependent_recombine`), and the bond spaces
are unchanged (`absorbEdgeGauges_bondDim`).

Source: arXiv:1804.04964, Section 3, lines 1037--1038: the absorbed family
`Btilde` is again a normal (injective) PEPS. -/
theorem isVertexInjective_absorbEdgeGauges (B : Tensor G d)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (hB : IsVertexInjective B) :
    IsVertexInjective (absorbEdgeGauges B Z) := by
  intro v
  have hcomp : (absorbEdgeGauges B Z).component v =
      fun η => fun σ => gaugeVertex B Z v η σ := by
    funext η σ; rw [absorbEdgeGauges_component]
  rw [hcomp]
  set K : Matrix (LocalVirtualConfig B v) (LocalVirtualConfig B v) ℂ :=
    Matrix.of (fun η η' => ∏ ie : IncidentEdge G v,
      edgeGaugeAt B Z v ie (η ie) (η' ie)) with hKdef
  have hrewrite : (fun η : LocalVirtualConfig B v => fun σ => gaugeVertex B Z v η σ) =
      (fun η => ∑ η', K η η' • B.component v η') := by
    funext η σ
    rw [gaugeVertex]
    simp only [hKdef, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrewrite]
  have hKunit : IsUnit K := by
    rw [hKdef]
    exact piProductKernel_isUnit
      (fun ie => edgeGaugeAt B Z v ie) (fun ie => edgeGaugeAtInv (G := G) B Z v ie)
      (fun ie => edgeGaugeAt_mul_inv B Z v ie) (fun ie => edgeGaugeAtInv_mul B Z v ie)
  exact linearIndependent_recombine (B.component v) (hB v) K hKunit

/-! ### Gauge consistency across edges -/

/-- Post-absorption edge insertion equality from arXiv:1804.04964, Section 3,
lines 1037--1065. Assuming the separately tracked bond-dimension equality
\(D_A=D_B\) (#874), the edge gauges obtained from the three-site comparison can
be absorbed into the second tensor family so that every edge insertion in \(A\)
agrees with the transported edge insertion in the absorbed tensor family.

**Positive-bond hypothesis (faithfulness fix).** The edge gauges come from
the edge-gauge existence result, which blocks the PEPS around each edge into a
three-site injective chain. That step needs every bond dimension positive,
\(\forall e,\ 0 < D_A(e)\), the source's standing assumption that injective PEPS
have nonzero virtual bond spaces. A vertex incident to a zero-dimensional bond
has an empty virtual-configuration family, making linear independence vacuous.
The same defect was corrected for the PEPS fundamental theorem, gauge
consistency, and the edge-blocked three-site injectivity (#1366); it is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
theorem post_absorption_edge_insertion_equality (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B) (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ Z, PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z) := by
  classical
  obtain ⟨X, hX⟩ := exists_edgeGaugeFamily A B hA hB hAB hDim hpos
  choose Φ hΦcoeff hΦconj using hX
  refine ⟨fun e => glReindex (congr_fun hDim e) (glTranspose (X e)), ?_, ?_⟩
  · exact hDim
  intro e σ M
  simp only [absorbEdgeGauges]
  rw [hΦcoeff e σ M, hΦconj e M, edgeInsertedCoeff_applyGauge]
  congr 1
  have hZt :
      (↑(glReindex (congr_fun hDim e) (glTranspose (X e))) :
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)ᵀ =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e))
          (↑(X e) : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
    rw [glReindex_coe, glTranspose_coe]
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex,
      Matrix.transpose_transpose]
  have hZit :
      ((↑(glReindex (congr_fun hDim e) (glTranspose (X e))) :
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)⁻¹)ᵀ =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e))
    (↑(X e)⁻¹ : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
    rw [← Matrix.GeneralLinearGroup.coe_inv, ← map_inv, glReindex_coe,
      glTranspose_inv_coe]
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex,
      Matrix.transpose_transpose]
  rw [hZt, hZit, map_mul, map_mul]
  rfl

omit [Fintype V] in
/-- Reindexing a PEPS tensor along a bond-dimension equality preserves vertex
injectivity: the local coefficient family of the reindexed tensor is the
original family precomposed with the bondwise index recast, an injective
reindexing of the configuration type. -/
theorem isVertexInjective_reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (hB : IsVertexInjective B) :
    IsVertexInjective (reindexTensor (G := G) B h) := by
  intro v
  have heq : (reindexTensor (G := G) B h).component v
      = (B.component v) ∘ (Equiv.piCongrRight (fun ie : IncidentEdge G v =>
          finCongr (congr_fun h ie.1))) := by
    funext η; rfl
  rw [heq]
  exact (hB v).comp _ (Equiv.piCongrRight _).injective

/-- **Per-vertex scalar from the one-vertex-versus-complement comparison.**

After absorbing the edge gauges `Z` into the second tensor family
(`absorbEdgeGauges B Z`), the post-absorption edge-insertion equality
(`PostAbsorptionEdgeInsertionEquality`) supplies, via
`sameTwoBlockInsertions_of_edgeInsertedCoeff_eq`, equality of all one-bond
insertions for the vertex/complement two-block split. The four two-block
injectivity facts and `one_vertex_complement_comparison` then yield, at every
vertex with a nonempty incident-edge set, a nonzero scalar `c` with
`A_v = c · gaugeVertex B Z v`.

This is the per-vertex scalar of arXiv:1804.04964, Section 3 (the passage after
`eq:inj_equal_edge`), recorded in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`. -/
theorem perVertexScalar (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (hPA : PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z))
    (v : V) [Nonempty (IncidentEdge G v)] :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      A.component v η σ =
        c * gaugeVertex B Z v
          (fun ie => Fin.cast (congr_fun hPA.bondDim_eq ie.1) (η ie)) σ := by
  classical
  have hPA_abs := hPA
  set Btilde := absorbEdgeGauges B Z with hBt
  have hbd : A.bondDim = Btilde.bondDim := hPA.bondDim_eq
  have hBtinj : IsVertexInjective Btilde := isVertexInjective_absorbEdgeGauges B Z hB
  have hposBt : ∀ e : Edge G, 0 < Btilde.bondDim e := by
    intro e; rw [← congr_fun hbd e]; exact hpos e
  have hedge : ∀ (ie : IncidentEdge G v)
      (N : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) (σ : V → Fin d),
      edgeInsertedCoeff (G := G) A ie.1 σ N =
        edgeInsertedCoeff (G := G) Btilde ie.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd ie.1)) N) :=
    fun ie N σ => hPA.edgeInsertedCoeff_eq ie.1 σ N
  obtain ⟨c, hc_ne, hprop⟩ := one_vertex_complement_comparison
      (ExternalVertex := PUnit.{1}) (ExternalComplement := PUnit.{1})
    (vertexTwoBlock (G := G) A v) (vertexTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) v)
    (complementTwoBlock (G := G) A v)
    (complementTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) v)
    (isTwoBlockInjective_vertexTwoBlock (G := G) A hA v)
    (isTwoBlockInjective_complementTwoBlock (G := G) A hA hpos v)
    (isTwoBlockInjective_vertexTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd)
      (isVertexInjective_reindexTensor Btilde hbd hBtinj) v)
    (isTwoBlockInjective_complementTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd)
      (isVertexInjective_reindexTensor Btilde hbd hBtinj)
      (by intro e; rw [reindexTensor_bondDim]; exact hpos e) v)
    (sameTwoBlockInsertions_of_edgeInsertedCoeff_eq A Btilde v hbd hedge)
  refine ⟨c, hc_ne, fun η σ => ?_⟩
  have hlocal := hprop (PUnit.unit : PUnit) η σ
  change A.component v η σ =
    c * (absorbEdgeGauges B Z).component v
      (fun ie => Fin.cast (congr_fun hPA_abs.bondDim_eq ie.1) (η ie)) σ
  simpa only [vertexTwoBlock, reindexTensor_component, hBt] using hlocal

/-! ### Construction of the global gauge from per-vertex scalars

Closing `gaugeConsistency` from `perVertexScalar` and
`exists_edgeScalars_of_connected` absorbs the per-vertex scalars $c_v$ into one
global gauge family: on a connected graph the $c_v$ satisfy $\prod_v c_v = 1$,
the spanning-tree edge-scalar solve realizes $c_v^{-1}$ as the oriented
incidence product of one edge-scalar family $s$, and folding $s$ into the
inverse of the absorbed edge gauges $Z$ produces the global gauge.
Source: arXiv:1804.04964, Section 3, the passage after `eq:inj_equal_edge`;
recorded in `docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`. -/

/-- Inverting a product kernel. If a family `f` is the product kernel of `M`
applied to `g`, and `Minv` is the per-leg left inverse of `M`, then `g` is the
product kernel of `Minv` applied to `f`. This is the linear-algebra core of
recovering `B` from the absorbed family. -/
theorem productKernel_invert {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (M Minv : (i : ι) → Matrix (n i) (n i) ℂ)
    (hMr : ∀ i, Minv i * M i = 1)
    (f g : ((i : ι) → n i) → W)
    (h : ∀ η, f η = ∑ η', (∏ i, M i (η i) (η' i)) • g η') :
    ∀ η, g η = ∑ η', (∏ i, Minv i (η i) (η' i)) • f η' := by
  intro η
  have hrw : (∑ η' : (i : ι) → n i, (∏ i, Minv i (η i) (η' i)) • f η')
      = ∑ η' : (i : ι) → n i, (∏ i, Minv i (η i) (η' i)) •
          (∑ ξ : (i : ι) → n i, (∏ i, M i (η' i) (ξ i)) • g ξ) := by
    refine Finset.sum_congr rfl ?_
    intro η' _
    rw [h η']
  rw [hrw]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcollapse : ∀ ξ : (i : ι) → n i,
      (∑ η' : (i : ι) → n i, (∏ i, Minv i (η i) (η' i)) * (∏ i, M i (η' i) (ξ i)))
        = if η = ξ then 1 else 0 := by
    intro ξ
    have hmul := piProductKernel_mul Minv M hMr
    have hval := congrArg (fun N : Matrix ((i : ι) → n i) ((i : ι) → n i) ℂ => N η ξ) hmul
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at hval
    convert hval using 2
  refine Eq.symm ?_
  calc (∑ ξ : (i : ι) → n i, ∑ η' : (i : ι) → n i,
            ((∏ i, Minv i (η i) (η' i)) * (∏ i, M i (η' i) (ξ i))) • g ξ)
      = ∑ ξ : (i : ι) → n i,
          (∑ η' : (i : ι) → n i,
            (∏ i, Minv i (η i) (η' i)) * (∏ i, M i (η' i) (ξ i))) • g ξ := by
        refine Finset.sum_congr rfl ?_
        intro ξ _
        rw [Finset.sum_smul]
    _ = ∑ ξ : (i : ι) → n i, (if η = ξ then (1 : ℂ) else 0) • g ξ := by
        refine Finset.sum_congr rfl ?_
        intro ξ _
        rw [hcollapse ξ]
    _ = g η := by simp

/-- The scalar matrix as an element of `GL (Fin n) ℂ`. -/
noncomputable def scalarGL {n : ℕ} (s : ℂˣ) : GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.scalar (Fin n) s

theorem scalarGL_coe {n : ℕ} (s : ℂˣ) :
    (↑(scalarGL (n := n) s) : Matrix (Fin n) (Fin n) ℂ) = Matrix.scalar (Fin n) (s : ℂ) :=
  rfl

/-- The nonsingular inverse of a unit scalar multiple of an invertible matrix. -/
theorem smul_matrix_inv {n : ℕ} (s : ℂˣ) (M : Matrix (Fin n) (Fin n) ℂ) (h : IsUnit M.det) :
    ((s : ℂ) • M)⁻¹ = (s : ℂ)⁻¹ • M⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, inv_mul_cancel₀ s.ne_zero, Matrix.nonsing_inv_mul _ h, one_smul]

/-- The scalar matrix is central, so it commutes with every invertible matrix. -/
theorem scalarGL_comm {n : ℕ} (s : ℂˣ) (W : GL (Fin n) ℂ) :
    W * scalarGL s = scalarGL s * W := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalarGL_coe]
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

/-- The global gauge family built from edge scalars `s` and the absorbed edge
gauges `Z`: on each edge, the transported inverse `Z_e⁻¹` scaled by `s_e`. -/
noncomputable def globalGauge (A B : Tensor G d) (hbd : A.bondDim = B.bondDim)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (s : Edge G → ℂˣ) :
    (e : Edge G) → GL (Fin (A.bondDim e)) ℂ :=
  fun e => scalarGL (s e) * glReindex (congr_fun hbd e).symm ((Z e)⁻¹)

omit [Fintype V] in
/-- The oriented endpoint action of the global gauge at an incident edge equals
the endpoint scalar times the transported inverse endpoint gauge of `Z`. This is
the matrix identity that absorbs the per-vertex scalar into the edge gauges. -/
theorem edgeGaugeAt_globalGauge (A B : Tensor G d) (hbd : A.bondDim = B.bondDim)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (s : Edge G → ℂˣ)
    (v : V) (ie : IncidentEdge G v) :
    edgeGaugeAt A (globalGauge A B hbd Z s) v ie =
      (edgeScalarUnit (G := G) s v ie : ℂ) •
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd ie.1).symm)
          (edgeGaugeAtInv (G := G) B Z v ie) := by
  unfold edgeGaugeAt edgeGaugeAtInv globalGauge edgeScalarUnit
  by_cases h : ie.1.1.1 = v
  · simp only [if_pos h]
    rw [Units.val_mul, scalarGL_coe, glReindex_coe,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  · simp only [if_neg h]
    have hdet : IsUnit (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd ie.1).symm)
        (↑((Z ie.1)⁻¹) : Matrix (Fin (B.bondDim ie.1)) (Fin (B.bondDim ie.1)) ℂ)).det := by
      rw [← glReindex_coe]
      exact (Matrix.isUnit_iff_isUnit_det _).mp
        (glReindex (congr_fun hbd ie.1).symm ((Z ie.1)⁻¹)).isUnit
    have hXinv : ((scalarGL (n := A.bondDim ie.1) (s ie.1)
          * glReindex (congr_fun hbd ie.1).symm ((Z ie.1)⁻¹))⁻¹
        : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
        = (↑(s ie.1) : ℂ)⁻¹ •
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd ie.1).symm)
            (↑(Z ie.1) : Matrix _ _ ℂ)) := by
      rw [scalarGL_coe, glReindex_coe,
        Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
        smul_matrix_inv (s ie.1) _ hdet]
      congr 1
      rw [← glReindex_coe, ← glReindex_coe, ← Matrix.GeneralLinearGroup.coe_inv,
        ← map_inv, inv_inv]
    rw [Matrix.GeneralLinearGroup.coe_inv, Units.val_mul, hXinv, Matrix.transpose_smul,
      Units.val_inv_eq_inv_val]
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex]

/-- **Per-vertex global-gauge identity.** At a vertex `v`, the per-vertex scalar
relation `A_v = c · gaugeVertex B Z v` together with `∏ s_e = c⁻¹` (oriented
incidence) gives `B_v = gaugeVertex A (globalGauge …) v`. The absorbed gauge `Z`
is inverted by the product-kernel inversion, and the scalar `c⁻¹` is distributed
edgewise as the oriented incidence product of the edge scalars `s`.

Source: arXiv:1804.04964, Section 3, the passage after `eq:inj_equal_edge`. -/
theorem perVertex_gauge_identity (A B : Tensor G d)
    (hbd : A.bondDim = B.bondDim)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (s : Edge G → ℂˣ)
    (v : V)
    (c : ℂ) (hc : c ≠ 0)
    (hcs : ∏ ie : IncidentEdge G v, (edgeScalarUnit (G := G) s v ie : ℂ) = c⁻¹)
    (hPV : ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      A.component v η σ =
        c * gaugeVertex B Z v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ) :
    ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ =
        gaugeVertex A (globalGauge A B hbd Z s) v η σ := by
  classical
  set M : (ie : IncidentEdge G v) →
      Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ :=
    fun ie => Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd ie.1).symm)
      (edgeGaugeAt B Z v ie) with hM
  set Minv : (ie : IncidentEdge G v) →
      Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ :=
    fun ie => Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd ie.1).symm)
      (edgeGaugeAtInv (G := G) B Z v ie) with hMinv
  have hMr : ∀ ie, Minv ie * M ie = 1 := by
    intro ie
    rw [hM, hMinv]
    simp only
    rw [← map_mul, edgeGaugeAtInv_mul, map_one]
  set g : ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) → (Fin d → ℂ) :=
    fun η => fun σ => B.component v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ with hg
  set f : ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) → (Fin d → ℂ) :=
    fun η => fun σ => c⁻¹ * A.component v η σ with hf
  have hfMg : ∀ η, f η = ∑ η', (∏ ie, M ie (η ie) (η' ie)) • g η' := by
    intro η
    funext σ
    rw [hf]
    simp only
    rw [hPV η σ]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [gaugeVertex]
    rw [← Equiv.sum_comp (Equiv.piCongrRight
      (fun ie : IncidentEdge G v => finCongr (congr_fun hbd ie.1)))]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun η' _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    rfl
  have hgMinv := productKernel_invert M Minv hMr f g hfMg
  intro η σ
  have hgval : g η σ =
      B.component v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ := by rw [hg]
  rw [← hgval, hgMinv η]
  rw [Finset.sum_apply]
  rw [gaugeVertex]
  refine Finset.sum_congr rfl (fun η' _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hf]
  simp only
  have hprodX : (∏ ie, edgeGaugeAt A (globalGauge A B hbd Z s) v ie (η ie) (η' ie))
      = c⁻¹ * ∏ ie, Minv ie (η ie) (η' ie) := by
    have hpw : ∀ ie, edgeGaugeAt A (globalGauge A B hbd Z s) v ie (η ie) (η' ie)
        = (edgeScalarUnit (G := G) s v ie : ℂ) * Minv ie (η ie) (η' ie) := by
      intro ie
      rw [edgeGaugeAt_globalGauge, Matrix.smul_apply, smul_eq_mul, hMinv]
    rw [Finset.prod_congr rfl (fun ie _ => hpw ie), Finset.prod_mul_distrib, hcs]
  rw [hprodX]
  ring

/-- The state coefficient is invariant under reindexing a tensor along a
bond-dimension equality. -/
theorem stateCoeff_reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (σ : V → Fin d) :
    stateCoeff (reindexTensor (G := G) B h) σ = stateCoeff B σ := by
  unfold stateCoeff
  refine Fintype.sum_equiv
    (Equiv.piCongrRight (fun e => finCongr (congr_fun h e))) _ _ (fun η => ?_)
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [reindexTensor_component]
  rfl

/-- **Vertex-complement decomposition of the state coefficient.** Splitting the
contraction at a chosen vertex `v`, the state coefficient factors as a sum over
the `v`-star boundary configuration of the single-vertex coefficient at `v`
times the contracted complement weight on `V\{v}`.

The physical legs glue as `σ` on `v` and the restriction of `σ` to `V\{v}` on
the complement. This is the one-vertex-versus-complement split of
arXiv:1804.04964, Section 3 (lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`), read at the level of the closed state
coefficient rather than the bond-inserted coefficient. -/
theorem stateCoeff_eq_vertexComplement (A : Tensor G d) (v : V) (σ : V → Fin d) :
    stateCoeff A σ =
      ∑ starCfg : LocalVirtualConfig A v,
        A.component v starCfg (σ v) *
          vertexComplementWeight (G := G) A v starCfg (fun w => σ w.1) := by
  classical
  unfold stateCoeff
  -- Group the global virtual configurations by their `v`-star label.
  rw [← Finset.sum_fiberwise Finset.univ
      (fun ζ : VirtualConfig A => vertexStarLabel (G := G) A v ζ)
      (fun ζ => ∏ w : V, A.component w (fun ie => ζ ie.1) (σ w))]
  refine Finset.sum_congr rfl (fun starCfg _ => ?_)
  -- On each fiber the `v`-factor is constant; the remaining product is the
  -- complement weight.
  rw [vertexComplementWeight, Finset.mul_sum]
  refine Finset.sum_congr (by ext ζ; simp [Finset.mem_filter, eq_comm]) (fun ζ hζ => ?_)
  rw [Finset.mem_filter] at hζ
  have hstar : ∀ ie : IncidentEdge G v, ζ ie.1 = starCfg ie := by
    intro ie
    have := congrFun hζ.2 ie
    simpa [vertexStarLabel] using this
  rw [prod_split_off_vertex v (fun w => A.component w (fun ie => ζ ie.1) (σ w))]
  -- The `v`-factor reads the star label; the complement product is the summand.
  have hvfac : A.component v (fun ie => ζ ie.1) (σ v) = A.component v starCfg (σ v) := by
    congr 1
    funext ie
    exact hstar ie
  rw [hvfac]

/-- A vertex-injective PEPS with positive bond dimensions has a nonzero state
coefficient.

Source: arXiv:1804.04964, Section 3. Injective PEPS describe genuine, nonzero
states; the nonvanishing is the closed-network instance of injectivity of the
contracted blocked tensor. Splitting at a vertex `v`
(`stateCoeff_eq_vertexComplement`) writes the state coefficient as a contraction
of the single-vertex coefficient family at `v` against the complement weight
family. If every state coefficient vanished, then for each complement physical
configuration the complement weights would form a kernel vector of the local
tensor map at `v`; vertex injectivity (`localCoeff_eq_zero_of_contract_zero`)
forces the whole complement weight family to vanish, contradicting linear
independence of that family (`isTwoBlockInjective_complementTwoBlock`), which is
nonzero because positive bond dimensions make the `v`-star configuration type
nonempty. -/
theorem exists_stateCoeff_ne_zero (A : Tensor G d)
    (hA : IsVertexInjective A) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ σ : V → Fin d, stateCoeff A σ ≠ 0 := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    -- The complement weight family is linearly independent, hence has a nonzero
    -- member at some `v`-star configuration `starCfg₀`.
    have hcompInj : LinearIndependent ℂ (vertexComplementTensorFamily (G := G) A v) :=
      vertexComplementTensorInjective_of_isVertexInjective (G := G) A v hA hpos
    -- The `v`-star configuration type is nonempty by positive bond dimensions.
    have hNeStar : Nonempty (LocalVirtualConfig A v) := by
      refine ⟨fun ie => ?_⟩
      have := hpos ie.1
      exact ⟨0, this⟩
    obtain ⟨starCfg₀⟩ := hNeStar
    have hne : vertexComplementTensorFamily (G := G) A v starCfg₀ ≠ 0 :=
      hcompInj.ne_zero starCfg₀
    -- Some complement physical configuration gives a nonzero complement weight.
    obtain ⟨τ₀, hτ₀⟩ :
        ∃ τ, vertexComplementWeight (G := G) A v starCfg₀ τ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by funext τ; simpa [vertexComplementTensorFamily] using hall τ)
    -- Suppose, for contradiction, every state coefficient vanishes.
    by_contra hzero
    push Not at hzero
    -- For each physical leg `σ₁` at `v`, the complement weights form a kernel
    -- vector of the local tensor map at `v`.
    have hkernel : ∀ σ₁ : Fin d,
        ∑ starCfg : LocalVirtualConfig A v,
          vertexComplementWeight (G := G) A v starCfg τ₀ •
            A.component v starCfg σ₁ = 0 := by
      intro σ₁
      have hsc := hzero (assembleσ (V := V) (d := d) v σ₁ τ₀)
      rw [stateCoeff_eq_vertexComplement A v] at hsc
      -- Rewrite the assembled physical configuration: `v ↦ σ₁`, complement ↦ `τ₀`.
      have hσv : (assembleσ (V := V) (d := d) v σ₁ τ₀) v = σ₁ :=
        assembleσ_self v σ₁ τ₀
      have hσc : (fun w : {w : V // w ≠ v} =>
          (assembleσ (V := V) (d := d) v σ₁ τ₀) w.1) = τ₀ := by
        funext w
        exact assembleσ_of_ne v σ₁ τ₀ w.2
      rw [hσv, hσc] at hsc
      -- Convert the scalar products to `•` and commute the factors.
      have hrw : (∑ starCfg : LocalVirtualConfig A v,
            A.component v starCfg σ₁ *
              vertexComplementWeight (G := G) A v starCfg τ₀)
          = ∑ starCfg : LocalVirtualConfig A v,
              vertexComplementWeight (G := G) A v starCfg τ₀ •
                A.component v starCfg σ₁ := by
        refine Finset.sum_congr rfl (fun starCfg _ => ?_)
        rw [smul_eq_mul, mul_comm]
      rw [hrw] at hsc
      exact hsc
    -- Vertex injectivity at `v` forces every complement weight at `τ₀` to vanish.
    have hRzero : (fun starCfg : LocalVirtualConfig A v =>
        vertexComplementWeight (G := G) A v starCfg τ₀) = 0 :=
      hA.localCoeff_eq_zero_of_contract_zero v _ hkernel
    exact hτ₀ (congrFun hRzero starCfg₀)
  · -- Empty vertex set: the contraction over no vertices is `1`.
    rw [not_nonempty_iff] at hV
    refine ⟨fun w => (hV.false w).elim, ?_⟩
    rw [stateCoeff]
    -- Each summand is the empty product `1`; there is at least one virtual config.
    have hone : ∀ η : VirtualConfig A,
        (∏ w : V, A.component w (fun ie => η ie.1) ((fun w => (hV.false w).elim) w)) = 1 := by
      intro η
      rw [Finset.prod_of_isEmpty]
    -- With no vertices there are no edges, so the virtual configuration type has
    -- a unique element and the sum collapses to the empty product `1`.
    have hEmptyEdge : IsEmpty (Edge G) := by
      constructor
      rintro ⟨⟨a, _⟩, _, _⟩
      exact (hV.false a).elim
    have : Unique (VirtualConfig A) := Pi.uniqueOfIsEmpty _
    rw [Fintype.sum_unique, hone]
    exact one_ne_zero

/-- **Obligation: the per-vertex scalars multiply to one.** If the vertex
scalars `c` relate `A` to the absorbed second tensor family
(`A_v = c_v · gaugeVertex B Z v`), then the nonvanishing state equality forces
`∏_v c_v = 1`. The proof substitutes the per-vertex relation into the state
contraction, factors out `∏_v c_v`, and cancels using gauge-state invariance
(`applyGauge_stateCoeff`) together with a nonzero state coefficient
(`exists_stateCoeff_ne_zero`).

Source: arXiv:1804.04964, Section 3, the passage after `eq:inj_equal_edge`. -/
theorem prod_perVertexScalar_eq_one (A B : Tensor G d)
    (hA : IsVertexInjective A)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hAB : SameState A B)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (hbd : A.bondDim = B.bondDim)
    (c : V → ℂ)
    (hPV : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      A.component v η σ =
        c v * gaugeVertex B Z v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ) :
    (∏ v, c v) = 1 := by
  classical
  have hkey : ∀ σ : V → Fin d,
      stateCoeff A σ = (∏ v, c v) * stateCoeff (applyGauge B Z) σ := by
    intro σ
    have hAcoeff : stateCoeff A σ
        = ∑ η : VirtualConfig A,
            (∏ v, c v) * ∏ v, gaugeVertex B Z v
              (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie.1)) (σ v) := by
      unfold stateCoeff
      refine Finset.sum_congr rfl (fun η _ => ?_)
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      exact hPV v (fun ie => η ie.1) (σ v)
    rw [hAcoeff, ← Finset.mul_sum]
    have hsum : (∑ η : VirtualConfig A, ∏ v, gaugeVertex B Z v
            (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie.1)) (σ v))
        = stateCoeff (applyGauge B Z) σ := by
      unfold stateCoeff
      refine Fintype.sum_equiv
        (Equiv.piCongrRight (fun e => finCongr (congr_fun hbd e)))
        (fun η : VirtualConfig A => ∏ v, gaugeVertex B Z v
            (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie.1)) (σ v))
        (fun ηB => ∏ v, (applyGauge B Z).component v (fun ie => ηB ie.1) (σ v))
        (fun η => ?_)
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rfl
    rw [hsum]
  obtain ⟨σ, hσ⟩ := exists_stateCoeff_ne_zero A hA hpos
  have hBσ : stateCoeff (applyGauge B Z) σ = stateCoeff A σ := by
    rw [applyGauge_stateCoeff B Z σ, ← hAB σ]
  have h1 : stateCoeff A σ = (∏ v, c v) * stateCoeff A σ :=
    (hkey σ).trans (by rw [hBσ])
  have h2 : (∏ v, c v) * stateCoeff A σ = 1 * stateCoeff A σ := by
    rw [one_mul]; exact h1.symm
  exact mul_right_cancel₀ hσ h2

omit [Fintype V] [DecidableRel G.Adj] in
/-- On a connected graph with more than one vertex, every vertex has a nonempty
incident-edge set. -/
theorem nonempty_incidentEdge_of_connected [Nontrivial V]
    (hconn : G.Connected) (v : V) : Nonempty (IncidentEdge G v) := by
  obtain ⟨u, hadj⟩ := hconn.preconnected.exists_adj_of_nontrivial v
  rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
  · exact ⟨⟨⟨(v, u), hlt, hadj⟩, Or.inl rfl⟩⟩
  · exact ⟨⟨⟨(u, v), hgt, hadj.symm⟩, Or.inr rfl⟩⟩

/-- Edge gauges obtained from the three-site reductions give one global gauge
family. Source: arXiv:1804.04964, Section 3, from `eq:TN_5_particle_eq` through
`eq:inj_equal_edge`.

**Connectivity hypothesis (faithfulness fix).** Without `G.Connected` the
conclusion is false: on the empty graph the per-vertex scalars produced by the
source reduction cannot be absorbed into edge gauges, because the oriented
incidence product of edge scalars at a vertex has product `1` on each connected
component, while the state equality constrains the per-vertex scalars only on
each component. The refutation is machine-checked in
`TNLean.PEPS.GaugeConsistencyConnectivityCounterexample.gaugeConsistencyStatement_false`
(empty graph on two vertices, `2 · 3 = 6 = 6 · 1` but `6 ≠ 2`). The source's
injective PEPS are implicitly connected (`Papers/1804.04964/paper_normal.tex:1207`,
"the constants $\lambda_v$ can be incorporated into the gauge transformations"),
which is valid only on a single component. Documented in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`.

**Proof status:** Complete and axiom-clean. The edge-blocked route is recorded
in `docs/paper-gaps/peps_injective_ft_section3_route.tex`. Under connectivity the
per-vertex scalars satisfy `∏_v λ_v = 1`, and a spanning-tree construction
produces the absorbing edge scalars. -/
theorem gaugeConsistency (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hconn : G.Connected) :
    ∃ (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
       ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
         B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
           gaugeVertex A X v η σ := by
  classical
  -- Edge gauges `Z` and the post-absorption insertion identity.
  obtain ⟨Z, hPA⟩ := post_absorption_edge_insertion_equality A B hA hB hAB hDim hpos
  have hbd : A.bondDim = (absorbEdgeGauges B Z).bondDim := hPA.bondDim_eq
  by_cases hnt : Nontrivial V
  · -- Multi-vertex connected graph: every vertex has an incident edge.
    have hne : ∀ v : V, Nonempty (IncidentEdge G v) :=
      fun v => nonempty_incidentEdge_of_connected hconn v
    -- A nonzero per-vertex scalar `c_v` with `A_v = c_v · gaugeVertex B Z v`.
    have hpvs : ∀ v : V, ∃ c : ℂ, c ≠ 0 ∧
        ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
          A.component v η σ =
            c * gaugeVertex B Z v
              (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ := by
      intro v
      have := hne v
      exact perVertexScalar A B hA hB hpos Z hPA v
    choose c hcne hcPV using hpvs
    -- The per-vertex scalars multiply to one.
    have hprod : (∏ v, c v) = 1 :=
      prod_perVertexScalar_eq_one A B hA hpos hAB Z hDim c hcPV
    -- The reciprocal vertex units have product one, so the oriented incidence
    -- equation `∏_{ie} s = c_v⁻¹` is solvable on the connected graph.
    set t : V → ℂˣ := fun v => (Units.mk0 (c v) (hcne v))⁻¹ with ht
    have htprod : (∏ v, t v) = 1 := by
      have hmk : (∏ v, (Units.mk0 (c v) (hcne v))) = 1 := by
        apply Units.ext
        rw [Units.val_one, Units.coe_prod]
        simp only [Units.val_mk0]
        exact hprod
      rw [ht]
      simp only
      rw [Finset.prod_inv_distrib, hmk, inv_one]
    obtain ⟨s, hs⟩ := exists_edgeScalars_of_connected hconn t htprod
    -- The global gauge absorbing `Z` and the edge scalars `s`.
    refine ⟨globalGauge A B hDim Z s, ?_⟩
    intro v η σ
    have hcs : ∏ ie : IncidentEdge G v, (edgeScalarUnit (G := G) s v ie : ℂ) = (c v)⁻¹ := by
      have hsv := hs v
      rw [orientedIncidence] at hsv
      have hval : ((∏ ie : IncidentEdge G v, edgeScalarUnit (G := G) s v ie : ℂˣ) : ℂ)
          = (c v)⁻¹ := by
        rw [hsv, ht]
        simp [Units.val_mk0]
      rwa [Units.coe_prod] at hval
    exact perVertex_gauge_identity A B hDim Z s v (c v) (hcne v) hcs
      (fun η σ => hcPV v η σ) η σ
  · -- Single vertex (subsingleton vertex set): no edges, gauge is trivial.
    have hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
    have hEmptyEdge : IsEmpty (Edge G) := by
      constructor
      rintro ⟨⟨a, b⟩, hlt, _⟩
      exact absurd (Subsingleton.elim a b) (ne_of_lt hlt)
    refine ⟨fun e => hEmptyEdge.elim e, ?_⟩
    intro v η σ
    have hgauge : ∀ (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
        gaugeVertex A X v η σ = A.component v η σ := by
      intro X
      rw [gaugeVertex, Finset.sum_eq_single η]
      · rw [Finset.prod_of_isEmpty, one_mul]
      · intro b _ hb; exact absurd (Subsingleton.elim b η) hb
      · intro h; exact absurd (Finset.mem_univ η) h
    rw [hgauge]
    -- At the single vertex the state coefficient is the component, so `SameState`
    -- gives `B_v(cast η) = A_v(η)`.
    have hsingle : ∀ (C : Tensor G d)
        (ζ : (ie : IncidentEdge G v) → Fin (C.bondDim ie.1)) (τ : Fin d),
        stateCoeff C (fun _ => τ) = C.component v ζ τ := by
      intro C ζ τ
      unfold stateCoeff
      rw [Finset.sum_eq_single (fun e => hEmptyEdge.elim e)]
      · rw [Finset.prod_eq_single v]
        · congr 1
          exact Subsingleton.elim _ _
        · intro b _ hb; exact absurd (Subsingleton.elim b v) hb
        · intro h; exact absurd (Finset.mem_univ v) h
      · intro b _ hb; exact absurd (Subsingleton.elim b _) hb
      · intro h; exact absurd (Finset.mem_univ _) h
    have hAv := hsingle A η σ
    have hBv := hsingle B (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ
    rw [← hAv, ← hBv, hAB (fun _ => σ)]

/-! ### Main theorem -/

/-- **Fundamental Theorem for injective PEPS, conditional on bond-dimension
equality** (arXiv:1804.04964, Theorem 2).

If the bond spaces of `A` and `B` are already identified, equality of their PEPS
states and vertex injectivity imply the gauge formula
`B_v = gaugeVertex A X v` for one invertible matrix `X_e` on each edge, under
the explicit assumption that every virtual bond of `A` has positive dimension.
Via the bond-dimension equality this is also the corresponding positivity
assumption for `B`.

**Connectivity hypothesis (faithfulness fix).** The connectivity hypothesis
`G.Connected` is threaded into `gaugeConsistency`, where it is needed: the
conclusion is false on a disconnected graph. See
`TNLean.PEPS.GaugeConsistencyConnectivityCounterexample` and
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`.

**Proof status:** Complete and axiom-clean; proved from the global-gauge
statement `gaugeConsistency`. The added positivity and connectivity hypotheses
relative to the source statement are the documented faithfulness fixes recorded
in `docs/paper-gaps/peps_injective_ft_section3_route.tex` and
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`. -/
theorem fundamentalTheorem_PEPS_of_bondDim (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hconn : G.Connected) :
    GaugeEquiv A B := by
  rcases gaugeConsistency A B hA hB hAB hDim hpos hconn with ⟨X, hX⟩
  exact ⟨hDim, X, hX⟩

/-- A matrix-algebra equivalence between full matrix algebras on `Fin m` and
`Fin n` forces `m = n`, since each algebra has linear dimension equal to the
square of its index size.

Source: standard dimension count; used to discharge the bond-dimension equality
hypothesis of `fundamentalTheorem_PEPS_of_bondDim` (issue #874). -/
theorem bondDim_eq_of_matrixAlgEquiv {m n : ℕ}
    (Φ : Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) : m = n := by
  have hfr : Module.finrank ℂ (Matrix (Fin m) (Fin m) ℂ) =
      Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    LinearEquiv.finrank_eq Φ.toLinearEquiv
  rw [Module.finrank_matrix, Module.finrank_matrix] at hfr
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hfr
  exact Nat.mul_self_inj.mp hfr

/-- **Fundamental Theorem for injective PEPS** (arXiv:1804.04964, Theorem 2).

For PEPS tensors on a finite simple graph, if `A` and `B` are vertex-injective
and have the same state coefficients, then there are invertible edge matrices
`X_e` such that, at every vertex, `B_v` is obtained from `A_v` by the oriented
endpoint action of the matrices `X_e` on the incident virtual legs.

**Positive-bond hypothesis (faithfulness fix).** Without the positivity conditions the
theorem is false: a zero-dimensional edge makes the virtual configuration empty,
so both state coefficients vanish and `SameState` holds vacuously without
relating the two tensors, while the gauge-equivalence conclusion stays a genuine
constraint that fails. The hypotheses (every bond dimension positive) are the
source's standing assumption that injective PEPS have nonzero virtual bond
spaces; the same defect was corrected for the edge-blocked three-site
injectivity (#1366) and the physical-to-virtual recovery (#1370), and is
recorded in `docs/paper-gaps/peps_injective_ft_section3_route.tex`.

**Connectivity hypothesis (faithfulness fix).** Without `G.Connected` the
theorem is also false: on the empty graph on two vertices the products of the
vertex scalars agree, so `SameState` holds, yet no edge gauge can relate the two
tensors. The refutation is machine-checked as
`fundamentalTheoremPEPS_false_without_connectivity` in the module
`TNLean.PEPS.GaugeConsistencyConnectivityCounterexample`.
The source's injective PEPS are implicitly connected
(`Papers/1804.04964/paper_normal.tex:1207`), so the scalar-absorption step is
valid only on a single component. Documented in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`.

**Proof status:** Complete and axiom-clean. The conclusion is the source
gauge-equivalence conclusion, with positive bond dimension made explicit to
exclude the zero-bond vacuous-state case above. The bond-dimension equality is
discharged edgewise from the edge-blocked insertion algebra equivalence (issue
#874), and the edge-centred gauge obligation is supplied by gauge consistency.
The faithfulness fixes are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex` and
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`. -/
theorem fundamentalTheorem_PEPS (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hconn : G.Connected) :
    GaugeEquiv A B := by
  -- Bond-dimension equality follows edgewise from the edge-blocked insertion
  -- algebra isomorphism: blocking around an edge gives two injective three-site
  -- chains generating the same state, and the matched matrix insertions on that
  -- bond form an algebra equivalence between the two full bond matrix algebras.
  -- Such an equivalence forces equal matrix sizes.
  have hDim : A.bondDim = B.bondDim := by
    funext e
    exact bondDim_eq_of_matrixAlgEquiv
      (edgeTransferAlgEquiv A B e
        (hA.edgeBlockedThreeSiteInjective hposA e)
        (hB.edgeBlockedThreeSiteInjective hposB e)
        hAB hposA hposB)
  -- With matching bond dimensions, gauge consistency supplies the global gauges.
  exact fundamentalTheorem_PEPS_of_bondDim A B hA hB hAB hDim hposA hconn


end PEPS
end TNLean
