/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.OneVertexComparison
import TNLean.PEPS.EdgeGaugeFamily
import TNLean.PEPS.LocalGauge
import TNLean.PEPS.TwoInjectiveComparison
import TNLean.PEPS.VertexComplement.Injective
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
# Local gauge extraction for injective PEPS

This module develops the local gauge extraction, absorbed-tensor injectivity,
and the one-vertex scalar comparison used to construct the global gauge in the
PEPS Fundamental Theorem (arXiv:1804.04964, Section 3, Theorem 2).
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
  · rw [ite_eq_right h, ite_eq_right (fun hall => h (funext hall))]

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
  · simp only [ite_eq_left h]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · simp only [ite_eq_right h]
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

omit [Fintype V] in
/-- `edgeGaugeAtInv` is a left inverse of `edgeGaugeAt`. -/
theorem edgeGaugeAtInv_mul (B : Tensor G d) (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeGaugeAtInv (G := G) B Z v ie * edgeGaugeAt B Z v ie = 1 := by
  unfold edgeGaugeAt edgeGaugeAtInv
  by_cases h : ie.1.1.1 = v
  · simp only [ite_eq_left h]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  · simp only [ite_eq_right h]
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
    funext η σ
    rfl
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
lines 1037--1065. Assuming the separately established bond-dimension equality
\(D_A=D_B\), the edge gauges obtained from the three-site comparison can
be absorbed into the second tensor family so that every edge insertion in \(A\)
agrees with the transported edge insertion in the absorbed tensor family.

**Positive-bond hypothesis (faithfulness fix).** The edge gauges come from
the edge-gauge existence result, which blocks the PEPS around each edge into a
three-site injective chain. That step needs every bond dimension positive,
\(\forall e,\ 0 < D_A(e)\), the source's standing assumption that injective PEPS
have nonzero virtual bond spaces. A vertex incident to a zero-dimensional bond
has an empty virtual-configuration family, making linear independence vacuous.
The same defect was corrected for the PEPS fundamental theorem, gauge
consistency, and the edge-blocked three-site injectivity theorem; it is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
theorem post_absorption_edge_insertion_equality (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B) (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ Z, PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z) := by
  classical
  obtain ⟨X, hX⟩ := exists_edgeGaugeFamily A B hA hB hAB hDim hpos
  choose Φ hΦcoeff hΦconj using hX
  let Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ :=
    fun e => glReindex (congr_fun hDim e) (glTranspose (X e))
  refine ⟨Z, hDim, ?_⟩
  intro e σ M
  simp only [absorbEdgeGauges]
  rw [hΦcoeff e σ M, hΦconj e M]
  have hZt :
      (↑(Z e) : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)ᵀ =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e))
          (↑(X e) : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
    simp only [Z]
    rw [glReindex_coe, glTranspose_coe]
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex,
      Matrix.transpose_transpose]
  have hZit :
      ((↑(Z e) : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)⁻¹)ᵀ =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e))
          (↑(X e)⁻¹ : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
    simp only [Z]
    rw [← Matrix.GeneralLinearGroup.coe_inv, ← map_inv, glReindex_coe,
      glTranspose_inv_coe]
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex,
      Matrix.transpose_transpose]
  have hMatrix :
      (↑(Z e) : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)ᵀ *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e)) M *
          ((↑(Z e) : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)⁻¹)ᵀ =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e))
          ((↑(X e) : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) * M *
            (↑(X e)⁻¹ : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)) := by
    rw [hZt, hZit, map_mul, map_mul]
  rw [← hMatrix]
  exact (edgeInsertedCoeff_applyGauge B Z e σ
    (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e)) M)).symm

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

end PEPS
end TNLean
