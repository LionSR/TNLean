import TNLean.PEPS.FundamentalTheorem.OneVertexComparison
import TNLean.PEPS.EdgeGaugeFamily
import TNLean.PEPS.LocalGauge
import TNLean.PEPS.TwoInjectiveComparison
import TNLean.PEPS.VertexComplement.KernelDescent
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

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
theorem linindep_recombine {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}
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
independence is therefore preserved (`linindep_recombine`), and the bond spaces
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
  exact linindep_recombine (B.component v) (hB v) K hKunit

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
    rw [glReindex_coe, glTranspose_coe, ← reindexAlgEquiv_transpose,
      Matrix.transpose_transpose]
  have hZit :
      ((↑(glReindex (congr_fun hDim e) (glTranspose (X e))) :
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)⁻¹)ᵀ =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hDim e))
     (↑(X e)⁻¹ : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
    rw [← Matrix.GeneralLinearGroup.coe_inv, ← map_inv, glReindex_coe,
      glTranspose_inv_coe, ← reindexAlgEquiv_transpose, Matrix.transpose_transpose]
  rw [hZt, hZit, map_mul, map_mul]
  rfl

/-- Edge gauges obtained from the three-site reductions give one global gauge
family. Source: arXiv:1804.04964, Section 3, from `eq:TN_5_particle_eq` through
`eq:inj_equal_edge`.

**Proof status:** The edge-blocked route and remaining insertion-to-gauge
obligations are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
theorem gaugeConsistency (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
       ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
         B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
           gaugeVertex A X v η σ := by
  -- The edge gauges and the post-absorption insertion identity are available.
  -- The complement block is also known to be two-injective under vertex
  -- injectivity and positive bond dimensions. Two mathematical steps remain.
  -- First, one must translate the edge-insertion equality for the absorbed tensor
  -- family into equality of the one-bond insertions for the vertex/complement
  -- two-block split, with the appropriate orientation transpose. Second, the
  -- scalar factors produced by the two-block comparison must be absorbed into
  -- edge scalars, after inverting the absorbed gauges and matching the chosen
  -- edge orientation.
  sorry

/-! ### Main theorem -/

/-- **Fundamental Theorem for injective PEPS, conditional on bond-dimension
equality** (arXiv:1804.04964, Theorem 2).

If the bond spaces of `A` and `B` are already identified, equality of their PEPS
states and vertex injectivity imply the gauge formula
`B_v = gaugeVertex A X v` for one invertible matrix `X_e` on each edge, under
the explicit assumption that every virtual bond of `A` has positive dimension.
Via the bond-dimension equality this is also the corresponding positivity
assumption for `B`.

**Proof status:** This theorem is proved from the conditional global-gauge
statement above. The remaining difference from the source theorem is recorded
in `docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem fundamentalTheorem_PEPS_of_bondDim (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    GaugeEquiv A B := by
  rcases gaugeConsistency A B hA hB hAB hDim hpos with ⟨X, hX⟩
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

**Proof status:** The conclusion is the source gauge-equivalence conclusion, with
positive bond dimension made explicit to exclude the zero-bond vacuous-state
case above. The bond-dimension equality is now discharged edgewise from the
edge-blocked insertion algebra equivalence (issue #874). The remaining
edge-centred gauge obligation is gauge consistency, recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem fundamentalTheorem_PEPS (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
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
  exact fundamentalTheorem_PEPS_of_bondDim A B hA hB hAB hDim hposA

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

**Proof status:** The proof has been reduced to equality of products of
incident edge-gauge entries at each vertex. The remaining step extracts the
local scalar ratios and reconciles them into one vertex-balanced edge-scalar
family; see `docs/paper-gaps/peps_gauge_edge_scalars.tex`. -/
theorem gauge_unique_mod_edge_scalars (A B : Tensor G d)
    (hA : IsVertexInjective A)
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
  -- From `hProd v` at each vertex `v`, extract a nonzero scalar `c_v(ie)` on
  -- each incident edge such that `edgeGaugeAt A X v ie = c_v(ie) • edgeGaugeAt A Y v ie`
  -- with the oriented product of `c_v(ie)` over incident `ie` at `v` equal to
  -- `1`, then reconcile `c_u` and `c_w` on every shared edge `e = (u,w)` into a
  -- single global family `c : (e : Edge G) → Units ℂ` satisfying
  -- `IsVertexBalanced c`. This is the local scalar-ratio argument of
  -- arXiv:1804.04964 Section 3; it is independent of the virtual-insertion and
  -- blocking lemmas used for local gauge existence.
  -- The current status is recorded in
  -- `docs/paper-gaps/peps_gauge_edge_scalars.tex`.
  sorry

end PEPS
end TNLean
