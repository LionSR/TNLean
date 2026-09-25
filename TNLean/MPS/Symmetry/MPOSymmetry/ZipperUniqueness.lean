/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.NormalCommutant
import TNLean.MPS.MPDO.ActionTensor

/-!
# Uniqueness of zipper fusion and action tensors up to the multiplicity gauge

Let `B` be a tensor whose one-site matrices decompose exactly over copies of normal blocks,
$$B^i = \sum_{c}\sum_{\mu=1}^{N_c} W_{c,\mu}\, C_c^i\, V_{c,\mu},
\qquad V_{c,\mu}W_{c',\nu} = \delta_{cc'}\delta_{\mu\nu}\,\mathbb 1,$$
with compressions `V` on the left and embeddings `W` on the right.  This is the zipper
condition of Bultinck et al. (arXiv:1511.08090, equation `inversegaugeone`, lines 181--191):
the canonical form of the product has no nonzero blocks above the diagonal, so the remainder
of the compression vanishes.  For the stacked product $T_aT_b$ of two tensors of a fusion
algebra the pairs $(V_{c,\mu},W_{c,\mu})$ are the fusion tensors, and for the tensor
$T_a\cdot A_x$ of an operator acting on a state they are the action tensors.

If $(\widetilde V,\widetilde W)$ is a second such decomposition over the same blocks and
multiplicities, then $\widetilde V_{c,\mu}W_{e,\nu}$ intertwines the letters of $C_c$ and
$C_e$.  For normal blocks such an intertwiner is a scalar when $e = c$, and zero when $C_c$ and
$C_e$ are not related by a gauge transformation.  The scalars form, for every block, an
invertible matrix $Y_c$, and the two decompositions differ exactly by
$\bigoplus_c Y_c$: no dressing by long words is needed.  This is the converse direction of the
gauge freedom of arXiv:1511.08090, lines 164--166, argued at lines 191--200, and the gauge
freedom of fusion and action tensors of arXiv:2203.12563, lines 415--424 and 595--602.

The family `c ↦ Y_c` is, for one pair of labels `(a, b)`, the component of the fusion gauge of
the complete-zipper family, planned in #7985 (arXiv:1511.08090, lines 164--166).  The complete zipper fusion families carry isometric fusion tensors and
their own bookkeeping of all pairs, so the comparison there is not made here.

## References

* N. Bultinck, M. Marien, D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete,
  *Anyons and matrix product operator algebras*, arXiv:1511.08090, `AnyonsPEPS.tex`,
  lines 155--200.
* J. Garre-Rubio, L. Lootens, A. Molnár, *Classifying phases protected by matrix product
  operator symmetries using matrix product states*, arXiv:2203.12563, `REsubmission.tex`,
  lines 415--424, 459--490 and 595--602.

## Main definitions

* `MPSTensor.IsGaugeRelated`: two tensors, of possibly different bond dimensions, related by
  an invertible rectangular gauge.
* `MPSTensor.ZipperDecomposition`: an exact decomposition of the letters of a tensor over
  copies of blocks, with biorthogonal compressions and embeddings.
* `MPSTensor.ZipperDecomposition.multiplicityGauge`: the scalar matrix
  $(Y_c)_{\mu\nu}$ with $\widetilde V_{c,\mu}W_{c,\nu} = (Y_c)_{\mu\nu}\,\mathbb 1$.

## Main statements

* `MPSTensor.eq_zero_or_isGaugeRelated_of_intertwines`: the intertwiner lemma for normal
  tensors.
* `MPSTensor.ZipperDecomposition.V_mul_W_eq_multiplicityGauge_smul`,
  `MPSTensor.ZipperDecomposition.V_mul_W_eq_zero_of_not_isGaugeRelated`: the cross products
  of two decompositions are scalar within a block and zero across blocks.
* `MPSTensor.ZipperDecomposition.multiplicityGauge_mul_multiplicityGauge`: the matrices of the
  two directions are mutually inverse.
* `MPSTensor.ZipperDecomposition.exists_unique_multiplicityGauge`: the two decompositions
  differ by a unique element of $\prod_c \mathrm{GL}_{N_c}(\mathbb C)$.
* `MPOTensor.exists_unique_zipperFusionGauge`,
  `MPOTensor.exists_unique_zipperActionGauge`: the fusion-tensor and action-tensor readings.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### The intertwiner lemma for normal tensors -/

/-- Two tensors of possibly different bond dimensions are **gauge related** when an invertible
rectangular matrix `X` intertwines their letters, `A i * X = X * A' i`, so that
`A' i = X⁻¹ * A i * X`.  For equal bond dimensions this is gauge equivalence. -/
def IsGaugeRelated {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (A' : MPSTensor d D₂) : Prop :=
  ∃ (X : Matrix (Fin D₁) (Fin D₂) ℂ) (Y : Matrix (Fin D₂) (Fin D₁) ℂ),
    X * Y = 1 ∧ Y * X = 1 ∧ ∀ i, A i * X = X * A' i

/-- A rectangular matrix that annihilates `M *ᵥ v` for every matrix `M` and a nonzero vector
`v` is zero. -/
private theorem eq_zero_of_forall_mulVec_mulVec {D₁ D₂ : ℕ} {X : Matrix (Fin D₁) (Fin D₂) ℂ}
    {v : Fin D₂ → ℂ} (hv : v ≠ 0)
    (h : ∀ M : Matrix (Fin D₂) (Fin D₂) ℂ, X *ᵥ (M *ᵥ v) = 0) : X = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
  have hM : Matrix.vecMulVec u (Pi.single j (v j)⁻¹) *ᵥ v = u := by
    rw [Matrix.vecMulVec_mulVec, single_dotProduct, inv_mul_cancel₀ hj, MulOpposite.op_one,
      one_smul]
  simpa [hM] using h (Matrix.vecMulVec u (Pi.single j (v j)⁻¹))

/-- **The intertwiner lemma for normal tensors.** If `A` and `A'` are normal and
`A i * X = X * A' i` for every letter, then `X = 0` or `X` is invertible, so that the two
tensors are gauge related.

The kernel of `X` is invariant under the words of `A'`, whose span at a block-injective length
is the full matrix algebra, so a nonzero kernel vector forces `X = 0`; symmetrically for the
left kernel and the words of `A`.  This is the step "since the $B^{ik}_c$ are injective their
commutant consists of multiples of the identity" of arXiv:1511.08090, lines 191--193, in the
form needed for two different blocks. -/
theorem eq_zero_or_isGaugeRelated_of_intertwines {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {A' : MPSTensor d D₂} (hA : Kraus.IsNormal A) (hA' : Kraus.IsNormal A')
    {X : Matrix (Fin D₁) (Fin D₂) ℂ} (hX : ∀ i, A i * X = X * A' i) :
    X = 0 ∨ IsGaugeRelated A A' := by
  classical
  by_cases hX0 : X = 0
  · exact Or.inl hX0
  right
  have hword := Kraus.evalWord_intertwine A A' X hX
  -- The kernel of `X` is trivial.
  have hinj : Function.Injective (Matrix.toLin' X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    obtain ⟨N, -, hN⟩ := hA'
    let f : Matrix (Fin D₂) (Fin D₂) ℂ →ₗ[ℂ] (Fin D₁ → ℂ) :=
      { toFun := fun M => X *ᵥ (M *ᵥ v)
        map_add' := fun M M' => by simp [Matrix.add_mulVec, Matrix.mulVec_add]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec, Matrix.mulVec_smul] }
    have hle : Kraus.wordSpan A' N ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 (Set.range_subset_iff.2 fun σ => ?_)
      change X *ᵥ (Kraus.evalWord A' (List.ofFn σ) *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, ← hword, ← Matrix.mulVec_mulVec]
      simp only [Matrix.toLin'_apply] at hv
      rw [hv, Matrix.mulVec_zero]
    rw [hN] at hle
    exact hX0 (eq_zero_of_forall_mulVec_mulVec hv0 fun M => hle Submodule.mem_top)
  -- The left kernel of `X` is trivial.
  have hinjT : Function.Injective (Matrix.toLin' Xᵀ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    obtain ⟨N, -, hN⟩ := hA
    let f : Matrix (Fin D₁) (Fin D₁) ℂ →ₗ[ℂ] (Fin D₂ → ℂ) :=
      { toFun := fun M => Xᵀ *ᵥ (Mᵀ *ᵥ v)
        map_add' := fun M M' => by
          simp [Matrix.transpose_add, Matrix.add_mulVec, Matrix.mulVec_add]
        map_smul' := fun c M => by
          simp [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul] }
    have hle : Kraus.wordSpan A N ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 (Set.range_subset_iff.2 fun σ => ?_)
      change Xᵀ *ᵥ ((Kraus.evalWord A (List.ofFn σ))ᵀ *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hword, Matrix.transpose_mul,
        ← Matrix.mulVec_mulVec]
      simp only [Matrix.toLin'_apply] at hv
      rw [hv, Matrix.mulVec_zero]
    rw [hN] at hle
    have hXT : Xᵀ = 0 := eq_zero_of_forall_mulVec_mulVec hv0 fun M => by
      have h := LinearMap.mem_ker.1 (hle (Submodule.mem_top (x := Mᵀ)))
      change Xᵀ *ᵥ (Mᵀᵀ *ᵥ v) = 0 at h
      simpa using h
    exact hX0 (by simpa using congrArg Matrix.transpose hXT)
  -- Equal dimensions, hence `X` is bijective.
  have hle₁ := LinearMap.finrank_le_finrank_of_injective hinj
  have hle₂ := LinearMap.finrank_le_finrank_of_injective hinjT
  have hdim : Module.finrank ℂ (Fin D₂ → ℂ) = Module.finrank ℂ (Fin D₁ → ℂ) := by
    simp only [Module.finrank_fin_fun] at hle₁ hle₂ ⊢
    omega
  let e : (Fin D₂ → ℂ) ≃ₗ[ℂ] (Fin D₁ → ℂ) := LinearEquiv.ofBijective (Matrix.toLin' X)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  refine ⟨X, LinearMap.toMatrix' (e.symm : (Fin D₁ → ℂ) →ₗ[ℂ] (Fin D₂ → ℂ)), ?_, ?_, hX⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe]
    exact e.apply_symm_apply u
  · refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe]
    exact e.symm_apply_apply u

/-- A normal tensor of positive bond dimension has a nonzero letter. -/
theorem exists_ne_zero_of_isNormal {D : ℕ} [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) : ∃ i, A i ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨N, hN0, hN⟩ := hA
  have hle : Kraus.wordSpan A N ≤ ⊥ := by
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun σ => ?_)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN0.ne'
    simp [List.ofFn_succ, h]
  rw [hN] at hle
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
    (Submodule.mem_bot ℂ).1 (hle (Submodule.mem_top (x := 1)))
  exact one_ne_zero h1

/-! ### Zipper decompositions -/

variable {DB : ℕ} {ι : Type*} [Fintype ι] {D N : ι → ℕ}

/-- A **zipper decomposition** of a tensor `B` over blocks `C c` with multiplicities `N c`:
compressions `V c μ` and embeddings `W c μ` with `V c μ * W c' ν = δ_{(c,μ),(c',ν)} 1`, such
that every letter decomposes exactly,
$B^i = \sum_c\sum_\mu W_{c,\mu}\,C_c^i\,V_{c,\mu}$, with no remainder.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, the biorthogonality relation at line 161 and the
zipper decomposition, equation `inversegaugeone`, lines 181--191 (the absence of nonzero
blocks above the diagonal).  For action tensors, arXiv:2203.12563, lines 459--490 and 595--602.
The embeddings need not span the bond space of `B`: zero diagonal blocks are allowed, as in
arXiv:1511.08090, lines 179--180. -/
structure ZipperDecomposition (B : MPSTensor d DB) (C : ∀ c, MPSTensor d (D c))
    (N : ι → ℕ) where
  /-- The compressions `V c μ`. -/
  V : ∀ c, Fin (N c) → Matrix (Fin (D c)) (Fin DB) ℂ
  /-- The embeddings `W c μ`. -/
  W : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (D c)) ℂ
  /-- Each compression is a left inverse of its embedding. -/
  V_mul_W_self : ∀ c μ, V c μ * W c μ = 1
  /-- Compressions and embeddings of different slots are orthogonal. -/
  V_mul_W_of_ne : ∀ c μ c' ν,
    (⟨c, μ⟩ : (c : ι) × Fin (N c)) ≠ ⟨c', ν⟩ → V c μ * W c' ν = 0
  /-- The zipper decomposition of every letter, with vanishing remainder. -/
  decomp : ∀ i, B i = ∑ c, ∑ μ, W c μ * C c i * V c μ

namespace ZipperDecomposition

variable {B : MPSTensor d DB} {C : ∀ c, MPSTensor d (D c)}

/-- Sandwiching a sum over the slots of a decomposition between a matrix `L` on the left
whose products with the embeddings vanish off one slot picks out that slot. -/
private theorem V_mul_sum (P : ZipperDecomposition B C N) {m : ℕ}
    (F : ∀ c, Fin (N c) → Matrix (Fin (D c)) (Fin m) ℂ) (c : ι) (μ : Fin (N c)) :
    P.V c μ * ∑ c', ∑ ν, P.W c' ν * F c' ν = F c μ := by
  rw [Matrix.mul_sum, Fintype.sum_eq_single c, Matrix.mul_sum, Fintype.sum_eq_single μ]
  · rw [← Matrix.mul_assoc, P.V_mul_W_self, Matrix.one_mul]
  · intro ν hν
    rw [← Matrix.mul_assoc, P.V_mul_W_of_ne c μ c ν (by simpa using hν.symm), Matrix.zero_mul]
  · intro c' hc'
    rw [Matrix.mul_sum]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [← Matrix.mul_assoc, P.V_mul_W_of_ne c μ c' ν (fun h => hc' (congrArg Sigma.fst h).symm),
      Matrix.zero_mul]

/-- The mirror image of `V_mul_sum`. -/
private theorem sum_mul_W (P : ZipperDecomposition B C N) {m : ℕ}
    (F : ∀ c, Fin (N c) → Matrix (Fin m) (Fin (D c)) ℂ) (c : ι) (μ : Fin (N c)) :
    (∑ c', ∑ ν, F c' ν * P.V c' ν) * P.W c μ = F c μ := by
  rw [Matrix.sum_mul, Fintype.sum_eq_single c, Matrix.sum_mul, Fintype.sum_eq_single μ]
  · rw [Matrix.mul_assoc, P.V_mul_W_self, Matrix.mul_one]
  · intro ν hν
    rw [Matrix.mul_assoc, P.V_mul_W_of_ne c ν c μ (by simpa using hν), Matrix.mul_zero]
  · intro c' hc'
    rw [Matrix.sum_mul]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Matrix.mul_assoc, P.V_mul_W_of_ne c' ν c μ (fun h => hc' (congrArg Sigma.fst h)),
      Matrix.mul_zero]

/-- **The zipper condition, compression side**: `V c μ * B i = C c i * V c μ`.

Source: arXiv:1511.08090, equation `zippercondition2`, lines 194--200. -/
theorem V_mul (P : ZipperDecomposition B C N) (c : ι) (μ : Fin (N c)) (i : Fin d) :
    P.V c μ * B i = C c i * P.V c μ := by
  rw [P.decomp i]
  simpa only [Matrix.mul_assoc] using P.V_mul_sum (fun c' ν => C c' i * P.V c' ν) c μ

/-- **The zipper condition, embedding side**: `B i * W c μ = W c μ * C c i`.

Source: arXiv:1511.08090, equation `zippercondition2`, lines 194--200. -/
theorem mul_W (P : ZipperDecomposition B C N) (c : ι) (μ : Fin (N c)) (i : Fin d) :
    B i * P.W c μ = P.W c μ * C c i := by
  rw [P.decomp i]
  exact P.sum_mul_W (fun c' ν => P.W c' ν * C c' i) c μ

/-- The cross product `Q.V c μ * P.W e ν` of two zipper decompositions intertwines the letters
of the blocks `C c` and `C e`. -/
theorem intertwines (P Q : ZipperDecomposition B C N) (c e : ι) (μ : Fin (N c))
    (ν : Fin (N e)) (i : Fin d) :
    C c i * (Q.V c μ * P.W e ν) = (Q.V c μ * P.W e ν) * C e i := by
  rw [← Matrix.mul_assoc, ← Q.V_mul, Matrix.mul_assoc, P.mul_W, Matrix.mul_assoc]

/-- Across blocks that are not gauge related, the cross products of two zipper
decompositions vanish.

Source: arXiv:1511.08090, lines 191--193. -/
theorem V_mul_W_eq_zero_of_not_isGaugeRelated (P Q : ZipperDecomposition B C N) {c e : ι}
    (hc : Kraus.IsNormal (C c)) (he : Kraus.IsNormal (C e))
    (hce : ¬ IsGaugeRelated (C c) (C e)) (μ : Fin (N c)) (ν : Fin (N e)) :
    Q.V c μ * P.W e ν = 0 :=
  (eq_zero_or_isGaugeRelated_of_intertwines hc he (P.intertwines Q c e μ ν)).resolve_right hce

/-- The **multiplicity gauge** of two zipper decompositions: the scalar
$(Y_c)_{\mu\nu} = \operatorname{tr}(\widetilde V_{c,\mu} W_{c,\nu}) / D_c$, where
`P = (V, W)` and `Q = (V', W')`. -/
noncomputable def multiplicityGauge (P Q : ZipperDecomposition B C N) (c : ι) :
    Matrix (Fin (N c)) (Fin (N c)) ℂ :=
  fun μ ν => (D c : ℂ)⁻¹ * (Q.V c μ * P.W c ν).trace

/-- **Within a normal block the cross products are scalar**:
$\widetilde V_{c,\mu}W_{c,\nu} = (Y_c)_{\mu\nu}\,\mathbb 1$.

Source: arXiv:1511.08090, lines 191--193 (the commutant of an injective block is scalar). -/
theorem V_mul_W_eq_multiplicityGauge_smul (P Q : ZipperDecomposition B C N) {c : ι}
    (hc : Kraus.IsNormal (C c)) (μ ν : Fin (N c)) :
    Q.V c μ * P.W c ν = P.multiplicityGauge Q c μ ν • 1 := by
  obtain ⟨y, hy⟩ := hc.eq_smul_one_of_commute fun i => (P.intertwines Q c c μ ν i).symm
  rcases Nat.eq_zero_or_pos (D c) with hD | hD
  · ext a
    exact absurd a.2 (by omega)
  rw [hy, multiplicityGauge, hy, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul, ← mul_assoc, mul_comm _ y, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hD.ne'),
    mul_one]

/-- **The two multiplicity gauges are mutually inverse.** For normal blocks of positive bond
dimension that are pairwise not gauge related, `multiplicityGauge P Q c` and
`multiplicityGauge Q P c` are inverse matrices.

Compressing a letter of `B` with `Q` on both sides gives `δ • C c i` by the decomposition `Q`,
and $\sum_\nu (Y_c)_{\mu\nu}(Y'_c)_{\nu\kappa}\,C_c^i$ by the decomposition `P`. -/
theorem multiplicityGauge_mul_multiplicityGauge (P Q : ZipperDecomposition B C N)
    (hC : ∀ c, Kraus.IsNormal (C c)) (hD : ∀ c, 0 < D c)
    (hsep : ∀ c e, c ≠ e → ¬ IsGaugeRelated (C c) (C e)) (c : ι) :
    P.multiplicityGauge Q c * Q.multiplicityGauge P c = 1 := by
  classical
  have : NeZero (D c) := ⟨(hD c).ne'⟩
  obtain ⟨i, hi⟩ := exists_ne_zero_of_isNormal (hC c)
  ext μ κ
  apply smul_left_injective ℂ hi
  have key : Q.V c μ * B i * Q.W c κ =
      (P.multiplicityGauge Q c * Q.multiplicityGauge P c) μ κ • C c i := by
    rw [P.decomp i, Matrix.mul_sum, Matrix.sum_mul, Fintype.sum_eq_single c]
    · rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.V_mul_W_eq_multiplicityGauge_smul Q (hC c),
        Matrix.mul_assoc, Q.V_mul_W_eq_multiplicityGauge_smul P (hC c), Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]
    · intro e he
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_eq_zero fun ν _ => ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
        P.V_mul_W_eq_zero_of_not_isGaugeRelated Q (hC c) (hC e) (hsep c e (Ne.symm he)),
        Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
  have key' : Q.V c μ * B i * Q.W c κ = (1 : Matrix (Fin (N c)) (Fin (N c)) ℂ) μ κ • C c i := by
    rw [Q.V_mul, Matrix.mul_assoc]
    by_cases hμκ : μ = κ
    · subst hμκ
      rw [Q.V_mul_W_self, Matrix.mul_one, Matrix.one_apply_eq, one_smul]
    · rw [Q.V_mul_W_of_ne c μ c κ (by simpa using hμκ), Matrix.mul_zero,
        Matrix.one_apply_ne hμκ, zero_smul]
  exact key.symm.trans key'

/-- The multiplicity gauge as an invertible matrix on each multiplicity space. -/
noncomputable def multiplicityGaugeUnit (P Q : ZipperDecomposition B C N)
    (hC : ∀ c, Kraus.IsNormal (C c)) (hD : ∀ c, 0 < D c)
    (hsep : ∀ c e, c ≠ e → ¬ IsGaugeRelated (C c) (C e)) (c : ι) :
    GL (Fin (N c)) ℂ where
  val := P.multiplicityGauge Q c
  inv := Q.multiplicityGauge P c
  val_inv := P.multiplicityGauge_mul_multiplicityGauge Q hC hD hsep c
  inv_val := Q.multiplicityGauge_mul_multiplicityGauge P hC hD hsep c

/-- The compressions of the second decomposition are the multiplicity-gauge combinations of
those of the first, on the support of `B`: `Q.V c μ * B i = ∑ ν, Y μ ν • (P.V c ν * B i)`. -/
theorem V_mul_eq_sum (P Q : ZipperDecomposition B C N) (hC : ∀ c, Kraus.IsNormal (C c))
    (hsep : ∀ c e, c ≠ e → ¬ IsGaugeRelated (C c) (C e)) (c : ι) (μ : Fin (N c)) (i : Fin d) :
    Q.V c μ * B i = ∑ ν, P.multiplicityGauge Q c μ ν • (P.V c ν * B i) := by
  rw [P.decomp i, Matrix.mul_sum, Fintype.sum_eq_single c]
  · rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.V_mul_W_eq_multiplicityGauge_smul Q (hC c),
      ← P.decomp i, P.V_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  · intro e he
    rw [Matrix.mul_sum]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      P.V_mul_W_eq_zero_of_not_isGaugeRelated Q (hC c) (hC e) (hsep c e (Ne.symm he)),
      Matrix.zero_mul, Matrix.zero_mul]

/-- The embeddings of the second decomposition are the inverse-gauge combinations of those of
the first, on the support of `B`: `B i * Q.W c κ = ∑ ν, Y' ν κ • (B i * P.W c ν)`. -/
theorem mul_W_eq_sum (P Q : ZipperDecomposition B C N) (hC : ∀ c, Kraus.IsNormal (C c))
    (hsep : ∀ c e, c ≠ e → ¬ IsGaugeRelated (C c) (C e)) (c : ι) (κ : Fin (N c)) (i : Fin d) :
    B i * Q.W c κ = ∑ ν, Q.multiplicityGauge P c ν κ • (B i * P.W c ν) := by
  rw [P.decomp i, Matrix.sum_mul, Fintype.sum_eq_single c]
  · rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Matrix.mul_assoc, Q.V_mul_W_eq_multiplicityGauge_smul P (hC c), ← P.decomp i, P.mul_W,
      Matrix.mul_smul, Matrix.mul_one]
  · intro e he
    rw [Matrix.sum_mul]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Matrix.mul_assoc,
      Q.V_mul_W_eq_zero_of_not_isGaugeRelated P (hC e) (hC c) (hsep e c he), Matrix.mul_zero]

/-- A matrix that expresses the compressions of `Q` through those of `P` on the support of `B`
is the multiplicity gauge. -/
theorem eq_multiplicityGauge_of_V_mul_eq_sum (P Q : ZipperDecomposition B C N)
    (hC : ∀ c, Kraus.IsNormal (C c)) (hD : ∀ c, 0 < D c) {c : ι}
    (Z : Matrix (Fin (N c)) (Fin (N c)) ℂ)
    (hZ : ∀ μ i, Q.V c μ * B i = ∑ ν, Z μ ν • (P.V c ν * B i)) :
    Z = P.multiplicityGauge Q c := by
  have : NeZero (D c) := ⟨(hD c).ne'⟩
  obtain ⟨i, hi⟩ := exists_ne_zero_of_isNormal (hC c)
  have hsum : ∀ (Z' : Matrix (Fin (N c)) (Fin (N c)) ℂ) μ κ,
      (∑ ν, Z' μ ν • (P.V c ν * B i)) * P.W c κ = Z' μ κ • C c i := by
    intro Z' μ κ
    rw [Matrix.sum_mul, Finset.sum_eq_single κ]
    · rw [Matrix.smul_mul, Matrix.mul_assoc, P.mul_W, ← Matrix.mul_assoc, P.V_mul_W_self,
        Matrix.one_mul]
    · intro ν _ hν
      rw [Matrix.smul_mul, Matrix.mul_assoc, P.mul_W, ← Matrix.mul_assoc,
        P.V_mul_W_of_ne c ν c κ (by simpa using hν), Matrix.zero_mul, smul_zero]
    · simp
  ext μ κ
  apply smul_left_injective ℂ hi
  change Z μ κ • C c i = P.multiplicityGauge Q c μ κ • C c i
  rw [← hsum Z, ← hZ, Matrix.mul_assoc, P.mul_W, ← Matrix.mul_assoc,
    P.V_mul_W_eq_multiplicityGauge_smul Q (hC c), Matrix.smul_mul, Matrix.one_mul]

/-- **Uniqueness of zipper decompositions up to the multiplicity gauge.** Let the blocks be
normal, of positive bond dimension, and pairwise not gauge related.  Two zipper decompositions
`P = (V, W)` and `Q = (V', W')` of `B` over the same blocks and multiplicities differ by a unique
family `Y c ∈ GL (N c)`:
$\widetilde V_{c,\mu}B^i = \sum_\nu (Y_c)_{\mu\nu}V_{c,\nu}B^i$ and
$B^i\widetilde W_{c,\kappa} = \sum_\nu B^iW_{c,\nu}(Y_c^{-1})_{\nu\kappa}$ for every letter.
The identities hold on the support of `B`, the range of its letters, since the embeddings need
not span the bond space (arXiv:1511.08090, lines 179--180).  No dressing by words is needed.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 164--166 (the gauge transformation `Y`) and
lines 181--200 (its uniqueness under the zipper condition); arXiv:2203.12563, lines 415--424. -/
theorem exists_unique_multiplicityGauge (P Q : ZipperDecomposition B C N)
    (hC : ∀ c, Kraus.IsNormal (C c)) (hD : ∀ c, 0 < D c)
    (hsep : ∀ c e, c ≠ e → ¬ IsGaugeRelated (C c) (C e)) :
    ∃! Y : ∀ c, GL (Fin (N c)) ℂ,
      (∀ c μ i, Q.V c μ * B i =
        ∑ ν, (↑(Y c) : Matrix (Fin (N c)) (Fin (N c)) ℂ) μ ν • (P.V c ν * B i)) ∧
      (∀ c κ i, B i * Q.W c κ =
        ∑ ν, (↑(Y c)⁻¹ : Matrix (Fin (N c)) (Fin (N c)) ℂ) ν κ • (B i * P.W c ν)) :=
  ⟨P.multiplicityGaugeUnit Q hC hD hsep,
    ⟨fun c μ i => P.V_mul_eq_sum Q hC hsep c μ i, fun c κ i => P.mul_W_eq_sum Q hC hsep c κ i⟩,
    fun _ hY => funext fun c => Units.ext
      (P.eq_multiplicityGauge_of_V_mul_eq_sum Q hC hD _ fun μ i => hY.1 c μ i)⟩

end ZipperDecomposition

end MPSTensor

namespace MPOTensor

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- **Uniqueness of zipper fusion tensors up to the multiplicity gauge.** Let the blocks
`T c` of a fusion algebra be normal, of positive bond dimension, and pairwise not gauge
related, and let `P` and `Q` be two families of fusion tensors for the stacked product
$T_aT_b$ with vanishing remainder,
$(T_aT_b)^{ij} = \sum_{c,\mu} W_{ab}^{c,\mu}T_c^{ij}V_{ab}^{c,\mu}$.  Then the two families
differ by a unique $Y_{ab}^c \in \mathrm{GL}_{N_{ab}^c}(\mathbb C)$ for each `c`, on the
support of the product.  The family `c ↦ Y c` is the `(a, b)` component of a fusion gauge.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 164--166 and 181--200 (fusion tensors under
the zipper condition, equation `inversegaugeone`); arXiv:2203.12563, lines 415--424. -/
theorem exists_unique_zipperFusionGauge {Da Db : ℕ} {χ Nab : ι → ℕ} {Ta : MPOTensor d Da}
    {Tb : MPOTensor d Db} {T : ∀ c, MPOTensor d (χ c)}
    (P Q : MPSTensor.ZipperDecomposition (mulTensor Ta Tb).toMPSTensor
      (fun c => (T c).toMPSTensor) Nab)
    (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hχ : ∀ c, 0 < χ c)
    (hsep : ∀ c e, c ≠ e → ¬ MPSTensor.IsGaugeRelated (T c).toMPSTensor (T e).toMPSTensor) :
    ∃! Y : ∀ c, GL (Fin (Nab c)) ℂ,
      (∀ c μ i, Q.V c μ * (mulTensor Ta Tb).toMPSTensor i =
        ∑ ν, (↑(Y c) : Matrix (Fin (Nab c)) (Fin (Nab c)) ℂ) μ ν •
          (P.V c ν * (mulTensor Ta Tb).toMPSTensor i)) ∧
      (∀ c κ i, (mulTensor Ta Tb).toMPSTensor i * Q.W c κ =
        ∑ ν, (↑(Y c)⁻¹ : Matrix (Fin (Nab c)) (Fin (Nab c)) ℂ) ν κ •
          ((mulTensor Ta Tb).toMPSTensor i * P.W c ν)) :=
  P.exists_unique_multiplicityGauge Q hT hχ hsep

/-- **Uniqueness of zipper action tensors up to the multiplicity gauge.** Let the blocks
`A y` be normal, of positive bond dimension, and pairwise not gauge related, and let `P` and
`Q` be two families of action tensors for the tensor $T_a\cdot A_x$ with vanishing remainder,
$(T_a\cdot A_x)^i = \sum_{y,k} W_{ax}^{y,k}A_y^iV_{ax}^{y,k}$.  Then the two families differ by
a unique $X_{ax}^y \in \mathrm{GL}_{M_{a,x}^y}(\mathbb C)$ for each `y`, on the support of
$T_a\cdot A_x$.

Source: arXiv:2203.12563, lines 459--490 (action tensors) and 595--602 (their gauge
transformations); the zipper condition is arXiv:1511.08090, lines 181--191. -/
theorem exists_unique_zipperActionGauge {Da Dx : ℕ} {Dy M : ι → ℕ} {Ta : MPOTensor d Da}
    {Ax : MPSTensor d Dx} {A : ∀ y, MPSTensor d (Dy y)}
    (P Q : MPSTensor.ZipperDecomposition (actTensor Ta Ax) A M)
    (hA : ∀ y, Kraus.IsNormal (A y)) (hDy : ∀ y, 0 < Dy y)
    (hsep : ∀ y z, y ≠ z → ¬ MPSTensor.IsGaugeRelated (A y) (A z)) :
    ∃! X : ∀ y, GL (Fin (M y)) ℂ,
      (∀ y k i, Q.V y k * actTensor Ta Ax i =
        ∑ l, (↑(X y) : Matrix (Fin (M y)) (Fin (M y)) ℂ) k l • (P.V y l * actTensor Ta Ax i)) ∧
      (∀ y k i, actTensor Ta Ax i * Q.W y k =
        ∑ l, (↑(X y)⁻¹ : Matrix (Fin (M y)) (Fin (M y)) ℂ) l k •
          (actTensor Ta Ax i * P.W y l)) :=
  P.exists_unique_multiplicityGauge Q hA hDy hsep

end MPOTensor
