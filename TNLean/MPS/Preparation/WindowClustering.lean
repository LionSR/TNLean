/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ObservableTransferBound
import TNLean.MPS.Preparation.WindowOperatorSupport

/-!
# Clustering of block observables in a normal matrix product state

For a normal tensor in the gauge `∑ (A^i)† A^i = 1`, `E_A(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1`, the
connected correlation in the normalized vector `φ_N` of two operators `X`, `Y` of norm at
most `M` on windows of `w` consecutive sites, separated by `g` sites on one side and `h'`
sites on the other side of the ring, is at most `C (r^g + r^{h'})`, where `r < 1` is any
rate above `|λ₂|` and `C` depends on `A`, `r` and `M` but not on `w`, `g`, `h'` or `N`.

This is the second estimate of the chapter's proof of `thm:ldp_depth_lower_bound` (the
chapter's version of arXiv:2307.01696, Theorem 1): "the connected correlation in `φ_N` of
two operators of norm at most `4` on intervals separated by `g` and `g'` sites around the
ring is at most `C(r^g + r^{g'})`, with `C` and `r < 1` depending only on `A`". The
source's proof of Theorem 1 uses instead the approximation of `φ_N` by a product state
(arXiv:2307.01696, Lemma 1); see the chapter comment after `thm:ldp_depth_lower_bound`.

## Main results

* `inner_mpvState_chainWindowOperator_offset`,
  `inner_mpvState_chainWindowOperator_mul_offset`: the trace formulas for windows at an
  arbitrary offset, which make `φ_N` translation invariant on windows.
* `exists_norm_mpvExpectation_mul_sub_mul_le`: the clustering estimate.
-/

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Operator ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-! ### Trace formulas at an arbitrary offset -/

/-- The inserted transfer map of two windows, `E_{X_1 Y_{L+m+1}} = E_X E_A^m E_Y E_A^n`
on a chain of `L + m + L + n` sites (arXiv:2307.01696, Supplemental Material, proof of
Lemma 2, trace expansion of the correlator). -/
theorem physicalObservableTransfer_chainWindowOperator_mul (A : MPSTensor d D) {L : ℕ}
    (hL : 0 < L) (m n : ℕ) (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    physicalObservableTransfer A (L + m + L + n)
        (chainWindowOperator (L + m + L + n) 0 X *
          chainWindowOperator (L + m + L + n) (L + m) Y) =
      physicalObservableTransfer A L X * Kraus.transferMap A ^ m *
        physicalObservableTransfer A L Y * Kraus.transferMap A ^ n := by
  rw [chainWindowOperator_zero_eq_appendObservable hL,
    chainWindowOperator_add_eq_appendObservable hL, appendObservable_mul, appendObservable_mul,
    appendObservable_mul, mul_one, mul_one, one_mul, mul_one,
    physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_appendObservable, physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_one, physicalObservableTransfer_one]

/-- **One window at any offset.** On a chain of `a + (L + n)` sites, the expectation of an
operator `X` on the window `a, …, a + L - 1` is `tr(E_X E_A^{n+a})`, independent of the
offset `a`. This is the translation invariance of the vectors `φ_N` of arXiv:2307.01696,
eq. (TI-MPS2), used in the chapter's proof of `thm:ldp_depth_lower_bound`. -/
theorem inner_mpvState_chainWindowOperator_offset (A : MPSTensor d D) {L : ℕ} (hL : 0 < L)
    (a n : ℕ) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ⟪mpvState A (a + (L + n)),
        Matrix.toEuclideanLin (chainWindowOperator (a + (L + n)) a X)
          (mpvState A (a + (L + n)))⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (physicalObservableTransfer A L X * Kraus.transferMap A ^ (n + a)) := by
  rw [chainWindowOperator_add_right (p := a) (q := L + n) (a := a) le_rfl (by omega) (by omega),
    Nat.sub_self, chainWindowOperator_add_left (p := L) (q := n) (a := 0) hL (by omega),
    chainWindowOperator_self hL,
    inner_mpvState_toEuclideanLin, physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_appendObservable, physicalObservableTransfer_one,
    physicalObservableTransfer_one, LinearMap.trace_mul_comm, mul_assoc, ← pow_add]

/-- **Two windows at any offset.** On a chain of `a + (L + m + L + n)` sites, with `X` on
the window starting at `a` and `Y` on the window starting at `a + L + m`,
`⟨φ|X Y|φ⟩ = tr(E_X E_A^m E_Y E_A^{n+a})`. This is the trace expansion of arXiv:2307.01696,
Supplemental Material, proof of Lemma 2, at an arbitrary position on the ring, used in
the chapter's proof of `thm:ldp_depth_lower_bound`. -/
theorem inner_mpvState_chainWindowOperator_mul_offset (A : MPSTensor d D) {L : ℕ}
    (hL : 0 < L) (a m n : ℕ) (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ⟪mpvState A (a + (L + m + L + n)),
        Matrix.toEuclideanLin (chainWindowOperator (a + (L + m + L + n)) a X *
          chainWindowOperator (a + (L + m + L + n)) (a + (L + m)) Y)
          (mpvState A (a + (L + m + L + n)))⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (physicalObservableTransfer A L X * Kraus.transferMap A ^ m *
          physicalObservableTransfer A L Y * Kraus.transferMap A ^ (n + a)) := by
  rw [chainWindowOperator_add_right (p := a) (q := L + m + L + n) (a := a) le_rfl (by omega)
      (by omega), Nat.sub_self,
    chainWindowOperator_add_right (p := a) (q := L + m + L + n) (a := a + (L + m)) (by omega)
      (by omega) (by omega), Nat.add_sub_cancel_left,
    appendObservable_mul, one_mul, inner_mpvState_toEuclideanLin,
    physicalObservableTransfer_appendObservable, physicalObservableTransfer_one,
    physicalObservableTransfer_chainWindowOperator_mul A hL, LinearMap.trace_mul_comm,
    pow_add]
  simp only [mul_assoc]

/-- The squared norm of `φ_N` is `tr E_A^N` (arXiv:2307.01696, Supplemental Material, proof
of Lemma 2, normalization of the correlator). -/
theorem inner_mpvState_self_eq_trace (A : MPSTensor d D) (N : ℕ) :
    ⟪mpvState A N, mpvState A N⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) (Kraus.transferMap A ^ N) := by
  have h := inner_mpvState_toEuclideanLin A N 1
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply] at h
  rwa [physicalObservableTransfer_one] at h

/-! ### Bounds on normalized expectations -/

/-- The normalized expectation of an operator is at most its operator norm. This bounds the
one-point values `e = ⟨𝒪_1⟩_φ` in the chapter's proof of `thm:ldp_depth_lower_bound` (the
chapter's version of arXiv:2307.01696, Supplemental Material, proof of Theorem 1). -/
theorem norm_mpvExpectation_le (A : MPSTensor d D) (N : ℕ)
    (O : Matrix (Cfg d N) (Cfg d N) ℂ) :
    ‖mpvExpectation A N O‖ ≤ ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) O‖ := by
  set u : MPVSpace d N := ((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N
  have hu : ‖u‖ ≤ 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
  have hO : Matrix.toEuclideanLin O u = Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) O u :=
    rfl
  change ‖⟪u, Matrix.toEuclideanLin O u⟫_ℂ‖ ≤ _
  rw [hO]
  calc ‖⟪u, Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) O u⟫_ℂ‖
      ≤ ‖u‖ * (‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) O‖ * ‖u‖) :=
        (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    _ ≤ 1 * (‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) O‖ * 1) := by
        gcongr
    _ = _ := by ring

/-- The operator norm of a product of matrices is at most the product of the norms. -/
theorem _root_.Matrix.norm_toEuclideanCLM_mul_le {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (P * Q)‖ ≤
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) P‖ *
        ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) Q‖ := by
  rw [map_mul]
  exact norm_mul_le _ _

/-! ### Translation invariance -/

/-- The numerator of the expectation of an operator `X` on the window `a, …, a + L - 1` of a
chain of `N` sites is `tr(E_X E_A^{N-L})`, independent of `a` (arXiv:2307.01696, Supplemental
Material, proof of Lemma 2, trace expansion). -/
theorem inner_mpvState_chainWindowOperator_eq_trace (A : MPSTensor d D) {L N a : ℕ}
    (hL : 0 < L) (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ⟪mpvState A N, Matrix.toEuclideanLin (chainWindowOperator N a X) (mpvState A N)⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (physicalObservableTransfer A L X * Kraus.transferMap A ^ (N - L)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = a + (L + n) := ⟨N - a - L, by omega⟩
  rw [inner_mpvState_chainWindowOperator_offset A hL a n X]
  congr 3
  omega

/-- The numerator of the two-window expectation, with `X` on the window starting at `a` and
`Y` on the window starting at `a + L + m`, is `tr(E_X E_A^m E_Y E_A^{N-2L-m})`, independent of
`a` (arXiv:2307.01696, Supplemental Material, proof of Lemma 2, trace expansion). -/
theorem inner_mpvState_chainWindowOperator_mul_eq_trace (A : MPSTensor d D) {L N a m : ℕ}
    (hL : 0 < L) (haL : a + (L + m + L) ≤ N) (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ⟪mpvState A N, Matrix.toEuclideanLin
        (chainWindowOperator N a X * chainWindowOperator N (a + (L + m)) Y) (mpvState A N)⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (physicalObservableTransfer A L X * Kraus.transferMap A ^ m *
          physicalObservableTransfer A L Y * Kraus.transferMap A ^ (N - (L + m + L))) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = a + (L + m + L + n) := ⟨N - a - (L + m + L), by omega⟩
  rw [inner_mpvState_chainWindowOperator_mul_offset A hL a m n X Y]
  congr 3
  omega

/-- **Translation invariance of one-window expectations** (arXiv:2307.01696, eq. (TI-MPS2):
the vectors `φ_N` are translation invariant). -/
theorem mpvExpectation_chainWindowOperator_eq (A : MPSTensor d D) {L N a : ℕ} (hL : 0 < L)
    (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    mpvExpectation A N (chainWindowOperator N a X) =
      mpvExpectation A N (chainWindowOperator N 0 X) := by
  rw [mpvExpectation_eq_div, mpvExpectation_eq_div,
    inner_mpvState_chainWindowOperator_eq_trace A hL haL,
    inner_mpvState_chainWindowOperator_eq_trace A hL (by omega)]

/-- **Translation invariance of two-window expectations** (arXiv:2307.01696, eq. (TI-MPS2)). -/
theorem mpvExpectation_chainWindowOperator_mul_eq (A : MPSTensor d D) {L N a m : ℕ}
    (hL : 0 < L) (haL : a + (L + m + L) ≤ N) (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    mpvExpectation A N (chainWindowOperator N a X * chainWindowOperator N (a + (L + m)) Y) =
      mpvExpectation A N (chainWindowOperator N 0 X * chainWindowOperator N (L + m) Y) := by
  have h0 := inner_mpvState_chainWindowOperator_mul_eq_trace A hL (a := 0) (m := m) (N := N)
    (by omega) X Y
  rw [zero_add] at h0
  rw [mpvExpectation_eq_div, mpvExpectation_eq_div,
    inner_mpvState_chainWindowOperator_mul_eq_trace A hL haL, h0]

/-- The connected correlation of two window operators is invariant under translating both
windows (arXiv:2307.01696, eq. (TI-MPS2)). -/
theorem mpvExpectation_mul_sub_mul_eq_mpvConnectedCorrelator (A : MPSTensor d D) {L N a m : ℕ}
    (hL : 0 < L) (haL : a + (L + m + L) ≤ N) (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    mpvExpectation A N (chainWindowOperator N a X * chainWindowOperator N (a + (L + m)) Y) -
        mpvExpectation A N (chainWindowOperator N a X) *
          mpvExpectation A N (chainWindowOperator N (a + (L + m)) Y) =
      mpvConnectedCorrelator A N 0 (L + m) X Y := by
  rw [mpvConnectedCorrelator, mpvExpectation_chainWindowOperator_mul_eq A hL haL,
    mpvExpectation_chainWindowOperator_eq A hL (a := a) (by omega),
    mpvExpectation_chainWindowOperator_eq A hL (a := a + (L + m)) (by omega),
    mpvExpectation_chainWindowOperator_eq A hL (a := L + m) (by omega)]

/-! ### The clustering estimate -/

/-- A connected correlation of operators of norm at most `M` is at most `2M²`. -/
theorem norm_mpvExpectation_mul_sub_mul_le (A : MPSTensor d D) {N : ℕ}
    {O O' : Matrix (Cfg d N) (Cfg d N) ℂ} {M : ℝ}
    (hO : ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) O‖ ≤ M)
    (hO' : ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) O'‖ ≤ M) :
    ‖mpvExpectation A N (O * O') - mpvExpectation A N O * mpvExpectation A N O'‖ ≤
      2 * M ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hO
  have h1 := (norm_mpvExpectation_le A N (O * O')).trans
    ((Matrix.norm_toEuclideanCLM_mul_le _ _).trans (mul_le_mul hO hO' (norm_nonneg _) hM))
  have h2 := (norm_mpvExpectation_le A N O).trans hO
  have h3 := (norm_mpvExpectation_le A N O').trans hO'
  calc _ ≤ ‖mpvExpectation A N (O * O')‖ +
        ‖mpvExpectation A N O‖ * ‖mpvExpectation A N O'‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ M * M + M * M := add_le_add h1 (mul_le_mul h2 h3 (norm_nonneg _) hM)
    _ = 2 * M ^ 2 := by ring

/-- The operator norm of a product of maps is at most the product of bounds on the factors. -/
private theorem norm_toContinuousLinearMap_mul_le
    (F₁ F₂ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) {b₁ b₂ : ℝ}
    (h₁ : ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) F₁‖ ≤ b₁)
    (h₂ : ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) F₂‖ ≤ b₂) :
    ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (F₁ * F₂)‖ ≤ b₁ * b₂ := by
  rw [map_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁))

/-- **Clustering of block observables.** For a normal tensor in the gauge
`eq:ldp_normal_gauge` and a rate `r` above `|λ₂|`, there is `C` such that for operators
`X`, `Y` of norm at most `M` on windows of `w` sites, placed at the offsets `a` and
`a + w + g` of a chain of `N = a + (w + g + w + h)` sites, the connected correlation in
`φ_N` is at most `C (r^g + r^{h+a})`, whatever the window length `w`.

This is the estimate "the connected correlation in `φ_N` of two operators of norm at most
`4` on intervals separated by `g` and `g'` sites around the ring is at most
`C(r^g + r^{g'})`" of the chapter's proof of `thm:ldp_depth_lower_bound` (the chapter's
version of arXiv:2307.01696, Theorem 1). -/
theorem exists_norm_mpvExpectation_mul_sub_mul_le [NeZero D] {A : MPSTensor d D} {L₀ : ℕ}
    (hL1 : 1 ≤ L₀) (hL : Kraus.IsNBlkInjective A L₀) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) {lam₂ : ℂ}
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {r : ℝ} (hr : ‖lam₂‖ < r) (hr1 : r ≤ 1) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, 0 < w →
      ∀ X Y : Matrix (Fin w → Fin d) (Fin w → Fin d) ℂ,
        ‖Matrix.toEuclideanCLM (n := Fin w → Fin d) (𝕜 := ℂ) X‖ ≤ M →
        ‖Matrix.toEuclideanCLM (n := Fin w → Fin d) (𝕜 := ℂ) Y‖ ≤ M →
        ∀ a g h N : ℕ, a + (w + g + w + h) = N → 1 ≤ g → 1 ≤ h + a →
          ‖mpvExpectation A N (chainWindowOperator N a X * chainWindowOperator N (a + (w + g)) Y) -
              mpvExpectation A N (chainWindowOperator N a X) *
                mpvExpectation A N (chainWindowOperator N (a + (w + g)) Y)‖ ≤
            C * (r ^ g + r ^ (h + a)) := by
  classical
  have htr : Matrix.trace ρ ≠ 0 := by rw [hρtr]; exact one_ne_zero
  obtain ⟨CQ, hCQ, hQ⟩ := exists_compl_pow_bound hL1 hL hA hρ hρfix hρtr htr hmax hr
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr.le
  set E := Kraus.transferMap A with hE_def
  set P := fixedPointProj ρ htr with hP_def
  set Q := E - P with hQ_def
  set Φ : (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) :=
    Module.End.toContinuousLinearMap _ with hΦ_def
  set κ : ℝ := ∑ p : Fin D, ∑ q : Fin D, ‖Matrix.single p q (1 : ℂ)‖ with hκ_def
  have hκ : 0 ≤ κ := by positivity
  have htrb : ∀ F, ‖LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) F‖ ≤ κ * ‖Φ F‖ :=
    Matrix.norm_linearMap_trace_le_mul_norm
  have hTP : IsTracePreservingMap E := Kraus.isTracePreservingMap_mapLM_of_isTP A hA
  have hEk : ∀ k, 1 ≤ k → E ^ k = P + Q ^ k := fun k hk ↦
    pow_eq_fixedPointProj_add_compl_pow E htr hTP hρfix hk
  have hPform : ∀ Z, P Z = Matrix.trace Z • ρ := fun Z ↦ by
    simp [hP_def, fixedPointProj, hρtr]
  have htrFP : ∀ F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      LinearMap.trace ℂ _ (F * P) = Matrix.trace (F ρ) := by
    intro F
    have hFP : F * P = (Matrix.traceLinearMap (Fin D) ℂ ℂ).smulRight (F ρ) := by
      apply LinearMap.ext
      intro Z
      rw [Module.End.mul_apply, hPform, map_smul, LinearMap.smulRight_apply,
        Matrix.traceLinearMap_apply]
    rw [hFP, LinearMap.trace_smulRight, Matrix.traceLinearMap_apply]
  /- One constant `B ≥ 1` bounding every factor and `K` bounding every trace. -/
  set B : ℝ := (D : ℝ) ^ 3 * M + CQ + ‖Φ P‖ + 1 with hB_def
  have hB1 : 1 ≤ B := by
    have : 0 ≤ (D : ℝ) ^ 3 * M := by positivity
    linarith [norm_nonneg (Φ P)]
  have hB0 : 0 ≤ B := by linarith
  set K : ℝ := κ * B ^ 4 + 1 with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hrk0 : ∀ k, 0 ≤ r ^ k := fun k ↦ pow_nonneg hr0 k
  have hrle : ∀ k, r ^ k ≤ 1 := fun k ↦ pow_le_one₀ hr0 hr1
  have hQk : ∀ k, ‖Φ (Q ^ k)‖ ≤ B * r ^ k := fun k ↦
    (hQ k).trans (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (Φ P),
      (by positivity : 0 ≤ (D : ℝ) ^ 3 * M)]) (hrk0 k))
  have hPB : ‖Φ P‖ ≤ B := by linarith [(by positivity : 0 ≤ (D : ℝ) ^ 3 * M)]
  have hEkB : ∀ k, 1 ≤ k → ‖Φ (E ^ k)‖ ≤ B := by
    intro k hk
    rw [hEk k hk, map_add]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖Φ (Q ^ k)‖ ≤ CQ := (hQ k).trans (mul_le_of_le_one_right hCQ.le (hrle k))
    have h2 : 0 ≤ (D : ℝ) ^ 3 * M := by positivity
    linarith
  /- A bound `κ b₁ b₂ b₃ (B r^k) ≤ K r^k` for products of four bounded factors. -/
  have hK4 : ∀ {b₁ b₂ b₃ : ℝ} (k : ℕ), 0 ≤ b₁ → 0 ≤ b₂ → 0 ≤ b₃ → b₁ ≤ B → b₂ ≤ B → b₃ ≤ B →
      κ * (b₁ * b₂ * b₃ * (B * r ^ k)) ≤ K * r ^ k := by
    intro b₁ b₂ b₃ k h₁ h₂ h₃ h₁' h₂' h₃'
    have hb : b₁ * b₂ * b₃ * (B * r ^ k) ≤ B ^ 4 * r ^ k := by
      have : b₁ * b₂ * b₃ ≤ B * B * B := by gcongr
      calc b₁ * b₂ * b₃ * (B * r ^ k) ≤ B * B * B * (B * r ^ k) := by gcongr
        _ = B ^ 4 * r ^ k := by ring
    calc κ * (b₁ * b₂ * b₃ * (B * r ^ k)) ≤ κ * (B ^ 4 * r ^ k) :=
          mul_le_mul_of_nonneg_left hb hκ
      _ ≤ K * r ^ k := by rw [hK_def, add_mul, one_mul, mul_assoc]; linarith [hrk0 k]
  clear_value K B κ Q P E
  refine ⟨(4 * (K + 2) ^ 2 + 1) * K + 4 * M ^ 2 * K + 1, by positivity, ?_⟩
  intro w hw X Y hX hY a g h N hN hg hh
  set h' := h + a with hh'_def
  rw [mpvExpectation_mul_sub_mul_eq_mpvConnectedCorrelator A hw (by omega)]
  obtain rfl : N = w + g + w + h' := by omega
  set ε : ℝ := K * (r ^ g + r ^ h') with hε_def
  have hS : 0 ≤ r ^ g + r ^ h' := add_nonneg (hrk0 _) (hrk0 _)
  have hε0 : 0 ≤ ε := mul_nonneg hK0 hS
  clear_value ε
  by_cases hsmall : ε ≤ 1 / 2
  swap
  · /- Large `ε`: the trivial bound `2M²`. -/
    push Not at hsmall
    have hwX := (norm_toEuclideanCLM_chainWindowOperator_le (N := w + g + w + h') (a := 0)
      (by omega) (by omega) X).trans hX
    have hwY := (norm_toEuclideanCLM_chainWindowOperator_le (N := w + g + w + h')
      (a := w + g) (by omega) (by omega) Y).trans hY
    refine (norm_mpvExpectation_mul_sub_mul_le A hwX hwY).trans ?_
    have h4 : 2 * M ^ 2 ≤ 4 * M ^ 2 * ε := by
      have := mul_le_mul_of_nonneg_left hsmall.le (by positivity : (0 : ℝ) ≤ 4 * M ^ 2)
      linarith
    have h5 : 4 * M ^ 2 * ε = (4 * M ^ 2 * K) * (r ^ g + r ^ h') := by rw [hε_def]; ring
    have h6 : (4 * M ^ 2 * K) * (r ^ g + r ^ h') ≤
        ((4 * (K + 2) ^ 2 + 1) * K + 4 * M ^ 2 * K + 1) * (r ^ g + r ^ h') := by
      gcongr
      have : 0 ≤ (4 * (K + 2) ^ 2 + 1) * K := by positivity
      linarith
    linarith
  /- Small `ε`: compare with the limit correlator. -/
  obtain ⟨EX, hEX_def⟩ : ∃ F, F = physicalObservableTransfer A w X := ⟨_, rfl⟩
  obtain ⟨EY, hEY_def⟩ : ∃ F, F = physicalObservableTransfer A w Y := ⟨_, rfl⟩
  have hDB : (D : ℝ) ^ 3 * M ≤ B := by linarith [norm_nonneg (Φ P)]
  have hEX : ‖Φ EX‖ ≤ B := by
    rw [hEX_def]
    exact (norm_toContinuousLinearMap_physicalObservableTransfer_le hA w X).trans
      ((mul_le_mul_of_nonneg_left hX (by positivity)).trans hDB)
  have hEY : ‖Φ EY‖ ≤ B := by
    rw [hEY_def]
    exact (norm_toContinuousLinearMap_physicalObservableTransfer_le hA w Y).trans
      ((mul_le_mul_of_nonneg_left hY (by positivity)).trans hDB)
  have hB24 : B * B ≤ B ^ 4 := by
    rw [← sq]; exact pow_le_pow_right₀ hB1 (by norm_num)
  have hB4 : B ≤ B ^ 4 := by
    simpa using pow_le_pow_right₀ hB1 (show 1 ≤ 4 by norm_num)
  /- Every trace is bounded by `K r^k` once its map is bounded by `B⁴ r^k`. -/
  have htrK : ∀ (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (k : ℕ),
      ‖Φ F‖ ≤ B ^ 4 * r ^ k → ‖LinearMap.trace ℂ _ F‖ ≤ K * r ^ k := by
    intro F k hF
    refine (htrb F).trans ?_
    calc κ * ‖Φ F‖ ≤ κ * (B ^ 4 * r ^ k) := mul_le_mul_of_nonneg_left hF hκ
      _ ≤ K * r ^ k := by rw [hK_def, add_mul, one_mul, ← mul_assoc]; linarith [hrk0 k]
  have hmul := @norm_toContinuousLinearMap_mul_le D
  have hpow : ∀ {i j : ℕ}, j ≤ i → r ^ i ≤ r ^ j := fun hij ↦ pow_le_pow_of_le_one hr0 hr1 hij
  have hrg : r ^ g ≤ r ^ g + r ^ h' := le_add_of_nonneg_right (hrk0 _)
  have hrh : r ^ h' ≤ r ^ g + r ^ h' := le_add_of_nonneg_left (hrk0 _)
  have hεK : ∀ k, K * r ^ k ≤ K * r ^ h' → K * r ^ k ≤ ε := fun k hk ↦
    hk.trans ((mul_le_mul_of_nonneg_left hrh hK0).trans_eq hε_def.symm)
  /- The terms. -/
  have ha0 : ‖Matrix.trace (EX ρ)‖ ≤ K := by
    rw [← htrFP]
    have := htrK _ 0 ((hmul EX P hEX hPB).trans (by rw [pow_zero, mul_one]; exact hB24))
    simpa using this
  have hb0 : ‖Matrix.trace (EY ρ)‖ ≤ K := by
    rw [← htrFP]
    have := htrK _ 0 ((hmul EY P hEY hPB).trans (by rw [pow_zero, mul_one]; exact hB24))
    simpa using this
  have hgl : ‖limitCorrelator A ρ htr w X Y g‖ ≤ K * r ^ g := by
    have e : limitCorrelator A ρ htr w X Y g = LinearMap.trace ℂ _ (EX * Q ^ g * EY * P) := by
      rw [htrFP, hEX_def, hEY_def, hQ_def, hE_def, hP_def]; rfl
    rw [e]
    refine htrK _ g ((hmul _ _ (hmul _ _ (hmul _ _ hEX (hQk g)) hEY) hPB).trans ?_)
    calc B * (B * r ^ g) * B * B = B ^ 4 * r ^ g := by ring
      _ ≤ B ^ 4 * r ^ g := le_rfl
  have hδ : ‖LinearMap.trace ℂ _ (Q ^ (w + g + w + h'))‖ ≤ ε := by
    refine hεK (w + g + w + h') (mul_le_mul_of_nonneg_left (hpow (by omega)) hK0) |>.trans' ?_
    refine htrK _ _ ((hQk _).trans ?_)
    exact mul_le_mul_of_nonneg_right hB4 (hrk0 _)
  have hδX : ‖LinearMap.trace ℂ _ (EX * Q ^ (g + (w + h')))‖ ≤ ε := by
    refine hεK (g + (w + h')) (mul_le_mul_of_nonneg_left (hpow (by omega)) hK0) |>.trans' ?_
    refine htrK _ _ ((hmul _ _ hEX (hQk _)).trans ?_)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hB24 (hrk0 _)
  have hδY : ‖LinearMap.trace ℂ _ (EY * Q ^ (h' + (w + g)))‖ ≤ ε := by
    refine hεK (h' + (w + g)) (mul_le_mul_of_nonneg_left (hpow (by omega)) hK0) |>.trans' ?_
    refine htrK _ _ ((hmul _ _ hEY (hQk _)).trans ?_)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hB24 (hrk0 _)
  have hδXY : ‖LinearMap.trace ℂ _ (EX * E ^ g * EY * Q ^ h')‖ ≤ ε := by
    refine hεK _ le_rfl |>.trans' ?_
    refine htrK _ _ ((hmul _ _ (hmul _ _ (hmul _ _ hEX (hEkB g hg)) hEY) (hQk h')).trans ?_)
    calc B * B * B * (B * r ^ h') = B ^ 4 * r ^ h' := by ring
      _ ≤ B ^ 4 * r ^ h' := le_rfl
  have hG := mpvConnectedCorrelator_eq_of_compl hw hA (by rw [← hE_def]; exact hρfix) hρtr htr
    X Y hg hh
  rw [← hE_def, ← hP_def, ← hQ_def, ← hEX_def, ← hEY_def] at hG
  rw [hG]
  have hgK : ‖limitCorrelator A ρ htr w X Y g‖ ≤ K :=
    hgl.trans (mul_le_of_le_one_right hK0 (hrle g))
  have hmain := Complex.norm_div_sub_div_mul_div_sub_le (M := K) hε0 hsmall hK0
    (by rw [add_sub_cancel_left]; exact hδ)
    (by rw [add_sub_cancel_left]; exact hδXY)
    (by rw [add_sub_cancel_left]; exact hδX)
    (by rw [add_sub_cancel_left]; exact hδY) ha0 hb0 hgK
  have htri := norm_le_norm_sub_add
    ((Matrix.trace (EX ρ) * Matrix.trace (EY ρ) + limitCorrelator A ρ htr w X Y g +
        LinearMap.trace ℂ _ (EX * E ^ g * EY * Q ^ h')) /
        (1 + LinearMap.trace ℂ _ (Q ^ (w + g + w + h'))) -
      (Matrix.trace (EX ρ) + LinearMap.trace ℂ _ (EX * Q ^ (g + (w + h')))) /
        (1 + LinearMap.trace ℂ _ (Q ^ (w + g + w + h'))) *
      ((Matrix.trace (EY ρ) + LinearMap.trace ℂ _ (EY * Q ^ (h' + (w + g)))) /
        (1 + LinearMap.trace ℂ _ (Q ^ (w + g + w + h')))))
    (limitCorrelator A ρ htr w X Y g)
  refine htri.trans ?_
  have hsum : ‖limitCorrelator A ρ htr w X Y g‖ ≤ K * (r ^ g + r ^ h') :=
    hgl.trans (mul_le_mul_of_nonneg_left hrg hK0)
  calc _ ≤ 4 * (K + 2) ^ 2 * ε + K * (r ^ g + r ^ h') := add_le_add hmain hsum
    _ = ((4 * (K + 2) ^ 2 + 1) * K) * (r ^ g + r ^ h') := by rw [hε_def]; ring
    _ ≤ ((4 * (K + 2) ^ 2 + 1) * K + 4 * M ^ 2 * K + 1) * (r ^ g + r ^ h') := by
        gcongr
        have : 0 ≤ 4 * M ^ 2 * K := by positivity
        linarith

end MPSTensor
