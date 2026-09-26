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
* `exists_norm_mpvCovariance_le`: the clustering estimate.
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

/-- The normalized expectation of an operator is at most its operator norm (arXiv:2307.01696,
Supplemental Material, proof of Theorem 1, observables of norm one). -/
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

/-! ### The clustering estimate -/

private theorem mul4_le {a b c e a' b' c' e' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c') (hee : e ≤ e') :
    a * b * c * e ≤ a' * b' * c' * e' := by
  have ha' := ha.trans haa
  have hb' := hb.trans hbb
  have hc' := hc.trans hcc
  gcongr

private theorem mul2_le {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haa : a ≤ a') (hbb : b ≤ b') :
    a * b ≤ a' * b' := by
  have ha' := ha.trans haa
  gcongr

/-- **Clustering of block observables.** For a normal tensor in the gauge
`eq:ldp_normal_gauge` and a rate `r` above `|λ₂|`, there is `C` such that for operators
`X`, `Y` of norm at most `M` on windows of `w` sites, placed at the offsets `a` and
`a + w + g` of a chain of `N = a + (w + g + w + h)` sites, the connected correlation in
`φ_N` is at most `C (r^g + r^{h+a})`, whatever the window length `w`.

This is the estimate "the connected correlation in `φ_N` of two operators of norm at most
`4` on intervals separated by `g` and `g'` sites around the ring is at most
`C(r^g + r^{g'})`" of the chapter's proof of `thm:ldp_depth_lower_bound` (the chapter's
version of arXiv:2307.01696, Theorem 1). -/
theorem exists_norm_mpvCovariance_le [NeZero D] {A : MPSTensor d D} {L₀ : ℕ} (hL1 : 1 ≤ L₀)
    (hL : Kraus.IsNBlkInjective A L₀) (hA : ∑ i, (A i)ᴴ * A i = 1)
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
  let Φ : (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) :=
    Module.End.toContinuousLinearMap _
  set κ : ℝ := ∑ p : Fin D, ∑ q : Fin D, ‖Matrix.single p q (1 : ℂ)‖ with hκ_def
  have hκ : 0 ≤ κ := by positivity
  have htrb : ∀ F, ‖LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) F‖ ≤ κ * ‖Φ F‖ :=
    Matrix.norm_linearMap_trace_le_mul_norm
  set KX : ℝ := (D : ℝ) ^ 3 * M with hKX_def
  have hKX : 0 ≤ KX := by positivity
  set pP : ℝ := ‖Φ P‖ with hpP_def
  have hpP : 0 ≤ pP := norm_nonneg _
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
  have hP1 : LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) P = 1 := fixedPointProj_trace ρ htr
  /- The single constant `K` dominating every error term. -/
  set B : ℝ := KX + CQ + pP + 1 with hB_def
  have hB1 : 1 ≤ B := by linarith
  have hKXB : KX ≤ B := by linarith
  have hCQB : CQ ≤ B := by linarith
  have hpPB : pP ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  set K : ℝ := κ * B ^ 4 + 1 with hK_def
  have hK1 : 1 ≤ K := by
    have : 0 ≤ κ * B ^ 4 := by positivity
    linarith
  have hκB : ∀ t : ℝ, t ≤ B ^ 4 → κ * t ≤ K := fun t ht ↦ by
    have := mul_le_mul_of_nonneg_left ht hκ
    linarith
  have hB2 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
  have hB1' : B ≤ B ^ 4 := by simpa using pow_le_pow_right₀ hB1 (show 1 ≤ 4 by norm_num)
  have hΦ4 : ∀ F₁ F₂ F₃ F₄ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      ‖LinearMap.trace ℂ _ (F₁ * F₂ * F₃ * F₄)‖ ≤
        κ * (‖Φ F₁‖ * ‖Φ F₂‖ * ‖Φ F₃‖ * ‖Φ F₄‖) := by
    intro F₁ F₂ F₃ F₄
    refine (htrb _).trans (mul_le_mul_of_nonneg_left ?_ hκ)
    rw [map_mul, map_mul, map_mul]
    calc ‖Φ F₁ * Φ F₂ * Φ F₃ * Φ F₄‖ ≤ ‖Φ F₁ * Φ F₂ * Φ F₃‖ * ‖Φ F₄‖ := norm_mul_le _ _
      _ ≤ (‖Φ F₁ * Φ F₂‖ * ‖Φ F₃‖) * ‖Φ F₄‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (‖Φ F₁‖ * ‖Φ F₂‖ * ‖Φ F₃‖) * ‖Φ F₄‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
  have hΦ2 : ∀ F₁ F₂ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      ‖LinearMap.trace ℂ _ (F₁ * F₂)‖ ≤ κ * (‖Φ F₁‖ * ‖Φ F₂‖) := by
    intro F₁ F₂
    refine (htrb _).trans (mul_le_mul_of_nonneg_left ?_ hκ)
    rw [map_mul]
    exact norm_mul_le _ _
  refine ⟨(12 * (K + 2) ^ 2 + 12 * M ^ 2 + 1) * K, by positivity, ?_⟩
  intro w hw X Y hX hY a g h N hN hg hh
  subst hN
  have hEX : ‖Φ (physicalObservableTransfer A w X)‖ ≤ KX :=
    (norm_toContinuousLinearMap_physicalObservableTransfer_le hA w X).trans
      (mul_le_mul_of_nonneg_left hX (by positivity))
  have hEY : ‖Φ (physicalObservableTransfer A w Y)‖ ≤ KX :=
    (norm_toContinuousLinearMap_physicalObservableTransfer_le hA w Y).trans
      (mul_le_mul_of_nonneg_left hY (by positivity))
  have hQk : ∀ k, ‖Φ (Q ^ k)‖ ≤ CQ * r ^ k := hQ
  have hQk' : ∀ k, ‖Φ (Q ^ k)‖ ≤ B := fun k ↦ (hQk k).trans
    ((mul_le_of_le_one_right hCQ.le (pow_le_one₀ hr0 hr1)).trans hCQB)
  have hpow : ∀ {i j : ℕ}, j ≤ i → r ^ i ≤ r ^ j := fun hij ↦ pow_le_pow_of_le_one hr0 hr1 hij
  have hrle : ∀ k, r ^ k ≤ 1 := fun k ↦ pow_le_one₀ hr0 hr1
  have hrk0 : ∀ k, 0 ≤ r ^ k := fun k ↦ pow_nonneg hr0 k
  set EX := physicalObservableTransfer A w X with hEX_def
  set EY := physicalObservableTransfer A w Y with hEY_def
  have hEXB : ‖Φ EX‖ ≤ B := hEX.trans hKXB
  have hEYB : ‖Φ EY‖ ≤ B := hEY.trans hKXB
  have hPB : ‖Φ P‖ ≤ B := hpPB
  /- The one-point values and their bounds. -/
  set x : ℂ := Matrix.trace (EX ρ) with hx_def
  set y : ℂ := Matrix.trace (EY ρ) with hy_def
  have hxb : ‖x‖ ≤ K := by
    rw [hx_def, ← htrFP EX]
    refine (hΦ2 _ _).trans (hκB _ ?_)
    calc ‖Φ EX‖ * ‖Φ P‖ ≤ B * B := mul_le_mul hEXB hPB (norm_nonneg _) hB0
      _ = B ^ 2 := by ring
      _ ≤ B ^ 4 := hB2
  have hyb : ‖y‖ ≤ K := by
    rw [hy_def, ← htrFP EY]
    refine (hΦ2 _ _).trans (hκB _ ?_)
    calc ‖Φ EY‖ * ‖Φ P‖ ≤ B * B := mul_le_mul hEYB hPB (norm_nonneg _) hB0
      _ = B ^ 2 := by ring
      _ ≤ B ^ 4 := hB2
  /- The numerators as traces. -/
  set N := a + (w + g + w + h) with hN_def
  set h' := h + a with hh'_def
  have eZ : ⟪mpvState A N, mpvState A N⟫_ℂ = 1 + LinearMap.trace ℂ _ (Q ^ N) := by
    rw [inner_mpvState_self_eq_trace, hEk N (by omega), map_add, hP1]
  have eX : ⟪mpvState A N, Matrix.toEuclideanLin (chainWindowOperator N a X) (mpvState A N)⟫_ℂ =
      x + LinearMap.trace ℂ _ (EX * Q ^ ((g + w + h) + a)) := by
    have e := inner_mpvState_chainWindowOperator_offset A hw a (g + w + h) X
    rw [show a + (w + (g + w + h)) = N by omega] at e
    rw [e, hEk _ (by omega), mul_add, map_add, htrFP]
  have eY : ⟪mpvState A N,
      Matrix.toEuclideanLin (chainWindowOperator N (a + (w + g)) Y) (mpvState A N)⟫_ℂ =
      y + LinearMap.trace ℂ _ (EY * Q ^ (h + (a + (w + g)))) := by
    have e := inner_mpvState_chainWindowOperator_offset A hw (a + (w + g)) h Y
    rw [show a + (w + g) + (w + h) = N by omega] at e
    rw [e, hEk _ (by omega), mul_add, map_add, htrFP]
  have eXY : ⟪mpvState A N, Matrix.toEuclideanLin
      (chainWindowOperator N a X * chainWindowOperator N (a + (w + g)) Y) (mpvState A N)⟫_ℂ =
      x * y + (LinearMap.trace ℂ _ (EX * P * EY * Q ^ h') +
        LinearMap.trace ℂ _ (EX * Q ^ g * EY * P) +
        LinearMap.trace ℂ _ (EX * Q ^ g * EY * Q ^ h')) := by
    rw [inner_mpvState_chainWindowOperator_mul_offset A hw a g h X Y, hEk g hg, hEk h' hh]
    have hxy : LinearMap.trace ℂ _ (EX * P * EY * P) = x * y := by
      rw [htrFP, Module.End.mul_apply, Module.End.mul_apply, hPform, map_smul,
        Matrix.trace_smul, smul_eq_mul, mul_comm]
    simp only [mul_add, add_mul, map_add, hxy]
    ring
  /- The error bounds. -/
  set ε : ℝ := K * (r ^ g + r ^ h') with hε_def
  have hε0 : 0 ≤ ε := by positivity
  have hrg : r ^ g ≤ r ^ g + r ^ h' := le_add_of_nonneg_right (hrk0 _)
  have hrh : r ^ h' ≤ r ^ g + r ^ h' := le_add_of_nonneg_left (hrk0 _)
  have herr : ∀ (t : ℝ) (k : ℕ), t ≤ κ * B ^ 4 * r ^ k → r ^ k ≤ r ^ g + r ^ h' → t ≤ ε :=
    fun t k ht hk ↦ by
      refine ht.trans ?_
      rw [hε_def]
      have h1 : κ * B ^ 4 ≤ K := by linarith
      exact mul_le_mul h1 hk (hrk0 _) (by linarith)
  have hZerr : ‖(1 + LinearMap.trace ℂ _ (Q ^ N)) - 1‖ ≤ ε := by
    rw [add_sub_cancel_left]
    refine herr _ N ((htrb _).trans ?_) ((hpow (by omega)).trans hrh)
    calc κ * ‖Φ (Q ^ N)‖ ≤ κ * (B ^ 4 * r ^ N) := by
          refine mul_le_mul_of_nonneg_left ((hQk N).trans ?_) hκ
          exact mul_le_mul_of_nonneg_right (hCQB.trans hB1') (hrk0 _)
      _ = κ * B ^ 4 * r ^ N := by ring
  have hXerr : ‖(x + LinearMap.trace ℂ _ (EX * Q ^ ((g + w + h) + a))) - x‖ ≤ ε := by
    rw [add_sub_cancel_left]
    refine herr _ ((g + w + h) + a) ((hΦ2 _ _).trans ?_) ((hpow (by omega)).trans hrh)
    calc κ * (‖Φ EX‖ * ‖Φ (Q ^ ((g + w + h) + a))‖)
        ≤ κ * (B * (B * r ^ ((g + w + h) + a))) :=
          mul_le_mul_of_nonneg_left (mul2_le (norm_nonneg _) (norm_nonneg _) hEXB
            ((hQk _).trans (mul_le_mul_of_nonneg_right hCQB (hrk0 _)))) hκ
      _ ≤ κ * (B ^ 4 * r ^ ((g + w + h) + a)) := by
          refine mul_le_mul_of_nonneg_left ?_ hκ
          calc B * (B * r ^ ((g + w + h) + a)) = B ^ 2 * r ^ ((g + w + h) + a) := by ring
            _ ≤ B ^ 4 * r ^ ((g + w + h) + a) := mul_le_mul_of_nonneg_right hB2 (hrk0 _)
      _ = κ * B ^ 4 * r ^ ((g + w + h) + a) := by ring
  have hYerr : ‖(y + LinearMap.trace ℂ _ (EY * Q ^ (h + (a + (w + g))))) - y‖ ≤ ε := by
    rw [add_sub_cancel_left]
    refine herr _ (h + (a + (w + g))) ((hΦ2 _ _).trans ?_) ((hpow (by omega)).trans hrh)
    calc κ * (‖Φ EY‖ * ‖Φ (Q ^ (h + (a + (w + g))))‖)
        ≤ κ * (B * (B * r ^ (h + (a + (w + g))))) :=
          mul_le_mul_of_nonneg_left (mul2_le (norm_nonneg _) (norm_nonneg _) hEYB
            ((hQk _).trans (mul_le_mul_of_nonneg_right hCQB (hrk0 _)))) hκ
      _ ≤ κ * (B ^ 4 * r ^ (h + (a + (w + g)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hκ
          calc B * (B * r ^ (h + (a + (w + g)))) = B ^ 2 * r ^ (h + (a + (w + g))) := by ring
            _ ≤ B ^ 4 * r ^ (h + (a + (w + g))) := mul_le_mul_of_nonneg_right hB2 (hrk0 _)
      _ = κ * B ^ 4 * r ^ (h + (a + (w + g))) := by ring
  have hXYerr : ‖(x * y + (LinearMap.trace ℂ _ (EX * P * EY * Q ^ h') +
        LinearMap.trace ℂ _ (EX * Q ^ g * EY * P) +
        LinearMap.trace ℂ _ (EX * Q ^ g * EY * Q ^ h'))) - (x * y + 0)‖ ≤ 3 * ε := by
    rw [add_zero, add_sub_cancel_left]
    have e1 : ‖LinearMap.trace ℂ _ (EX * P * EY * Q ^ h')‖ ≤ ε := by
      refine herr _ h' ((hΦ4 _ _ _ _).trans ?_) hrh
      calc κ * (‖Φ EX‖ * ‖Φ P‖ * ‖Φ EY‖ * ‖Φ (Q ^ h')‖) ≤ κ * (B * B * B * (B * r ^ h')) :=
            mul_le_mul_of_nonneg_left (mul4_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
              (norm_nonneg _) hEXB hPB hEYB
              ((hQk _).trans (mul_le_mul_of_nonneg_right hCQB (hrk0 _)))) hκ
        _ = κ * B ^ 4 * r ^ h' := by ring
    have e2 : ‖LinearMap.trace ℂ _ (EX * Q ^ g * EY * P)‖ ≤ ε := by
      refine herr _ g ((hΦ4 _ _ _ _).trans ?_) hrg
      calc κ * (‖Φ EX‖ * ‖Φ (Q ^ g)‖ * ‖Φ EY‖ * ‖Φ P‖) ≤ κ * (B * (B * r ^ g) * B * B) :=
            mul_le_mul_of_nonneg_left (mul4_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
              (norm_nonneg _) hEXB ((hQk _).trans (mul_le_mul_of_nonneg_right hCQB (hrk0 _)))
              hEYB hPB) hκ
        _ = κ * B ^ 4 * r ^ g := by ring
    have e3 : ‖LinearMap.trace ℂ _ (EX * Q ^ g * EY * Q ^ h')‖ ≤ ε := by
      refine herr _ g ((hΦ4 _ _ _ _).trans ?_) hrg
      calc κ * (‖Φ EX‖ * ‖Φ (Q ^ g)‖ * ‖Φ EY‖ * ‖Φ (Q ^ h')‖) ≤
            κ * (B * (B * r ^ g) * B * B) :=
            mul_le_mul_of_nonneg_left (mul4_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
              (norm_nonneg _) hEXB ((hQk _).trans (mul_le_mul_of_nonneg_right hCQB (hrk0 _)))
              hEYB (hQk' _)) hκ
        _ = κ * B ^ 4 * r ^ g := by ring
    calc _ ≤ ‖LinearMap.trace ℂ _ (EX * P * EY * Q ^ h') +
          LinearMap.trace ℂ _ (EX * Q ^ g * EY * P)‖ +
          ‖LinearMap.trace ℂ _ (EX * Q ^ g * EY * Q ^ h')‖ := norm_add_le _ _
      _ ≤ ε + ε + ε := add_le_add ((norm_add_le _ _).trans (add_le_add e1 e2)) e3
      _ = 3 * ε := by ring
  /- The covariance through the normalized expectations. -/
  have hcov : mpvExpectation A N (chainWindowOperator N a X * chainWindowOperator N (a + (w + g)) Y) -
      mpvExpectation A N (chainWindowOperator N a X) *
        mpvExpectation A N (chainWindowOperator N (a + (w + g)) Y) =
      (x * y + (LinearMap.trace ℂ _ (EX * P * EY * Q ^ h') +
          LinearMap.trace ℂ _ (EX * Q ^ g * EY * P) +
          LinearMap.trace ℂ _ (EX * Q ^ g * EY * Q ^ h'))) / (1 + LinearMap.trace ℂ _ (Q ^ N)) -
        (x + LinearMap.trace ℂ _ (EX * Q ^ ((g + w + h) + a))) /
            (1 + LinearMap.trace ℂ _ (Q ^ N)) *
          ((y + LinearMap.trace ℂ _ (EY * Q ^ (h + (a + (w + g))))) /
            (1 + LinearMap.trace ℂ _ (Q ^ N))) - 0 := by
    rw [sub_zero, mpvExpectation_eq_div, mpvExpectation_eq_div, mpvExpectation_eq_div, eXY, eX,
      eY, eZ]
  have hS : 0 ≤ r ^ g + r ^ h' := add_nonneg (hrk0 _) (hrk0 _)
  have hK0 : 0 ≤ K := by linarith
  by_cases hsmall : 3 * ε ≤ 1 / 2
  · rw [hcov]
    refine (Complex.norm_div_sub_div_mul_div_sub_le (M := K) (by positivity) hsmall hK0
      (hZerr.trans (by linarith)) hXYerr (hXerr.trans (by linarith))
      (hYerr.trans (by linarith)) hxb hyb (by rw [norm_zero]; exact hK0)).trans ?_
    rw [hε_def]
    calc 4 * (K + 2) ^ 2 * (3 * (K * (r ^ g + r ^ h'))) =
          12 * (K + 2) ^ 2 * K * (r ^ g + r ^ h') := by ring
      _ ≤ (12 * (K + 2) ^ 2 + 12 * M ^ 2 + 1) * K * (r ^ g + r ^ h') := by
          gcongr
          nlinarith [sq_nonneg M]
  · push Not at hsmall
    have hwX : ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (chainWindowOperator N a X)‖ ≤ M :=
      (norm_toEuclideanCLM_chainWindowOperator_le (by omega) (by omega) X).trans hX
    have hwY : ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
        (chainWindowOperator N (a + (w + g)) Y)‖ ≤ M :=
      (norm_toEuclideanCLM_chainWindowOperator_le (by omega) (by omega) Y).trans hY
    have hXY' : ‖mpvExpectation A N
        (chainWindowOperator N a X * chainWindowOperator N (a + (w + g)) Y)‖ ≤ M * M :=
      (norm_mpvExpectation_le A N _).trans ((Matrix.norm_toEuclideanCLM_mul_le _ _).trans
        (mul_le_mul hwX hwY (norm_nonneg _) hM))
    have hX' := (norm_mpvExpectation_le A N (chainWindowOperator N a X)).trans hwX
    have hY' := (norm_mpvExpectation_le A N (chainWindowOperator N (a + (w + g)) Y)).trans hwY
    calc _ ≤ ‖mpvExpectation A N
            (chainWindowOperator N a X * chainWindowOperator N (a + (w + g)) Y)‖ +
          ‖mpvExpectation A N (chainWindowOperator N a X)‖ *
            ‖mpvExpectation A N (chainWindowOperator N (a + (w + g)) Y)‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ M * M + M * M := add_le_add hXY' (mul_le_mul hX' hY' (norm_nonneg _) hM)
      _ ≤ 12 * M ^ 2 * ε := by nlinarith [sq_nonneg M]
      _ = 12 * M ^ 2 * K * (r ^ g + r ^ h') := by rw [hε_def]; ring
      _ ≤ (12 * (K + 2) ^ 2 + 12 * M ^ 2 + 1) * K * (r ^ g + r ^ h') := by
          gcongr
          nlinarith [sq_nonneg (K + 2)]
