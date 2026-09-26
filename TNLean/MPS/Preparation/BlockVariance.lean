/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.WindowClustering
import TNLean.MPS.Preparation.WindowSeparation

/-!
# Averages over separated windows in a normal matrix product state

For a normal tensor in the gauge `eq:ldp_normal_gauge`, the normalized vector `φ_N` is
translation invariant on windows that do not wrap around the ring, and a weighted average of
translates of one operator over windows spaced `Δ` apart has variance of order `1/n` in `φ_N`,
uniformly in the window length and in `N`.

These are the facts "zero expectation in `φ_N` by translation invariance" and "every average of
`n` of these operators, or of their pair products, has variance at most `C₁/n` in `φ_N`" of the
chapter's proof of `thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696,
Theorem 1).

## Main results

* `MPSTensor.mpvExpectation_chainWindowOperator_eq`,
  `MPSTensor.mpvExpectation_chainWindowOperator_mul_eq`: translation invariance of one- and
  two-window expectations.
* `MPSTensor.exists_norm_sub_inner_smul_sq_le_mpv`: the variance bound in `φ_N`.
-/

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Operator

namespace MPSTensor

variable {d D : ℕ}

/-- The normalized periodic vector `φ_N = φ_N(A) / ‖φ_N(A)‖` has norm one when `φ_N(A) ≠ 0`
(arXiv:2307.01696, eq. (TI-MPS2)). -/
theorem norm_inv_smul_mpvState {A : MPSTensor d D} {N : ℕ} (h : mpvState A N ≠ 0) :
    ‖((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

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
  rw [mpvExpectation_eq_div, mpvExpectation_eq_div,
    inner_mpvState_chainWindowOperator_mul_eq_trace A hL haL,
    ← zero_add (L + m), inner_mpvState_chainWindowOperator_mul_eq_trace A hL (by omega)]

/-- A geometric sum with ratio `0 ≤ r < 1` is at most `1 / (1 - r)`. -/
theorem sum_range_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, r ^ j ≤ 1 / (1 - r) := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1
  rwa [← Finset.range_eq_Ico, pow_zero] at h

/-- The reflected geometric sum `∑_{j<n} r^{n-j}` is at most `1 / (1 - r)` for `0 ≤ r < 1`. -/
theorem sum_range_pow_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, r ^ (n - j) ≤ 1 / (1 - r) := by
  refine le_trans ?_ (sum_range_pow_le hr0 hr1 n)
  rw [← Finset.sum_range_reflect (fun j ↦ r ^ j) n]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hj := Finset.mem_range.mp hj
  exact pow_le_pow_of_le_one hr0 hr1.le (by omega)

/-- **Variance of averages in a normal matrix product state.** For a normal tensor in the gauge
`eq:ldp_normal_gauge`, a rate `‖λ₂‖ < r < 1` and a bound `M`, there is `C'` such that: for a
Hermitian operator `X` on `w` sites of operator norm at most `M`, placed on the windows starting
at `k Δ`, `k < n`, with `w < Δ` and `n Δ ≤ N`, and real weights `|c_k| ≤ γ`, the sum
`Z = ∑ c_k X^{(k)}` satisfies `‖(Z - ⟨Z⟩_φ) φ‖² ≤ γ² · 3n · C'` in the normalized vector
`φ = φ_N`, whenever `φ_N(A) ≠ 0`.

This is "every average of `n` of these operators, or of their pair products, has variance at
most `C₁/n` in `φ_N`" in the chapter's proof of `thm:ldp_depth_lower_bound` (the chapter's
version of arXiv:2307.01696, Theorem 1). -/
theorem exists_norm_sub_inner_smul_sq_le_mpv [NeZero D] {A : MPSTensor d D} {L₀ : ℕ}
    (hL1 : 1 ≤ L₀) (hL : Kraus.IsNBlkInjective A L₀) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) {lam₂ : ℂ}
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {r : ℝ} (hr : ‖lam₂‖ < r) (hr1 : r < 1) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ w Δ n N : ℕ, 0 < w → w < Δ → n * Δ ≤ N → mpvState A N ≠ 0 →
      ∀ X : Matrix (Fin w → Fin d) (Fin w → Fin d) ℂ, X.IsHermitian →
        ‖Matrix.toEuclideanCLM (n := Fin w → Fin d) (𝕜 := ℂ) X‖ ≤ M →
        ∀ (c : Fin n → ℝ) (γ : ℝ), (∀ k, |c k| ≤ γ) →
          ‖(∑ k : Fin n, (c k : ℂ) • Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N) -
              ⟪((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N,
                (∑ k : Fin n, (c k : ℂ) •
                  Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                  (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)⟫_ℂ •
                (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)‖ ^ 2 ≤
            γ ^ 2 * (3 * n * C') := by
  classical
  obtain ⟨C, hC, hclus⟩ := exists_norm_mpvCovariance_le hL1 hL hA hρ hρfix hρtr hmax hr hr1.le hM
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr.le
  refine ⟨2 * M ^ 2 + C * (2 * (1 / (1 - r))), ?_, ?_⟩
  · have : 0 < 1 - r := by linarith
    positivity
  intro w Δ n N hw hwΔ hn hne X hX hXM c γ hc
  set χ : MPVSpace d N := ((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N
  have hχ : ‖χ‖ = 1 := norm_inv_smul_mpvState hne
  have hwin := fun k : Fin n ↦ MPSPreparation.window_lt_and_le (N := N) hw hwΔ.le hn k.isLt
  set Xk : Fin n → Matrix (Cfg d N) (Cfg d N) ℂ := fun k ↦ chainWindowOperator N (k.val * Δ) X
  have hnorm : ∀ k, ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (Xk k)‖ ≤ M := fun k ↦
    (norm_toEuclideanCLM_chainWindowOperator_le (hwin k).1 (hwin k).2 X).trans hXM
  set f : ℕ → ℝ := fun j ↦ (if j = 0 then 2 * M ^ 2 else 0) + C * (r ^ j + r ^ (n - j))
  have hf : ∀ j, 0 ≤ f j := fun j ↦ by
    simp only [f]
    have : 0 ≤ (if j = 0 then 2 * M ^ 2 else 0) := by split_ifs <;> positivity
    positivity
  have hmain := MPSPreparation.norm_sub_inner_smul_sq_le (fun k ↦ Matrix.toEuclideanLin (Xk k))
    (fun k ↦ Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (chainWindowOperator_isHermitian (hwin k).1 (hwin k).2 hX)) hχ c hc f hf
    (fun k ↦ by
      refine (MPSPreparation.norm_inner_sq_sub_le (Xk k) (hnorm k) hχ).trans ?_
      simp only [f, if_true, Nat.sub_zero]
      have : 0 ≤ C * (r ^ 0 + r ^ n) := by positivity
      linarith)
    (fun k l hkl ↦ by
      obtain ⟨j, hj⟩ : ∃ j, l.val = k.val + j := ⟨l.val - k.val, by have := Fin.lt_def.mp hkl; omega⟩
      have hj1 : 1 ≤ j := by have := Fin.lt_def.mp hkl; omega
      have hjn : j < n := by have := l.isLt; omega
      have hjk : l.val - k.val = j := by omega
      rw [hjk]
      -- positions
      set p := k.val * Δ with hp
      set q := l.val * Δ with hq
      have hqp : q = p + j * Δ := by rw [hq, hp, hj, Nat.add_mul]
      have hjΔ : j ≤ j * Δ := Nat.le_mul_of_pos_right j (by omega)
      have hjΔw : j * Δ ≥ (j - 1) * Δ + Δ := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hj1]
      have hlast : (l.val + 1) * Δ ≤ n * Δ := Nat.mul_le_mul_right _ l.isLt
      rw [Nat.succ_mul] at hlast
      have hnj : (n - j) * Δ + j * Δ ≤ n * Δ := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hjn.le]
      have hnjΔ : n - j ≤ (n - j - 1) * Δ + 1 := by
        have : n - j - 1 ≤ (n - j - 1) * Δ := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have hnjΔ' : (n - j - 1) * Δ + Δ = (n - j) * Δ := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
      have hjΔ' : j - 1 ≤ (j - 1) * Δ := Nat.le_mul_of_pos_right _ (by omega)
      set g := j * Δ - w with hg
      set h := N - q - w with hh
      have hN : p + (w + g + w + h) = N := by omega
      have hg1 : 1 ≤ g := by omega
      have hh1 : 1 ≤ h + p := by omega
      have hpos : p + (w + g) = q := by omega
      have hcl := hclus w hw X X hXM hXM p g h N hN hg1 hh1
      rw [hpos] at hcl
      have hcov : ⟪χ, Matrix.toEuclideanLin (Xk k) (Matrix.toEuclideanLin (Xk l) χ)⟫_ℂ -
          ⟪χ, Matrix.toEuclideanLin (Xk k) χ⟫_ℂ * ⟪χ, Matrix.toEuclideanLin (Xk l) χ⟫_ℂ =
          mpvExpectation A N (chainWindowOperator N p X * chainWindowOperator N q X) -
            mpvExpectation A N (chainWindowOperator N p X) *
              mpvExpectation A N (chainWindowOperator N q X) := by
        rw [← MPSPreparation.toEuclideanLin_mul_apply]
        rfl
      rw [hcov]
      refine hcl.trans ?_
      have hg' : j ≤ g := by omega
      have hh' : n - j ≤ h + p := by omega
      have e1 : r ^ g ≤ r ^ j := pow_le_pow_of_le_one hr0 hr1.le hg'
      have e2 : r ^ (h + p) ≤ r ^ (n - j) := pow_le_pow_of_le_one hr0 hr1.le hh'
      have hj0 : j ≠ 0 := by omega
      simp only [f, hj0, if_false, zero_add]
      gcongr)
  refine hmain.trans ?_
  gcongr
  have hsplit : ∑ j ∈ Finset.range n, f j =
      ∑ j ∈ Finset.range n, (if j = 0 then 2 * M ^ 2 else 0) +
        C * (∑ j ∈ Finset.range n, r ^ j + ∑ j ∈ Finset.range n, r ^ (n - j)) := by
    simp only [f, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  have h1 : ∑ j ∈ Finset.range n, (if j = 0 then 2 * M ^ 2 else 0) ≤ 2 * M ^ 2 := by
    rw [Finset.sum_ite_eq' (Finset.range n) 0]
    split_ifs <;> positivity
  have h2 := sum_range_pow_le hr0 hr1 n
  have h3 := sum_range_pow_sub_le hr0 hr1 n
  have : C * (∑ j ∈ Finset.range n, r ^ j + ∑ j ∈ Finset.range n, r ^ (n - j)) ≤
      C * (2 * (1 / (1 - r))) := by
    gcongr
    linarith
  linarith

end MPSTensor
