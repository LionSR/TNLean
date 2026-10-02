/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import TNLean.MPS.Preparation.LogDepthPreparation

/-!
# Polynomial accuracy at every sufficiently large chain length

The prescribed block length is `q = ⌈2 ξ (1 + η) log N⌉`. When `q ≤ N`, the last
block absorbs the remainder, giving blocks of lengths `q, ..., q, q + N % q`.
When `q > N`, the existing exact one-block preparation theorem supplies the normalized
periodic state, extending the block prescription to this case.

Source: arXiv:2307.01696, the paragraph following Lemma 1 and the Supplemental Material,
proof of Theorem 1.

**Scope restriction (positive correlation length):** The prescribed logarithmic blocking
assumes `ξ > 0`. The zero-correlation-length case remains outside this construction; see
`docs/paper-gaps/mswc24_polynomial_accuracy_uniform_blocks.tex`.
-/

open scoped BigOperators ComplexOrder InnerProductSpace
open MPSTensor QuantumCircuit

namespace MPSPreparation

/-- The logarithmic block length prescribed after Lemma 1 of arXiv:2307.01696. -/
noncomputable def polynomialBlockLength (ξ η : ℝ) (N : ℕ) : ℕ :=
  ⌈2 * ξ * (1 + η) * Real.log N⌉₊

/-- Absorb the remainder into the final block, as in arXiv:2307.01696,
Supplemental Material, proof of Theorem 1. -/
def remainderBlockLengths (q N : ℕ) (k : Fin (N / q)) : ℕ :=
  if k.val + 1 = N / q then q + N % q else q

/-- The remainder-absorbing blocks partition the chain whenever `0 < q ≤ N`.
Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1. -/
theorem sum_remainderBlockLengths {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    ∑ k, remainderBlockLengths q N k = N := by
  obtain ⟨m, hm⟩ : ∃ m, N / q = m + 1 :=
    ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq)).symm⟩
  unfold remainderBlockLengths
  rw [hm, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hcast : ∀ k : Fin m, ¬k.val + 1 = m + 1 := fun k => by omega
  simp only [hcast, ite_false, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  have := Nat.div_add_mod N q
  rw [hm] at this
  nlinarith

/-- The actual all-length approximation: apply each block's polar partial isometry to the
fixed-point pairs, or use the exact normalized state when the prescribed block is longer
than the chain. Source: arXiv:2307.01696, eq. (10) and Supplemental Material, proof of
Theorem 1. -/
noncomputable def allLengthPolynomialState {d D : ℕ} (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ) (ξ η : ℝ) (N : ℕ) : MPVSpace d N :=
  if h : 0 < polynomialBlockLength ξ η N ∧ polynomialBlockLength ξ η N ≤ N then
    blockIsometryState A (fixedPointPair σ) (sum_remainderBlockLengths h.1 h.2)
  else normalizedMPVState A N

private theorem polynomialBlockLength_bounds {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {N R : ℕ} (hN : 2 ≤ N)
    (hthreshold : ⌈Real.exp ((R : ℝ) / (2 * ξ))⌉₊ ≤ N) :
    R ≤ polynomialBlockLength ξ η N ∧
      (polynomialBlockLength ξ η N : ℝ) ≤
        (2 * ξ + 1 / Real.log 2) * ((1 + η) * Real.log N) := by
  have hlog : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log N := hl2.trans_le hlog
  have hRlog : (R : ℝ) ≤ 2 * ξ * Real.log N := by
    have hexp : Real.exp ((R : ℝ) / (2 * ξ)) ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hthreshold)
    have h := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at h
    nlinarith [(div_le_iff₀ (by positivity : 0 < 2 * ξ)).mp h]
  have hQpos : 0 < 2 * ξ * (1 + η) * Real.log N := by positivity
  have hceil := Nat.le_ceil (2 * ξ * (1 + η) * Real.log N)
  constructor
  · have hbound : (R : ℝ) ≤ (polynomialBlockLength ξ η N : ℝ) := by
      have hprod : 0 ≤ 2 * ξ * η * Real.log N := by positivity
      change (R : ℝ) ≤ (⌈2 * ξ * (1 + η) * Real.log N⌉₊ : ℝ)
      nlinarith
    exact_mod_cast hbound
  · have hupper := Nat.ceil_lt_add_one hQpos.le
    have hlogη : Real.log 2 ≤ (1 + η) * Real.log N := by
      nlinarith [mul_pos hη hlogpos]
    have hone : 1 ≤ 1 / Real.log 2 * ((1 + η) * Real.log N) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hl2]
      simpa only [one_mul] using hlogη
    change (⌈2 * ξ * (1 + η) * Real.log N⌉₊ : ℝ) ≤ _
    nlinarith

private theorem polynomial_error_factor {ξ η : ℝ} (hξ : 0 < ξ)
    {N q M : ℕ} (hN : 0 < N) (hM : M ≤ N)
    (hceil : 2 * ξ * (1 + η) * Real.log N ≤ (q : ℝ)) :
    (M : ℝ) * Real.exp (-(1 / 2) * q / ξ) ≤ (N : ℝ) ^ (-η) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hexponent : -(1 / 2) * q / ξ ≤ -(1 + η) * Real.log N := by
    apply (div_le_iff₀ hξ).mpr
    nlinarith [hceil]
  calc
    (M : ℝ) * Real.exp (-(1 / 2) * q / ξ)
        ≤ (N : ℝ) * Real.exp (-(1 / 2) * q / ξ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hM) (Real.exp_pos _).le
    _ = Real.exp (Real.log N + -(1 / 2) * q / ξ) := by
      rw [Real.exp_add, Real.exp_log hNpos]
    _ ≤ Real.exp (Real.log N + -(1 + η) * Real.log N) :=
      Real.exp_le_exp.mpr (add_le_add (le_refl _) hexponent)
    _ = (N : ℝ) ^ (-η) := by
      rw [Real.rpow_def_of_pos hNpos]
      congr 1
      ring

/-- The prescribed logarithmic blocking gives polynomial accuracy at every sufficiently
large length, using one remainder-absorbing block or exact preparation when the prescribed
block exceeds the chain. The constants and threshold precede the accuracy exponent.
Source: arXiv:2307.01696, paragraph following Lemma 1 and Supplemental Material,
proof of Theorem 1. Positive correlation length is assumed. -/
theorem exists_isPreparedInDepth_allLengthPolynomialState {d D : ℕ} (A : MPSTensor d D)
    (hNormal : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) :
    ∃ (C c : ℝ) (N₀ : ℕ), 0 < C ∧ 0 < c ∧ 2 ≤ N₀ ∧
      ∀ η : ℝ, 0 < η → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
        mpvState A N ≠ 0 ∧ ∃ T : ℕ,
          ‖allLengthPolynomialState A σ (correlationLength lam₂) η N‖ = 1 ∧
          (T : ℝ) ≤ c * ((1 + η) * Real.log N) ∧
          IsPreparedInDepth T
            (fun s => allLengthPolynomialState A σ (correlationLength lam₂) η N s) ∧
          1 - ‖⟪allLengthPolynomialState A σ (correlationLength lam₂) η N,
            normalizedMPVState A N⟫_ℂ‖ ≤ C * (N : ℝ) ^ (-η) := by
  classical
  have : NeZero D := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨_, hlam1⟩ := norm_pos_and_lt_one_of_correlationLength_pos hξ
  obtain ⟨C, hC, herr⟩ := exists_blockApproximationError_le_mul A hNormal hA hσ htr hfix
    hlam hlam1.le (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_blockIsometryState d D
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedMPVState d D
  obtain ⟨Nz, hNz⟩ := exists_mpvState_ne_zero_of_le A hNormal
  obtain ⟨L, hLpos, hL⟩ := hNormal
  have hinj : ∀ n, L ≤ n → Kraus.IsInjective (blockTensor A n) := fun n hn =>
    (isNBlkInjective_iff_blockTensor_isInjective A n).mp (isNBlkInjective_of_le hLpos hL hn)
  set R := L + 3 * D
  set ξ := correlationLength lam₂
  set a := 2 * ξ + 1 / Real.log 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < a := by dsimp [a, ξ]; positivity
  set c := (2 * (Cb : ℝ) + Ce + 1) * a
  set N₀ := max (max Nz (max R 2)) ⌈Real.exp ((R : ℝ) / (2 * ξ))⌉₊
  refine ⟨C, c, N₀, hC, by dsimp [c]; positivity, ?_, ?_⟩
  · dsimp [N₀]
    omega
  intro η hη N _ hN
  have hcuts : Nz ≤ N ∧ R ≤ N ∧ 2 ≤ N ∧
      ⌈Real.exp ((R : ℝ) / (2 * ξ))⌉₊ ≤ N := by
    dsimp [N₀] at hN
    omega
  have h0 := hNz N hcuts.1
  refine ⟨h0, ?_⟩
  set q := polynomialBlockLength ξ η N
  obtain ⟨hRq, hqa⟩ := polynomialBlockLength_bounds hξ hη hcuts.2.2.1 hcuts.2.2.2
  have hq0 : 0 < q := by dsimp [q, R] at *; omega
  have hθ : 0 < (1 + η) * Real.log N := by
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    positivity
  have hLq : L ≤ q := by dsimp [q, R] at *; omega
  have hDq : 3 * D ≤ q := by dsimp [q, R] at *; omega
  by_cases hqN : q ≤ N
  · let ℓ := remainderBlockLengths q N
    have hsum := sum_remainderBlockLengths hq0 hqN
    have : NeZero (N / q) := ⟨(Nat.div_pos hqN hq0).ne'⟩
    have hℓq : ∀ k, q ≤ ℓ k := fun k => by
      dsimp [ℓ, remainderBlockLengths]
      split_ifs <;> omega
    have hℓ2 : ∀ k, ℓ k ≤ 2 * q := fun k => by
      have := Nat.mod_lt N hq0
      dsimp [ℓ, remainderBlockLengths]
      split_ifs <;> omega
    have hinjℓ : ∀ k, Kraus.IsInjective (blockTensor A (ℓ k)) :=
      fun k => hinj _ (hLq.trans (hℓq k))
    have hω : ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = 1 := by
      rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
    have hstate : allLengthPolynomialState A σ ξ η N =
        blockIsometryState A (fixedPointPair σ) hsum := by
      unfold allLengthPolynomialState
      rw [dite_eq_left (show 0 < polynomialBlockLength ξ η N ∧
        polynomialBlockLength ξ η N ≤ N from ⟨hq0, hqN⟩)]
    refine ⟨Cb * (2 * q), hstate ▸ norm_blockIsometryState A hω hsum hinjℓ, ?_, ?_, ?_⟩
    · push_cast
      have hfirst : 2 * (Cb : ℝ) * q ≤ 2 * Cb * (a * ((1 + η) * Real.log N)) :=
        mul_le_mul_of_nonneg_left hqa (by positivity)
      dsimp [c]
      nlinarith [mul_nonneg (Nat.cast_nonneg Ce) ha.le,
        mul_nonneg (Nat.cast_nonneg Ce) hθ.le]
    · rw [hstate]
      exact hCb A _ hω ℓ hsum (2 * q) (fun k => hDq.trans (hℓq k)) hℓ2 hinjℓ
    · rw [hstate]
      refine (herr (N / q) ℓ hsum q hℓq hinjℓ).trans ?_
      exact mul_le_mul_of_nonneg_left
        (polynomial_error_factor hξ (by omega) (Nat.div_le_self N q)
          (Nat.le_ceil (2 * ξ * (1 + η) * Real.log N))) hC.le
  · have hstate : allLengthPolynomialState A σ ξ η N = normalizedMPVState A N := by
      unfold allLengthPolynomialState
      rw [dite_eq_right (show ¬(0 < polynomialBlockLength ξ η N ∧
        polynomialBlockLength ξ η N ≤ N) from by change ¬(0 < q ∧ q ≤ N); tauto)]
    refine ⟨Ce * N, hstate ▸ norm_normalizedMPVState h0, ?_, ?_, ?_⟩
    · have hNq : (N : ℝ) ≤ q := by exact_mod_cast (show N ≤ q by omega)
      have hfirst := mul_le_mul_of_nonneg_left (hNq.trans hqa) (Nat.cast_nonneg Ce)
      push_cast
      dsimp [c]
      nlinarith [mul_nonneg (Nat.cast_nonneg Cb) ha.le,
        mul_nonneg (Nat.cast_nonneg Cb) hθ.le]
    · rw [hstate]
      exact hCe A N (by dsimp [R] at hcuts; omega) (hinj N (by dsimp [R] at hcuts; omega)) h0
    · rw [hstate, inner_self_eq_norm_sq_to_K, norm_normalizedMPVState h0]
      norm_num
      positivity

end MPSPreparation
