/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyConstruction
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Quantitative radii in the hierarchical construction

The adaptive radii of Hastings' hierarchy remain uniformly exponentially small through
all its levels. An explicit projection length proportional to the square of the number
of levels suffices for the sum of all radii to lie below a prescribed spectral gap.

**Local fix (deficiency recurrence):** these estimates use the corrected recurrence
against the original state, with coefficient `3^h - 1` and decay exponent `1/4`, as recorded
in `docs/paper-gaps/hastings05_hierarchical_projection.tex`.

Source: Hastings, arXiv:cond-mat/0508554v3, Section II, lines 676–720.
-/

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The scalar deficiency majorant increases with the level.
Hastings, arXiv:cond-mat/0508554v3, lines 696–707, with the corrected recurrence. -/
theorem monotone_hierarchyMajorant (e s : ℝ) : Monotone (hierarchyMajorant e s) := by
  apply monotone_nat_of_le_succ
  intro m
  rw [hierarchyMajorant_succ]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (hierarchyMajorant e s m),
    sq_nonneg ((e + 2 * hierarchyMajorant e s m) ^ s)]

/-- Every adaptive window has strictly positive radius when the coupling bound is positive.
Hastings, arXiv:cond-mat/0508554v3, lines 676–685. -/
theorem hierarchyWindowRadius_pos {K : ℝ} (hK : 0 < K) (r : ℝ) (h m : ℕ) :
    0 < hierarchyWindowRadius K r h m := by
  unfold hierarchyWindowRadius
  apply mul_pos hK
  apply Real.rpow_pos_of_pos
  exact add_pos_of_pos_of_nonneg (Real.exp_pos _)
    (mul_nonneg (by norm_num) (hierarchyMajorant_nonneg _ _ _))

/-- All levels up to the last obey the same exponentially decaying majorant.
Hastings, arXiv:cond-mat/0508554v3, lines 705–707, with the corrected coefficient. -/
theorem hierarchyMajorant_exp_le {r : ℝ} (hr : 0 ≤ r) {h m : ℕ} (hh : 2 ≤ h)
    (hm : m ≤ h) :
    hierarchyMajorant (Real.exp (-r)) (1 - 1 / (h : ℝ)) m ≤
      ((3 : ℝ) ^ h - 1) * Real.exp (-r / 4) := by
  have hbound := (monotone_hierarchyMajorant (Real.exp (-r)) (1 - 1 / (h : ℝ)) hm).trans
    (hierarchyMajorant_le_rpow_quarter (Real.exp_pos (-r))
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)) hh)
  simpa only [← Real.exp_mul, mul_one_div] using hbound

/-- The constructed hierarchy retains a nonzero space once `r > 4 h log 3`.
Hastings, arXiv:cond-mat/0508554v3, lines 705–711. -/
theorem hierarchyDeficiency_window_lt_one {K r : ℝ} (hK : 0 < K) {h : ℕ}
    (hh : 2 ≤ h) (hr : 4 * (h : ℝ) * Real.log 3 < r) :
    hierarchyDeficiency (K * Real.exp (-r)) K (hierarchyWindowRadius K r h) h < 1 := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have hr0 : 0 ≤ r := by nlinarith [mul_nonneg hh0 hlog.le]
  apply (hierarchyDeficiency_window_le hK hr0 hh).trans_lt
  calc
    ((3 : ℝ) ^ h - 1) * Real.exp (-r / 4) ≤
        (3 : ℝ) ^ h * Real.exp (-r / 4) := by gcongr; linarith
    _ = Real.exp ((h : ℝ) * Real.log 3 - r / 4) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      congr 1
      rw [neg_div]
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

/-- Each adaptive radius is at most `9 K exp(-r/(4h))`, uniformly through the last level.
Hastings, arXiv:cond-mat/0508554v3, lines 676–720. -/
theorem hierarchyWindowRadius_le {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) {h m : ℕ}
    (hh : 2 ≤ h) (hm : m ≤ h) :
    hierarchyWindowRadius K r h m ≤ 9 * K * Real.exp (-r / (4 * (h : ℝ))) := by
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
  have hβ := hierarchyMajorant_exp_le hr hh hm
  have hE : Real.exp (-r) ≤ Real.exp (-r / 4) := Real.exp_le_exp.mpr (by linarith)
  have h3 : 1 ≤ (3 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  have hbase : Real.exp (-r) +
      2 * hierarchyMajorant (Real.exp (-r)) (1 - 1 / (h : ℝ)) m ≤
      (9 : ℝ) ^ h * Real.exp (-r / 4) := by
    have h9 : (9 : ℝ) ^ h = ((3 : ℝ) ^ h) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm h 2, pow_mul]
      norm_num
    rw [h9]
    nlinarith [Real.exp_pos (-r / 4),
      mul_nonneg (sq_nonneg ((3 : ℝ) ^ h - 1)) (Real.exp_pos (-r / 4)).le]
  unfold hierarchyWindowRadius
  calc
    _ ≤ K * (((9 : ℝ) ^ h * Real.exp (-r / 4)) ^ (1 / (h : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact Real.rpow_le_rpow
        (add_nonneg (Real.exp_pos _).le
          (mul_nonneg (by norm_num) (hierarchyMajorant_nonneg _ _ _))) hbase
        (one_div_nonneg.mpr hhpos.le)
    _ = 9 * K * Real.exp (-r / (4 * (h : ℝ))) := by
      rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
        one_div, Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 9) (by omega),
        ← Real.exp_mul]
      have he : -r / 4 * (h : ℝ)⁻¹ = -r / (4 * (h : ℝ)) := by ring
      rw [he]
      ring

/-- The extra closing-link window retains the exponent `1/8` after the binary tree.
Hastings, arXiv:cond-mat/0508554v3, lines 705–720, with the periodic closing window
recorded in `docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
theorem eighth_le_one_sub_inv_pow_succ {h : ℕ} (hh : 2 ≤ h) :
    (1 / 8 : ℝ) ≤ (1 - 1 / (h : ℝ)) ^ (h + 1) := by
  have hhreal : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hs : (1 / 2 : ℝ) ≤ 1 - 1 / (h : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hhreal
    linarith
  rw [pow_succ]
  have hquarter := quarter_le_one_sub_inv_pow hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hquarter) (sub_nonneg.mpr hs)]

/-- The deficiency bound after the closing-link window is exponentially small in `r`.
Hastings, arXiv:cond-mat/0508554v3, lines 705–720, with the periodic correction above. -/
theorem hierarchyDeficiency_window_succ_le {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r)
    {h : ℕ} (hh : 2 ≤ h) :
    hierarchyDeficiency (K * Real.exp (-r)) K (hierarchyWindowRadius K r h) (h + 1) ≤
      ((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8) := by
  have he0 := Real.exp_pos (-r)
  have he1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
  obtain ⟨hs0, hs1⟩ := one_sub_inv_natCast_mem_Icc h
  have hbound := (hierarchyDeficiency_le_hierarchyMajorant hK he0
    (1 - 1 / (h : ℝ)) (h + 1)).trans (hierarchyMajorant_le he0 he1 hs0 hs1 (h + 1))
  have hcoeff : 0 ≤ (3 : ℝ) ^ (h + 1) - 1 := by
    have : 1 ≤ (3 : ℝ) ^ (h + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hexp := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge he0 he1 (eighth_le_one_sub_inv_pow_succ hh)) hcoeff
  change hierarchyDeficiency (K * Real.exp (-r)) K
    (fun m ↦ K * (Real.exp (-r) +
      2 * hierarchyMajorant (Real.exp (-r)) (1 - 1 / (h : ℝ)) m) ^ (1 / (h : ℝ))) (h + 1) ≤ _
  simpa only [sub_sub_cancel, ← Real.exp_mul, mul_one_div] using hbound.trans hexp

/-- The final closing window has nonzero retained space for the explicit linear threshold.
Hastings, arXiv:cond-mat/0508554v3, lines 705–711, with the periodic correction above. -/
theorem hierarchyDeficiency_window_succ_lt_one {K r : ℝ} (hK : 0 < K) {h : ℕ}
    (hh : 2 ≤ h) (hr : 8 * ((h : ℝ) + 1) * Real.log 3 < r) :
    hierarchyDeficiency (K * Real.exp (-r)) K (hierarchyWindowRadius K r h) (h + 1) < 1 := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have hr0 : 0 ≤ r := by nlinarith [mul_nonneg (by linarith : 0 ≤ (h : ℝ) + 1) hlog.le]
  apply (hierarchyDeficiency_window_succ_le hK hr0 hh).trans_lt
  calc
    ((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8) ≤
        (3 : ℝ) ^ (h + 1) * Real.exp (-r / 8) := by gcongr; linarith
    _ = Real.exp (((h : ℝ) + 1) * Real.log 3 - r / 8) := by
      rw [sub_eq_add_neg, Real.exp_add, ← Nat.cast_add_one, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      congr 1
      rw [neg_div]
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

/-- Absorb the linear prefactor by spending half of the exponential decay. -/
private theorem mul_exp_neg_div_le {a : ℝ} (ha : 0 < a) (r : ℝ) :
    r * Real.exp (-r / a) ≤ 2 * a * Real.exp (-r / (2 * a)) := by
  let t := r / (2 * a)
  have ht : t * Real.exp (-t) ≤ 1 := (Real.mul_exp_neg_le_exp_neg_one t).trans
    (Real.exp_le_one_iff.mpr (by norm_num))
  have hr : r = 2 * a * t := by dsimp [t]; field_simp
  have he : Real.exp (-r / a) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    field_simp
    ring
  rw [he]
  calc
    _ = 2 * a * (t * Real.exp (-t)) * Real.exp (-t) := by rw [hr]; ring
    _ ≤ 2 * a * 1 * Real.exp (-t) := by gcongr
    _ = _ := by simp only [mul_one, t, neg_div]

/-- An explicit projection length of order `h² (1 + log(J/Δ))`, with the logarithm
truncated below at zero. Hastings, arXiv:cond-mat/0508554v3, lines 709–720. -/
noncomputable def hierarchyProjectionLength (h : ℕ) (J Δ : ℝ) : ℝ :=
  512 * (h : ℝ) ^ 2 * (1 + max 0 (Real.log (J / Δ)))

/-- The logarithmic projection length makes the sum of `2^h` radii at most one quarter
of the gap, even when the coupling bound grows linearly with the projection length.
Hastings, arXiv:cond-mat/0508554v3, lines 709–720. -/
theorem hierarchyWindowEnergy_le_quarter_gap {h : ℕ} (hh : 2 ≤ h)
    {J Δ K r : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength h J Δ ≤ r) (hK : K ≤ J * r) :
    9 * (2 : ℝ) ^ h * K * Real.exp (-r / (4 * (h : ℝ))) ≤ Δ / 4 := by
  let H : ℝ := h
  let A := 1 + max 0 (Real.log (J / Δ))
  have hH : 2 ≤ H := by dsimp [H]; exact_mod_cast hh
  have hHpos : 0 < H := by linarith
  have hA : 1 ≤ A := by dsimp [A]; linarith [le_max_left 0 (Real.log (J / Δ))]
  have hr' : 512 * H ^ 2 * A ≤ r := hr
  have ht : 64 * H * A ≤ r / (8 * H) := by
    rw [le_div_iff₀ (by positivity : 0 < 8 * H)]
    nlinarith [hr']
  have hlogA : Real.log (J / Δ) ≤ A := by
    dsimp [A]
    linarith [le_max_right 0 (Real.log (J / Δ))]
  have hJexp : J ≤ Δ * Real.exp A := by
    have := Real.exp_le_exp.mpr hlogA
    rw [Real.exp_log (div_pos hJ hΔ), div_le_iff₀ hΔ] at this
    simpa only [mul_comm] using this
  have hExp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ h ≤ Real.exp H := by
    calc
      _ ≤ (Real.exp 1) ^ h := pow_le_pow_left₀ (by norm_num) hExp1 h
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one, H]
  have hHexp : H ≤ Real.exp H := by linarith [Real.add_one_le_exp H]
  have h72 : (72 : ℝ) ≤ Real.exp (36 * H) := by
    linarith [Real.add_one_le_exp (36 * H)]
  have hdecay : A + 38 * H - r / (8 * H) ≤ -2 := by
    have hHA : H ≤ H * A := by nlinarith
    have hAH : 2 * A ≤ H * A := by nlinarith
    nlinarith
  have hExp2 : (4 : ℝ) ≤ Real.exp 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hExp1 2
    norm_num [← Real.exp_nat_mul] at this ⊢
    exact this
  have hExpNeg : Real.exp (-2) ≤ 1 / 4 := by
    simpa only [Real.exp_neg, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hExp2
  calc
    _ ≤ 9 * (2 : ℝ) ^ h * (J * r) * Real.exp (-r / (4 * H)) := by gcongr
    _ = 9 * (2 : ℝ) ^ h * J * (r * Real.exp (-r / (4 * H))) := by ring
    _ ≤ 9 * (2 : ℝ) ^ h * J * (2 * (4 * H) * Real.exp (-r / (2 * (4 * H)))) := by
      exact mul_le_mul_of_nonneg_left (mul_exp_neg_div_le (by positivity : 0 < 4 * H) r)
        (by positivity)
    _ = 72 * (2 : ℝ) ^ h * H * J * Real.exp (-r / (8 * H)) := by
      have hden : 2 * (4 * H) = 8 * H := by ring
      rw [hden]
      ring
    _ ≤ Real.exp (36 * H) * Real.exp H * Real.exp H * (Δ * Real.exp A) *
        Real.exp (-r / (8 * H)) := by gcongr
    _ = Δ * Real.exp (A + 38 * H - r / (8 * H)) := by
      have hs : A + 38 * H - r / (8 * H) =
          36 * H + H + H + A + (-r / (8 * H)) := by ring
      rw [hs]
      simp only [Real.exp_add]
      ring
    _ ≤ Δ * Real.exp (-2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdecay) hΔ.le
    _ ≤ Δ / 4 := by nlinarith

/-- The logarithmic factor in the chosen length is at least one. -/
theorem hierarchyProjectionLength_ge_square (h : ℕ) (J Δ : ℝ) :
    512 * (h : ℝ) ^ 2 ≤ hierarchyProjectionLength h J Δ := by
  unfold hierarchyProjectionLength
  nlinarith [mul_nonneg (sq_nonneg (h : ℝ)) (le_max_left 0 (Real.log (J / Δ)))]

/-- The explicit projection length exceeds the nonzero-space threshold for the closing
window. Hastings, arXiv:cond-mat/0508554v3, lines 705–711, with the periodic correction. -/
theorem closing_threshold_lt_hierarchyProjectionLength {h : ℕ} (hh : 2 ≤ h) (J Δ : ℝ) :
    8 * ((h : ℝ) + 1) * Real.log 3 < hierarchyProjectionLength h J Δ := by
  have hH : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hlog : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at this
    exact this
  have hscale := hierarchyProjectionLength_ge_square h J Δ
  calc
    _ ≤ 16 * ((h : ℝ) + 1) := by nlinarith
    _ < 512 * (h : ℝ) ^ 2 := by nlinarith [sq_nonneg ((h : ℝ) - 1)]
    _ ≤ _ := hscale

/-- The chosen logarithmic length retains a nonzero space after the closing window.
Hastings, arXiv:cond-mat/0508554v3, lines 705–711, with the periodic correction. -/
theorem hierarchyDeficiency_window_succ_lt_one_of_length {h : ℕ} (hh : 2 ≤ h)
    {K r J Δ : ℝ} (hK : 0 < K) (hr : hierarchyProjectionLength h J Δ ≤ r) :
    hierarchyDeficiency (K * Real.exp (-r)) K (hierarchyWindowRadius K r h) (h + 1) < 1 :=
  hierarchyDeficiency_window_succ_lt_one hK hh
    ((closing_threshold_lt_hierarchyProjectionLength hh J Δ).trans_le hr)

/-- Each tree or closing-link radius fits the equal share of the total gap budget.
Hastings, arXiv:cond-mat/0508554v3, lines 709–720. -/
theorem hierarchyWindowRadius_le_quarter_gap_div {h m : ℕ} (hh : 2 ≤ h) (hm : m ≤ h)
    {J Δ K r : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) (hK0 : 0 ≤ K)
    (hr : hierarchyProjectionLength h J Δ ≤ r) (hK : K ≤ J * r) :
    hierarchyWindowRadius K r h m ≤ Δ / (4 * (2 : ℝ) ^ h) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpos := (closing_threshold_lt_hierarchyProjectionLength hh J Δ).trans_le hr
  have hr0 : 0 ≤ r := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (h : ℝ) + 1) hlog.le]
  have hE := hierarchyWindowEnergy_le_quarter_gap hh hJ hΔ hr hK
  have hN : 0 < (2 : ℝ) ^ h := pow_pos (by norm_num) h
  rw [div_mul_eq_div_div]
  apply (le_div_iff₀ hN).mpr
  calc
    _ ≤ (9 * K * Real.exp (-r / (4 * (h : ℝ)))) * (2 : ℝ) ^ h :=
      mul_le_mul_of_nonneg_right (hierarchyWindowRadius_le hK0 hr0 hh hm) hN.le
    _ ≤ Δ / 4 := by nlinarith

/-- The sum over the binary tree has at most `2^h - 1` times a bound for each entry. -/
theorem hierarchySum_le_const (f : ℕ → ℕ → ℝ) (B : ℝ) (h k : ℕ)
    (hf : ∀ m < h, ∀ j, f m j ≤ B) :
    hierarchySum f h k ≤ ((2 : ℝ) ^ h - 1) * B := by
  suffices hbound : ∀ n, n ≤ h → ∀ j,
      hierarchySum f n j ≤ ((2 : ℝ) ^ n - 1) * B from hbound h le_rfl k
  intro n
  induction n with
  | zero => intro _ j; simp
  | succ n ih =>
    intro hn j
    have hleft := ih (by omega) (2 * j)
    have hright := ih (by omega) (2 * j + 1)
    have htop := hf n (by omega) j
    rw [hierarchySum_succ, pow_succ]
    nlinarith

/-- All tree radii and the closing-link radius obey the common energy envelope.
Hastings, arXiv:cond-mat/0508554v3, lines 709–720, with the periodic closing window. -/
theorem hierarchySum_windowRadius_add_le {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    {h : ℕ} (hh : 2 ≤ h) (k : ℕ) :
    hierarchySum (fun m _ ↦ hierarchyWindowRadius K r h m) h k +
        hierarchyWindowRadius K r h h ≤
      9 * (2 : ℝ) ^ h * K * Real.exp (-r / (4 * (h : ℝ))) := by
  let B := 9 * K * Real.exp (-r / (4 * (h : ℝ)))
  have hsum := hierarchySum_le_const (fun m _ ↦ hierarchyWindowRadius K r h m) B h k
    (fun m hm _ ↦ hierarchyWindowRadius_le hK hr hh (Nat.le_of_lt hm))
  have hclose := hierarchyWindowRadius_le hK hr hh (le_refl h)
  calc
    _ ≤ ((2 : ℝ) ^ h - 1) * B + B := add_le_add hsum hclose
    _ = _ := by dsimp [B]; ring

/-- The chosen logarithmic length puts the tree and closing-link radii below `Δ/4`.
Hastings, arXiv:cond-mat/0508554v3, lines 709–720. -/
theorem hierarchySum_windowRadius_add_le_quarter_gap {h : ℕ} (hh : 2 ≤ h)
    {J Δ K r : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) (hK0 : 0 ≤ K)
    (hr : hierarchyProjectionLength h J Δ ≤ r) (hK : K ≤ J * r) (k : ℕ) :
    hierarchySum (fun m _ ↦ hierarchyWindowRadius K r h m) h k +
      hierarchyWindowRadius K r h h ≤ Δ / 4 := by
  have hr0 : 0 ≤ r := (by positivity : 0 ≤ 512 * (h : ℝ) ^ 2).trans
    ((hierarchyProjectionLength_ge_square h J Δ).trans hr)
  exact (hierarchySum_windowRadius_add_le hK0 hr0 hh k).trans
    (hierarchyWindowEnergy_le_quarter_gap hh hJ hΔ hr hK)

/-- The same chosen length controls the total exponentially small truncation error.
The constant in the local residual bound is absorbed into `J`.
Hastings, arXiv:cond-mat/0508554v3, lines 709–720. -/
theorem hierarchyTruncationError_le_eighth_gap {h : ℕ} (hh : 2 ≤ h)
    {J Δ r : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength h J Δ ≤ r) :
    (2 : ℝ) ^ h * J * Real.exp (-r) ≤ Δ / 8 := by
  have hH : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hr2 : 2 ≤ r := by
    have := (hierarchyProjectionLength_ge_square h J Δ).trans hr
    nlinarith [sq_nonneg ((h : ℝ) - 1)]
  have hbudget : 2 * J / 9 ≤ J * r := by
    nlinarith [mul_nonneg hJ.le (by linarith : 0 ≤ r - 2 / 9)]
  have hE := hierarchyWindowEnergy_le_quarter_gap hh hJ hΔ hr hbudget
  have hexp : Real.exp (-r) ≤ Real.exp (-r / (4 * (h : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    apply neg_le_neg
    rw [div_le_iff₀ (by positivity : 0 < 4 * (h : ℝ))]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * (h : ℝ) - 1) (by linarith : 0 ≤ r)]
  calc
    _ ≤ (2 : ℝ) ^ h * J * Real.exp (-r / (4 * (h : ℝ))) := by gcongr
    _ ≤ Δ / 8 := by nlinarith

end TNLean.MPS.AreaLaw.LocalSolution
