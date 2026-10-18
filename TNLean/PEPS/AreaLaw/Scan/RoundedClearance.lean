/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs
import TNLean.PEPS.AreaLaw.WeakRectangleShellSafety
import TNLean.Algebra.ExplicitThresholds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rounded scales for safe rectangle shells

For fixed positive row-scale multiplier and collar exponent in `(0, 1)`,
the rounded collar and logarithmic truncation radius are sublinear in the
parent rectangle size. One threshold works for every positive safety
parameter and every physical instance. Selected dyadic shell cells inherit
native rectangle safety. The dyadic cap exponent is not the scanner band count.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, proof of Proposition 9.5, `08-scanner.tex`, lines 707–729,
and `scanner:scales` / `scanner:test-geometry`, lines 32–49, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original proof from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold of the rounded clearance budgets: `s` must be at least one and
`C₂ s` must be at least `80 (C₂ + 1)` and the thresholds for `4 n^(1 - ell) ≤ η n` and
`20 Cr (log n)² ≤ η n`, where `η = 1 / (4 (C₂ + 1))`. Source: Proposition 9.5,
`08-scanner.tex`, lines 707–729. -/
noncomputable def roundedClearanceThreshold (C₂ Cr ell : ℝ) : ℕ :=
  max 1 ⌈max (Real.powerRatioThreshold 4 (1 / (4 * (C₂ + 1))) ell)
    (max (Real.logPowThreshold (20 * Cr) (1 / (4 * (C₂ + 1))) 1 2) (80 * (C₂ + 1))) / C₂⌉₊

/-- Rounded collar and truncation scales satisfy the safe-box and scanner clearance budgets at
every size `s` from the explicit threshold `roundedClearanceThreshold C₂ Cr ell` on, for every
positive safety parameter. Source: Proposition 9.5, `08-scanner.tex`, lines 707–729. -/
theorem rounded_clearance_of_threshold_le {C₂ Cr ell : ℝ}
    (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) (hell : 0 < ell) (hell1 : ell < 1) {s : ℕ}
    (hs : roundedClearanceThreshold C₂ Cr ell ≤ s) :
    let n := ⌈C₂ * s⌉₊
    let L := ⌊(n : ℝ) ^ (1 - ell)⌋₊
    let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
    1 ≤ L ∧ L ≤ s ∧ ∀ D₀ : ℕ, 1 ≤ D₀ →
      (D₀ + 1) * L ≤ D₀ * s ∧ 2 * L + 10 * r₀ ≤ D₀ * s := by
  intro n L r₀
  set η : ℝ := 1 / (4 * (C₂ + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hscale := Nat.ceil_le.mp ((le_max_right _ _).trans hs)
  rw [div_le_iff₀ hC₂] at hscale
  have hx : max (Real.powerRatioThreshold 4 η ell)
      (max (Real.logPowThreshold (20 * Cr) η 1 2) (80 * (C₂ + 1))) ≤ n :=
    (hscale.trans_eq (mul_comm _ _)).trans (Nat.le_ceil _)
  simp only [max_le_iff] at hx
  obtain ⟨hxp, hxl, hx80⟩ := hx
  have hn1 : (1 : ℝ) ≤ n := (Real.one_le_powerRatioThreshold _ _ _).trans hxp
  have hn0 : 0 < (n : ℝ) := one_pos.trans_le hn1
  have hpow := Real.mul_rpow_le_mul_rpow_of_powerRatioThreshold_le (C := 4) (b := 1) (x := n)
    (by norm_num) hη (sub_lt_self 1 hell) (by rw [sub_sub_cancel]; exact hxp)
  have hlog := Real.mul_log_pow_le_mul_rpow_of_logPowThreshold_le
    (mul_nonneg (by norm_num) hCr) hη one_pos hxl
  rw [Real.rpow_one] at hpow hlog
  have h20 : 20 ≤ η * n := by
    rw [hη_def, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  have hnupper : (n : ℝ) ≤ (C₂ + 1) * s := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ C₂ * s by positivity)).le
    have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    dsimp [n]
    nlinarith
  have htotal : 4 * (n : ℝ) ^ (1 - ell) + 20 * (Cr * Real.log n ^ 2 + 1) < s := by
    have hηn : 3 * (η * n) < (n : ℝ) / (C₂ + 1) := by
      rw [hη_def, lt_div_iff₀ (by positivity)]
      field_simp
      nlinarith
    have h := (div_le_iff₀' (show 0 < C₂ + 1 by positivity)).mpr hnupper
    linarith
  have hLupper : (L : ℝ) ≤ (n : ℝ) ^ (1 - ell) := Nat.floor_le (by positivity)
  have hrupper : (r₀ : ℝ) ≤ Cr * Real.log n ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hbudget : 4 * L + 20 * r₀ < s := by
    have h : (4 : ℝ) * L + 20 * r₀ < s := by linarith
    exact_mod_cast h
  have hLone : 1 ≤ L := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - ell) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by linarith)
    exact Nat.le_floor (by exact_mod_cast h1)
  refine ⟨hLone, by omega, ?_⟩
  intro D₀ hD₀
  have htwo : 2 * L ≤ s := by omega
  have hmul := Nat.mul_le_mul_left D₀ htwo
  have hside : L ≤ D₀ * L := Nat.le_mul_of_pos_left L hD₀
  have hsafety : s ≤ D₀ * s := Nat.le_mul_of_pos_left s hD₀
  constructor <;> nlinarith

/-- Rounded collar and truncation scales satisfy the safe-box and scanner
clearance budgets eventually. The threshold precedes the safety parameter.
Source: Proposition 9.5, `08-scanner.tex`, lines 707–729. -/
theorem exists_rounded_clearance_threshold {C₂ Cr ell : ℝ}
    (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) (hell : 0 < ell) (hell1 : ell < 1) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ s : ℕ, S ≤ s →
      let n := ⌈C₂ * s⌉₊
      let L := ⌊(n : ℝ) ^ (1 - ell)⌋₊
      let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
      1 ≤ L ∧ L ≤ s ∧ ∀ D₀ : ℕ, 1 ≤ D₀ →
        (D₀ + 1) * L ≤ D₀ * s ∧ 2 * L + 10 * r₀ ≤ D₀ * s :=
  ⟨_, le_max_left _ _, fun _ ↦ rounded_clearance_of_threshold_le hC₂ hCr hell hell1⟩

/-- The rounded clearance budgets at the scanner's actual collar scale, at every size from the
explicit threshold `roundedClearanceThreshold C₂ Cr X.ell` on. Source: Proposition 9.5,
`08-scanner.tex`, lines 707–729. -/
theorem ScannerExponents.rounded_clearance_of_threshold_le (X : ScannerExponents)
    {C₂ Cr : ℝ} (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) {s : ℕ}
    (hs : roundedClearanceThreshold C₂ Cr X.ell ≤ s) :
    let n := ⌈C₂ * s⌉₊
    let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
    1 ≤ X.L n ∧ X.L n ≤ s ∧ ∀ D₀ : ℕ, 1 ≤ D₀ →
      (D₀ + 1) * X.L n ≤ D₀ * s ∧ 2 * X.L n + 10 * r₀ ≤ D₀ * s :=
  Scan.rounded_clearance_of_threshold_le hC₂ hCr X.ell_pos X.ell_lt_one hs

/-- The rounded clearance theorem uses the scanner's actual collar scale;
it imposes no condition on the scanner band count. Source: Proposition 9.5,
`08-scanner.tex`, lines 707–729. -/
theorem ScannerExponents.exists_rounded_clearance_threshold (X : ScannerExponents)
    {C₂ Cr : ℝ} (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ s : ℕ, S ≤ s →
      let n := ⌈C₂ * s⌉₊
      let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
      1 ≤ X.L n ∧ X.L n ≤ s ∧ ∀ D₀ : ℕ, 1 ≤ D₀ →
        (D₀ + 1) * X.L n ≤ D₀ * s ∧ 2 * X.L n + 10 * r₀ ≤ D₀ * s :=
  Scan.exists_rounded_clearance_threshold hC₂ hCr X.ell_pos X.ell_lt_one

open TNLean.PEPS.AreaLaw.Geometry

/-- One rounded-scale threshold gives scanner clearance and safe actual shell
cells uniformly in the domain, cut, safety parameter and parent rectangle.
Source: Proposition 9.5, `08-scanner.tex`, lines 707–729. -/
theorem exists_safe_shell_cells_of_rounded_scales (X : ScannerExponents)
    {C₂ Cr : ℝ} (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ))
      (D₀ : ℕ), 1 ≤ D₀ → ∀ Q : IntRect, S ≤ Q.size → IsSafe Λ A D₀ Q →
      let n := ⌈C₂ * Q.size⌉₊
      let L := X.L n
      let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
      1 ≤ L ∧ L ≤ Q.size ∧
      (∀ e ∈ edgeBoundary Λ A, ∀ z ∈ e, ∀ p ∈ Q.toFinset,
        2 * L + 10 * r₀ < supDist p z.1) ∧
      ∀ j Kcap : ℕ, j ≤ L → 2 ^ Kcap ≤ L → ∀ k z,
        (k, z) ∈ cappedDyadicPartition ((Q.dilate j).toFinset \ Q.toFinset) Kcap →
        IsSafe Λ A D₀ (latticeDyadicRect k z) := by
  obtain ⟨S, hS, h⟩ := X.exists_rounded_clearance_threshold hC₂ hCr
  refine ⟨S, hS, ?_⟩
  intro Λ A D₀ hD₀ Q hQ hsafe
  obtain ⟨hLone, hLsize, hbudgets⟩ := h Q.size hQ
  obtain ⟨hbudget, hclear⟩ := hbudgets D₀ hD₀
  refine ⟨hLone, hLsize, ?_, ?_⟩
  · intro e he z hz p hp
    exact hclear.trans_lt (hsafe e he z hz p hp)
  · intro j Kcap hj hcap k z hcell
    exact hsafe.isSafe_cappedDyadicPartition_shell j _ Kcap k z hj hcap
      ((add_one_mul D₀ _).symm.trans_le hbudget) hcell

end TNLean.PEPS.AreaLaw.Scan
