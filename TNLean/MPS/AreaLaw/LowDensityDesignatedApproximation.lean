/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PositiveDimensionLowDensityApproximation
import TNLean.MPS.AreaLaw.DesignatedCutTruncation
import QICLean.Analysis.LogRankRounding

/-!
# One low-energy approximant with a sharp designated cut and global MPS bounds

The designated cut uses a constant fraction of the error budget; all other
cuts share a length-dependent budget. Their actual leading marginal
projections form one sequential product. Normalizing that product retains
both the sharper designated-cut rank and the global matrix product bound.

This proves the simultaneous-witness approximation conclusion of ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105, in positive
local dimension. The bandwidth is fixed as in Assumption (LD), lines
281–284. All original-band comparisons and polynomial-family bounds are
derived physically by the imported fixed-cut theorem; no raw-band gap or
invariance is assumed. The capped-width comparison is documented in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- One actual normalized sequential MPS satisfies the sharp rank bound at
any designated cut and the global bond bound simultaneously. Both integer
factors are chosen before the designated cut and vector. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_low_energy_designated_isOpenMPS_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ) (v : ℝ) (hq : 0 < q), 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, hq⟩⟩
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c)
      let bcap := min v (etaLD / 2)
      let g := min (bcap / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (128 / delta)
      let b := 16 + Real.log (1 / g) + Real.log (128 * ((L : ℝ) + 1) / delta)
      ∃ Bs Bg : ℕ, 1 ≤ Bs ∧ Bs ≤ Bg ∧
        Real.log (Bs : ℝ) ≤
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) ∧
        Real.log (Bg : ℝ) ≤
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log b) ∧
      ∀ (k0 : ℕ) (ψ : EuclideanSpace ℂ (Fin L → Fin q)),
        ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ (G etaLD) * Bg) (fun x ↦ Φ x) ∧
        (cutMatrix Φ k0).rank ≤ Module.finrank ℂ (G etaLD) * Bs ∧
        1 - delta < ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  obtain ⟨K, hK, hfixed⟩ :=
    exists_fixed_bandwidth_interval_low_energy_strict_approximation etaLD hLD
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro L q v hq hv h hs h0 h1 config H hH G bcap g u
  let : Nonempty (Fin L → Fin q) := config
  have hg : 0 < g := lt_min (by dsimp only [bcap]; positivity) (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogg, hlogq]
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hX : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith only [hu3, hg1])
  have hminspec : minEigenvalue hH ∈ spectrum ℝ H := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
    rw [← hi]
    exact hH.eigenvalues_mem_spectrum_real i
  have hrG : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hminspec (by linarith only [hLD]))
  intro delta hdelta hdelta1 a b
  let F : ℝ → ℝ := fun x ↦ K *
    (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u) * (1 + Real.log x)
  have hF0 {x : ℝ} (hx : 1 ≤ x) : 0 ≤ F x := by
    have hP : 0 ≤ 1 + Real.log x := by linarith only [Real.log_nonneg hx]
    dsimp only [F]
    positivity
  have hFmono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : F x ≤ F y := by
    have hy : 1 ≤ y := hx.trans hxy
    have hpow := Real.rpow_le_rpow (zero_le_one.trans hx) hxy (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have hlog := Real.log_le_log (zero_lt_one.trans_le hx) hxy
    have hleft : u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u ≤
        u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ) * u := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (1 / g) ^ (1 / 4 : ℝ))) hu0
      linarith only [hm]
    have hPx : 0 ≤ 1 + Real.log x := by linarith only [Real.log_nonneg hx]
    have hY : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ) * u) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hleft hK.le)
      (by linarith only [hlog]) hPx hY
  have ha : 16 ≤ a := by
    have hl : 0 ≤ Real.log (128 / delta) :=
      Real.log_nonneg ((one_le_div hdelta).2 (by linarith only [hdelta1]))
    dsimp only [a]
    linarith only [hlogg, hl]
  have hab : a ≤ b := by
    have harg : 128 / delta ≤ 128 * ((L : ℝ) + 1) / delta :=
      div_le_div_of_nonneg_right
        (by nlinarith only [show 0 ≤ (L : ℝ) from Nat.cast_nonneg L]) hdelta.le
    have hl := Real.log_le_log (by positivity : 0 < 128 / delta) harg
    dsimp only [a, b]
    linarith only [hl]
  have hb : 16 ≤ b := ha.trans hab
  have hround {x : ℝ} (hx : 1 ≤ x) :
      1 ≤ ⌈Real.exp (F x)⌉₊ ∧ Real.log (⌈Real.exp (F x)⌉₊ : ℕ) ≤
        (K + 1) * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log x) := by
    obtain ⟨hB, hlog⟩ := Real.log_ceil_exp_le_add_one (F x) (hF0 hx)
    have hsum : 1 ≤ u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u := by
      have hy : 0 ≤ (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u := by positivity
      linarith only [hX, hy]
    have hP : 1 ≤ 1 + Real.log x := by linarith only [Real.log_nonneg hx]
    have hprod : 1 ≤ (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log x) := by
      simpa only [one_mul] using
        mul_le_mul hsum hP (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hsum)
    refine ⟨hB, ?_⟩
    dsimp only [F] at hlog
    nlinarith only [hlog, hprod]
  let Bs : ℕ := ⌈Real.exp (F a)⌉₊
  let Bg : ℕ := ⌈Real.exp (F b)⌉₊
  obtain ⟨hBs, hlogs⟩ := hround (show 1 ≤ a by linarith only [ha])
  obtain ⟨_hBg, hloggBound⟩ := hround (show 1 ≤ b by linarith only [hb])
  have hBsg : Bs ≤ Bg := Nat.ceil_mono
    (Real.exp_le_exp.mpr (hFmono (by linarith only [ha]) hab))
  refine ⟨Bs, Bg, hBs, hBsg, hlogs, hloggBound, ?_⟩
  intro k0 ψ hψG hψ
  have hmassAt (k : ℕ) (hkL : k ≤ L) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm
          (Module.finrank ℂ (G etaLD) *
            ⌈Real.exp (F (16 + Real.log (1 / g) + Real.log (2 / eps)))⌉₊) ≤ 2 * eps := by
    obtain ⟨φ, hφ, hoverlap, hlogrank⟩ :=
      hfixed L q 0 k v hq (Nat.zero_le k) hkL hv h hs h0 h1 eps heps heps1 ψ hψG hψ
    have hregional := one_sub_regional_kyFanNorm_le_twice_error
      (interval L 0 k) ψ φ hφ eps heps1
      (Module.finrank ℂ (G etaLD) *
        ⌈Real.exp (F (16 + Real.log (1 / g) + Real.log (2 / eps)))⌉₊)
      (Nat.le_mul_ceil_exp_of_log_le hrG _ hlogrank) hoverlap.le
    rw [leftBlock_eq_interval]
    exact hregional
  have hDs : 1 ≤ Module.finrank ℂ (G etaLD) * Bs := by
    simpa only [one_mul] using Nat.mul_le_mul hrG hBs
  apply exists_unit_mps_of_designated_prefix_mass ψ hψ k0
    (Module.finrank ℂ (G etaLD) * Bs) (Module.finrank ℂ (G etaLD) * Bg)
    hDs (Nat.mul_le_mul_left _ hBsg) delta hdelta hdelta1
  · intro hk0
    have hm := hmassAt k0 (Finset.mem_Ico.mp hk0).2.le (delta / 64)
      (by positivity) (by linarith only [hdelta1])
    have heq : 2 / (delta / 64) = 128 / delta := by field_simp; ring
    rw [heq] at hm
    change 1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
      (leftBlock L k0) ψ).kyFanNorm (Module.finrank ℂ (G etaLD) * Bs) ≤ _ at hm
    convert hm using 1; ring
  · intro k hk _hne
    have hden : 0 < 64 * ((L : ℝ) + 1) := by positivity
    have heps1 : delta / (64 * ((L : ℝ) + 1)) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith only [hdelta1, hL]
    have hm := hmassAt k (Finset.mem_Ico.mp hk).2.le
      (delta / (64 * ((L : ℝ) + 1))) (by positivity) heps1
    have heq : 2 / (delta / (64 * ((L : ℝ) + 1))) =
        128 * ((L : ℝ) + 1) / delta := by field_simp; ring
    rw [heq] at hm
    change 1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
      (leftBlock L k) ψ).kyFanNorm (Module.finrank ℂ (G etaLD) * Bg) ≤ _ at hm
    convert hm using 1; field_simp; ring

end TNLean.MPS.AreaLaw
