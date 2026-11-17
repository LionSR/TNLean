/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLowDensitySharpApproximation
import TNLean.MPS.AreaLaw.NormalizedSequentialApproximation
import QICLean.Analysis.LogRankRounding
import QICLean.Analysis.ViableSubspaceEntropy
import QICLean.Channel.MaximalOverlap

/-!
# One sharp matrix product approximation to an original low-energy vector

The fixed-cut approximants control the discarded mass of the actual original
marginals. One sequential product of their leading spectral projections is
then normalized. The resulting vector has simultaneous bond control at all
cuts, with the same three-quarter power of the logarithmic accuracy as the
fixed-cut estimate. The coefficient of the logarithm of the full low-energy
dimension is one.

This supports ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105.
No spectral gap or invariance of an original band is assumed.

**Scope restriction (physical intervals and fixed bandwidth):** The theorem
retains `q ≥ 2` and a coefficient for each fixed positive bandwidth. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`. The effective width is
capped explicitly; the source comparison uses `0 < v ≤ etaLD`.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every original buffered low-energy unit vector has one normalized
sequential MPS approximation, with the sharp logarithmic accuracy exponent
and one full-band multiplicity factor. ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_low_energy_normalized_isOpenMPS_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ) (v : ℝ) (hq : 2 ≤ q), 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c)
      let bcap := min v (etaLD / 2)
      let g := min (bcap / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let b := 16 + Real.log (1 / g) + Real.log (16 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ (G etaLD) * B) (fun x ↦ Φ x) ∧
        1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  obtain ⟨K, hK, hfixed⟩ :=
    exists_fixed_bandwidth_interval_low_energy_normalized_approximation etaLD hLD
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro L q v hq hv h hs h0 h1 config H hH G bcap g u
  let : Nonempty (Fin L → Fin q) := config
  have hg : 0 < g := lt_min (by dsimp only [bcap]; positivity) (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hminspec : minEigenvalue hH ∈ spectrum ℝ H := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
    rw [← hi]
    exact hH.eigenvalues_mem_spectrum_real i
  have hGne : G etaLD ≠ ⊥ :=
    hH.spectralSpanLE_ne_bot_of_mem_spectrum hminspec (by linarith only [hLD])
  have hrG : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr hGne
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  intro delta hdelta hdelta1 b
  let deltaCut := delta / (16 * ((L : ℝ) + 1))
  have hden : 0 < 16 * ((L : ℝ) + 1) := by positivity
  have hcut : 0 < deltaCut := div_pos hdelta hden
  have hcut1 : deltaCut ≤ 1 := by
    apply (div_le_iff₀ hden).2
    have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith only [hdelta1, hL]
  have hrecip : 1 / deltaCut = 16 * ((L : ℝ) + 1) / delta := by
    dsimp only [deltaCut]
    field_simp
  have hb : 16 ≤ b := by
    have hlogcut := Real.log_nonneg ((one_le_div hcut).2 hcut1)
    rw [hrecip] at hlogcut
    dsimp only [b]
    linarith only [hlogg, hlogcut]
  let F := u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u
  have hbase : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith only [hu3, hg1])
  have hroot : 0 ≤ (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by positivity
  have hsum : 1 ≤ u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by
    linarith only [hbase, hroot]
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by linarith only [hb])
  have hF : 1 ≤ F := hsum
  have hPone : 1 ≤ 1 + Real.log b := by linarith only [hlogb]
  have hFP : 1 ≤ F * (1 + Real.log b) := by
    simpa only [one_mul] using
      (mul_le_mul hF hPone (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hF))
  let E := K * F * (1 + Real.log b)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg hK.le (zero_le_one.trans hF))
    (zero_le_one.trans hPone)
  let B : ℕ := ⌈Real.exp E⌉₊
  obtain ⟨hB, hlogB⟩ := Real.log_ceil_exp_le_add_one E hE
  refine ⟨B, hB, ?_, ?_⟩
  · change Real.log (B : ℝ) ≤ (K + 1) * F * (1 + Real.log b)
    change Real.log (B : ℝ) ≤ E + 1 at hlogB
    dsimp only [E] at hlogB
    nlinarith only [hlogB, hFP]
  · intro ψ hψG hψ
    have htail : ∀ k ∈ Finset.Ico 1 L,
        1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
          (leftBlock L k) ψ).kyFanNorm (Module.finrank ℂ (G etaLD) * B) ≤
            delta / (8 * ((L : ℝ) + 1)) := by
      intro k hk
      have hkL : k ≤ L := (Finset.mem_Ico.mp hk).2.le
      obtain ⟨φ, hφ, hoverlap, hlogrank⟩ :=
        hfixed L q 0 k v hq (Nat.zero_le k) hkL hv h hs h0 h1
          deltaCut hcut hcut1 ψ hψG hψ
      rw [hrecip] at hlogrank
      have hregional := one_sub_regional_kyFanNorm_le_twice_error
        (interval L 0 k) ψ φ hφ deltaCut hcut1 (Module.finrank ℂ (G etaLD) * B)
        (Nat.le_mul_ceil_exp_of_log_le hrG E hlogrank) hoverlap
      rw [leftBlock_eq_interval]
      convert hregional using 1
      dsimp only [deltaCut]
      field_simp; ring
    exact exists_unit_mps_of_uniform_prefix_mass ψ hψ (Module.finrank ℂ (G etaLD) * B)
      delta hdelta hdelta1 htail

end TNLean.MPS.AreaLaw
