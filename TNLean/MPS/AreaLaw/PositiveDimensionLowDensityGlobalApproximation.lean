/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLowDensityGlobalApproximation

/-!
# Strict global low-energy MPS approximation in positive local dimension

For the scalar local space, the original unit vector already has a bond-one
representation. For local dimension at least two, retain the same actual
sequential projection construction at half the requested accuracy. The one
bond factor is still chosen before the vector. The strict overlap changes
only the fixed numerical factor inside the logarithm of the global accuracy.

This is the global approximation consequence of ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. Positive local
dimension is the qudit convention. The bandwidth is fixed before physical
data; the capped-width comparison is recorded in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every original buffered low-energy unit vector admits a strict-overlap
MPS approximation in every positive local dimension. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. The global accuracy
logarithm contains the explicit fixed factor 32. -/
theorem exists_fixed_bandwidth_low_energy_strict_isOpenMPS_approximation
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
      let b := 16 + Real.log (1 / g) + Real.log (32 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ (G etaLD) * B) (fun x ↦ Φ x) ∧
        1 - delta < ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 4 := by
  classical
  obtain ⟨K, hK, hactual⟩ :=
    exists_fixed_bandwidth_low_energy_normalized_isOpenMPS_approximation etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q v hq hv h hs h0 h1 config H hH G bcap g u delta hdelta hdelta1 b
  by_cases hq2 : 2 ≤ q
  · obtain ⟨B, hB, hlogB, hvec⟩ :=
      hactual L q v hq2 hv h hs h0 h1
        (delta / 2) (by positivity) (by linarith only [hdelta1])
    have hscale : 16 * ((L : ℝ) + 1) / (delta / 2) =
        32 * ((L : ℝ) + 1) / delta := by field_simp; ring
    rw [hscale] at hlogB
    refine ⟨B, hB, hlogB, ?_⟩
    intro ψ hψG hψ
    obtain ⟨Φ, hΦ, hmps, hoverlap, hdist⟩ := hvec ψ hψG hψ
    refine ⟨Φ, hΦ, hmps, by linarith only [hoverlap, hdelta], ?_⟩
    linarith only [hdist]
  · have hq1 : q = 1 := by omega
    subst q
    let : Nonempty (Fin L → Fin 1) := config
    have hg : 0 < g := lt_min (by dsimp only [bcap]; positivity) (by norm_num)
    have hg1 : g ≤ 1 := min_le_right _ _
    have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
    have hu : 0 ≤ u := by
      simp only [u, Nat.cast_one, Real.log_one, add_zero]
      linarith only [hlogg]
    have hden : delta ≤ 32 * ((L : ℝ) + 1) := by
      have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith only [hdelta1, hL]
    have hlogdelta : 0 ≤ Real.log (32 * ((L : ℝ) + 1) / delta) :=
      Real.log_nonneg ((one_le_div hdelta).2 hden)
    have hb : 1 ≤ b := by dsimp only [b]; linarith only [hlogg, hlogdelta]
    have hP : 0 ≤ 1 + Real.log b := by linarith only [Real.log_nonneg hb]
    have hcost : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) := by positivity
    refine ⟨1, le_rfl, ?_, ?_⟩
    · simpa only [Nat.cast_one, Real.log_one] using hcost
    · intro ψ _hψG hψ
      have hminspec : minEigenvalue hH ∈ spectrum ℝ H := by
        obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
        rw [← hi]
        exact hH.eigenvalues_mem_spectrum_real i
      have hGne : G etaLD ≠ ⊥ :=
        hH.spectralSpanLE_ne_bot_of_mem_spectrum hminspec (by linarith only [hLD])
      have hrG : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr hGne
      have hmps : IsOpenMPS L 1 (Module.finrank ℂ (G etaLD) * 1) (fun x ↦ ψ x) := by
        apply isOpenMPS_of_cutMatrix_rank_le ψ
        intro k
        have hrank := Matrix.rank_le_card_height (cutMatrix ψ k)
        have hcard : Fintype.card (Entropy.RegionConfig (fun _ : Fin L ↦ 1)
            (leftBlock L k)) = 1 := by simp [Entropy.RegionConfig]
        rw [hcard] at hrank
        simpa only [mul_one] using hrank.trans hrG
      refine ⟨ψ, hψ, hmps, ?_, ?_⟩
      · have hi : ‖⟪ψ, ψ⟫_ℂ‖ = 1 := by norm_num [inner_self_eq_norm_sq_to_K, hψ]
        rw [hi]
        linarith only [hdelta]
      · simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        positivity

end TNLean.MPS.AreaLaw
