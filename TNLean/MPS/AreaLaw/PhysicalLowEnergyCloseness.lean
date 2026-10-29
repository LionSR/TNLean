/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FiveRegionTruncationResidual
import QICLean.Analysis.SpectralWindowCount

/-!
# Closeness at shifted physical low-energy cutoffs

The actual five-region truncation residual gives one-sided closeness at
shifted spectral cutoffs, in both directions. The energy bandwidth is
arbitrary and no ground-space gap is assumed. These are supporting physical
comparisons for ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 927–969,
and Theorem `t:aisgapless`, lines 1027–1041. The clipping threshold is
selected from the requested accuracy and positive cutoff shift; no numerical
smallness condition is supplied. The low-density bootstrap is separate.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- A physical clipping threshold makes the residual meet any positive
shifted-cutoff accuracy budget. Auxiliary to ALVV, arXiv:1602.08828v2,
`lem:hard-trunc`, lines 955–968. -/
private theorem exists_low_energy_residual_threshold
    (eta w delta : ℝ) (heta : 0 ≤ eta) (hw : 0 < w) (hdelta : 0 < delta) :
    ∃ t : ℝ, t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (delta * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      let xi := (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)
      xi ≤ 1 ∧ 2 * (6 + eta) * xi ≤ delta * w ^ 2 := by
  let C := 288 * Real.exp (11 / 8)
  let z := min 1 (delta * w ^ 2 / (2 * (6 + eta)))
  have hden : 0 < 2 * (6 + eta) := by linarith only [heta]
  have hz : 0 < z := lt_min (by norm_num) (div_pos (by positivity) hden)
  have hz1 : z ≤ 1 := min_le_left _ _
  have hC1 : 1 ≤ C := by
    have he : 1 ≤ Real.exp (11 / 8) := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp only [C]
    linarith only [he]
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hquot : 1 ≤ C / z := (one_le_div hz).mpr (hz1.trans hC1)
  have hlog : 0 ≤ Real.log (C / z) := Real.log_nonneg hquot
  let t := 21 + eta + 8 * Real.log (C / z)
  have harg : -(t - eta) / 8 = -21 / 8 - Real.log (C / z) := by
    dsimp only [t]
    ring
  have htail : C * Real.exp (-(t - eta) / 8) ≤ z := by
    rw [harg, Real.exp_sub, Real.exp_log (div_pos hC hz)]
    have he : Real.exp (-21 / 8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have heq : C * (Real.exp (-21 / 8) / (C / z)) = Real.exp (-21 / 8) * z := by
      field_simp
    rw [heq]
    exact (mul_le_mul_of_nonneg_right he hz.le).trans_eq (one_mul z)
  refine ⟨t, rfl, by dsimp only [t]; linarith only [heta, hlog],
    by dsimp only [t]; linarith only [hlog], htail.trans hz1, ?_⟩
  have hsmall := (le_div_iff₀ hden).mp (min_le_right 1 (delta * w ^ 2 / (2 * (6 + eta))))
  exact (mul_le_mul_of_nonneg_left htail hden.le).trans (by nlinarith only [hsmall])

/-- Actual hard truncation gives closeness at shifted physical low-energy
cutoffs in both directions. The original centered ground energy and the
regional minima are constructed from the nearest-neighbour terms. There
is no spectral-gap, supplied-residual or numerical smallness hypothesis.
The threshold is chosen from the requested accuracy and cutoff shift.
This supports ALVV,
arXiv:1602.08828v2, `lem:hard-trunc`, lines 927–969, and Theorem
`t:aisgapless`, lines 1027–1041. This is not the low-density bootstrap. -/
theorem exists_five_region_physical_low_energy_closeness
    (L q a b ell : ℕ) (eta w delta : ℝ)
    (heta : 0 < eta) (hw : 0 < w) (hdelta : 0 < delta)
    (hq : 0 < q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b + 1) (hbL : b + 2 * ell ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B : ℝ → (Fin 5 → ℝ) → Finset (Fin 5) →
        Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun t e T ↦
      (∑ j, ((if j ∈ T then
        cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
          (e j : ℂ) • 1)) + Y
    ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
      t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (delta * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      Submodule.IsCloseTo delta
          (Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta + w))
          (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) ∧
        Submodule.IsCloseTo delta
          (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta + w))
          (Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta)) := by
  classical
  intro k A Cross Y K B
  obtain ⟨t, htformula, ht, hcut, hxi1, hsmall⟩ :=
    exists_low_energy_residual_threshold eta w delta heta.le hw hdelta
  let xi := (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, hres⟩ :=
    exists_five_region_physical_truncation_residual L q a b ell t
      hq hell ht hab hbL h hs h0 h1
  have hA (j : Fin 5) : (A j).IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have he (j : Fin 5) : (e j : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A j :=
    Matrix.le_iff.mpr (hlo j)
  have hY : Y.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ ↦ h0 i)
  have hpos (T : Finset (Fin 5)) : (B t e T).PosSemidef := by
    obtain ⟨hX, _⟩ := Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t T hA he x hx (by linarith only [ht])
    exact hX.add hY
  let hO := (hpos ∅).isHermitian
  let hC := (hpos K).isHermitian
  refine ⟨t, e, E0, x, z, hO, hC, htformula, ht, hcut, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, ?_⟩
  let I := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
  have hxi : 0 < xi := by dsimp only [xi]; positivity
  have heigen (T : Finset (Fin 5)) (j : Fin L → Fin q) :
      I (B t e T) ((hpos T).isHermitian.eigenvectorBasis j) =
        ((hpos T).isHermitian.eigenvalues j : ℂ) •
          (hpos T).isHermitian.eigenvectorBasis j := by
    apply (WithLp.ofLp_injective 2)
    simpa only [I, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, Complex.coe_smul]
      using (hpos T).isHermitian.mulVec_eigenvectorBasis j
  have hwindow := Real.spectral_window_budget_bound E0 eta xi w delta hE0 hE04 heta.le
    hxi hxi1 hw.le hdelta.le hsmall
  have hbudget :
      (⌈(E0 + eta - 0) / (2 * xi)⌉₊ : ℝ) * (xi + xi) ^ 2 ≤
        delta * (E0 + eta + w - (E0 + eta) + xi) ^ 2 := by
    simpa only [sub_zero, add_sub_cancel_left] using hwindow
  have hres0 := hres ∅ eta heta.le hcut hO.eigenvectorBasis hO.eigenvalues (heigen ∅)
  have hresC := hres K eta heta.le hcut hC.eigenvectorBasis hC.eigenvalues (heigen K)
  have hpert0 (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : v ∈ Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) :
      ‖I (B t e ∅) v - I (B t e K) v‖ ≤ xi * ‖v‖ := by
    have hvbound := ((I (B t e ∅ - B t e K)).domRestrict
      (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta))).le_of_opNorm_le
        hres0 ⟨v, hv⟩
    rw [map_sub] at hvbound
    change ‖I (B t e ∅) v - I (B t e K) v‖ ≤ xi * ‖v‖ at hvbound
    exact hvbound
  have hpertC (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : v ∈ Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta)) :
      ‖I (B t e K) v - I (B t e ∅) v‖ ≤ xi * ‖v‖ := by
    have hvbound := ((I (B t e ∅ - B t e K)).domRestrict
      (Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta))).le_of_opNorm_le
        hresC ⟨v, hv⟩
    rw [map_sub] at hvbound
    change ‖I (B t e ∅) v - I (B t e K) v‖ ≤ xi * ‖v‖ at hvbound
    rwa [norm_sub_rev]
  constructor
  · exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      hO.eigenvectorBasis hC.eigenvectorBasis hO.eigenvalues hC.eigenvalues
      (heigen ∅) (heigen K) hpert0 hxi
      (fun j _ ↦ (hpos ∅).eigenvalues_nonneg j) (by linarith only [hE0, heta])
      (by linarith only [hw]) hbudget
  · exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      hC.eigenvectorBasis hO.eigenvectorBasis hC.eigenvalues hO.eigenvalues
      (heigen K) (heigen ∅) hpertC hxi
      (fun j _ ↦ (hpos K).eigenvalues_nonneg j) (by linarith only [hE0, heta])
      (by linarith only [hw]) hbudget

end TNLean.MPS.AreaLaw
