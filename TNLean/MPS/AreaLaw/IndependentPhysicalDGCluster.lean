/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FiveRegionTruncationResidual
import TNLean.MPS.AreaLaw.IndependentTruncationParameters

/-!
# Physical low clusters with independent approximation scales

A single universal constant chooses a logarithmic hard-truncation threshold.
The integer window length has an inverse-gap term and a fourth-root term.
The full original ground space and the actual clipped Hamiltonian are retained.
This is the five-region analytical construction supporting ALVV,
arXiv:1602.08828v2, Corollary 4.6 (`c:goodagsphardtrunc`) and the proof of
Theorem 4.9 (`thm:al-dg`, source line 1080). Polynomial operator families and
approximating vectors still require a separate construction at these parameters.

**Local fix (parameter choice):** The independent scales replace the printed
prescription that fails to provide uniform accuracy in the gap; see
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- One universal constant supplies the physical low cluster at every
projection accuracy, with a fourth-root window bound and a uniform filter
exponent. The original regional minima and spectral data are derived from
the supported nearest-neighbour terms. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary 4.6 and Theorem 4.9, proof line 1080. -/
theorem exists_independent_physical_dg_cluster_parameters :
    ∃ C : ℝ, 21 ≤ C ∧
      ∀ g tau : ℝ, 0 < g → g ≤ 1 → 0 < tau → tau ≤ 1 →
      let u := 1 + Real.log (1 / g) + Real.log (1 / tau)
      let t := C * u
      ∃ ell : ℕ, 1 ≤ ell ∧
      (ell : ℝ) ≤ 8 / (4 * g / 5) +
        (7 * C) ^ (1 / 4 : ℝ) * (1 / (4 * g / 5)) ^ (1 / 4 : ℝ) *
          u ^ (3 / 4 : ℝ) ∧
      (∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
        u ≤ (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R)) ∧
      ∀ (L q a b : ℕ), 0 < q → a + 2 * ell ≤ b + 1 → b + 2 * ell ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1)
    (mu : ℝ),
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    mu ∈ spectrum ℝ H →
    (∀ r ∈ spectrum ℝ H, r = mu ∨ mu + g ≤ r) →
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ),
      let S := ∑ j, e j
      let K : Finset (Fin 5) := {0, 2, 4}
      let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        (∑ j, ((if j ∈ K then
          cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + S = mu ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧ ‖B‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      ∃ (v : OrthonormalBasis (Fin L → Fin q) ℂ
          (EuclideanSpace ℂ (Fin L → Fin q))) (lam : (Fin L → Fin q) → ℝ),
        (∀ j, ι B (v j) = (lam j : ℂ) • v j) ∧
        let T := Submodule.spectralSpanLE v lam (E0 + g / 10)
        T = Submodule.spectralSpanLE v lam (E0 + 9 * g / 10) ∧
        (∀ tau : ℝ, E0 + g / 20 ≤ tau → tau ≤ E0 + 19 * g / 20 →
          Submodule.spectralSpanLE v lam tau = T) ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
        Submodule.IsCloseTo (tau / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (tau / 200 : ℝ) G T ∧
        ∀ j, lam j ≤ E0 + g / 10 ∨ E0 + 9 * g / 10 ≤ lam j := by
  obtain ⟨C, hC, hthreshold⟩ := Real.exists_independent_truncation_threshold_constant
  refine ⟨C, hC, ?_⟩
  intro g tau hg hg1 htau htau1 u t
  have hu : 0 ≤ u := by
    have hlogg := Real.log_nonneg ((one_le_div hg).2 hg1)
    have hlogtau := Real.log_nonneg ((one_le_div htau).2 htau1)
    dsimp only [u]
    linarith only [hlogg, hlogtau]
  obtain ⟨ell, hell, hbound, hfilter⟩ :=
    Real.exists_quarter_power_truncation_filter_scale C (4 * g / 5) u
      (by linarith only [hC]) (by linarith only [hg]) (by linarith only [hg1]) hu
  obtain ⟨ht, htail⟩ := hthreshold g tau hg hg1 htau htau1
  refine ⟨ell, hell, hbound, hfilter, ?_⟩
  intro L q a b hq hab hbL h hs h0 h1 mu H hH G hmu hgap k A J Y
  exact exists_five_region_physical_scaled_low_cluster L q a b ell t hq hell ht hab hbL
    h hs h0 h1 mu g (tau * g / 1000000) tau hg hg1 htau htau1 htail le_rfl hmu hgap

end TNLean.MPS.AreaLaw
