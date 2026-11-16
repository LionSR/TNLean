/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalScaledSoftTruncationResiduals
import QICLean.Analysis.SpectralResidualComparison
import QICLean.Analysis.SoftTruncationScaledAccuracy

/-!
# Directed physical soft spectral comparisons at prescribed accuracy

One logarithmic order is chosen before all chain and Hamiltonian data. The
two residuals, with their common regional minima, control the displacement
of the actual ground energies and both enlarged spectral windows. Neither
a residual estimate nor a spectral comparison is supplied as a hypothesis.

**Local fix (corrected residual comparison):** The scale is three times the order.
This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc` and
`lem:exp-approx`, lines 1178–1255. The bandwidth and enlargement are positive;
the source's printed first uniform energy estimate and its gap prescription
are not asserted. See
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A uniform explicit order gives both directed physical spectral comparisons
relative to the actual original and soft ground energies. Regional minima and
the actual ground data are constructed; no gap, residual, rank or closeness is
assumed. Corrected scale-three-times-order auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem exists_interval_physical_scaled_soft_low_energy_closeness
    (eta w delta : ℝ) (heta : 0 < eta) (hw : 0 < w) (hdelta : 0 < delta) :
    let rho := min 1 (min (w / 2) (delta * w ^ 2 / (2 * (eta + 2))))
    ∃ m : ℕ, m = ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * Real.log (80 / rho)⌉₊ ∧ 0 < m ∧
      ∀ (L q p r : ℕ) (hq : 0 < q) (_hpr : p ≤ r) (_hrL : r ≤ L)
        (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2))) →
        (∀ i, 0 ≤ h i) → (∀ i, h i ≤ 1) →
        let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
        let k : Fin 6 → ℕ := ![0, p, r, r, r, L]
        let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
          ∑ i ∈ Finset.univ.filter
            (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
        ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x : (Fin L → Fin q) → ℂ),
          let H := ∑ i, h i
          let Hc := H - (((∑ j, e j) : ℝ) : ℂ) • 1
          ∃ hHc : Hc.IsHermitian,
            star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
            (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
            E0 = minEigenvalue hHc ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
            ∀ eps : ℝ, e 1 - 10 ≤ eps → eps ≤ e 1 →
              let Hsoft := H - A 1 + (eps : ℂ) • 1 +
                cfc (Real.softTruncation (3 * (m : ℝ)) m) (A 1 - (eps : ℂ) • 1)
              let Hsc := Hsoft - (((∑ j, e j) : ℝ) : ℂ) • 1
              ∃ (Es : ℝ) (hHsc : Hsc.IsHermitian),
                Es = minEigenvalue hHsc ∧ Hsoft ≤ H ∧
                0 ≤ E0 - Es ∧ E0 - Es ≤ rho ∧
                Submodule.IsCloseTo delta
                  (Submodule.spectralSpanLE hHsc.eigenvectorBasis hHsc.eigenvalues
                    (Es + eta + w))
                  (Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues
                    (E0 + eta)) ∧
                Submodule.IsCloseTo delta
                  (Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues
                    (E0 + eta + w))
                  (Submodule.spectralSpanLE hHsc.eigenvectorBasis hHsc.eigenvalues
                    (Es + eta)) := by
  intro rho
  have hden : 0 < 2 * (eta + 2) := by linarith only [heta]
  have hrho : 0 < rho := lt_min (by norm_num)
    (lt_min (div_pos hw (by norm_num)) (div_pos (by positivity) hden))
  have hrho1 : rho ≤ 1 := min_le_left _ _
  have hrhow : rho ≤ w / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hsmall : 2 * (eta + 2) * rho ≤ delta * w ^ 2 := by
    have hb := (le_div_iff₀ hden).mp ((min_le_right 1 _).trans
      (min_le_right (w / 2) (delta * w ^ 2 / (2 * (eta + 2)))))
    nlinarith only [hb]
  obtain ⟨m, hmformula, hm, htau, ha0, _ha4, hscale, hbudget⟩ :=
    Real.exists_softTruncation_scaled_order_of_residual_budget eta rho heta.le hrho hrho1
  refine ⟨m, hmformula, hm, ?_⟩
  intro L q p r hq hpr hrL h hs h0 h1 _inst k A
  obtain ⟨e, E0, x, hO, hxunit, hx, he, hEcan, hE0, hE2, hresiduals⟩ :=
    exists_interval_physical_scaled_soft_residuals L q p r hq hpr hrL h hs h0 h1
  refine ⟨e, E0, x, ?_⟩
  intro H Hc
  refine ⟨hO, hxunit, hx, he, hEcan, hE0, hE2, ?_⟩
  intro eps hepslo hepshi Hsoft Hsc
  obtain ⟨Es, hS, hEscan, hsoftH, _hElowsoft, hEs0, hres⟩ :=
    hresiduals eps m (3 * (m : ℝ)) hepslo hepshi hm
      (by positivity)
      (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4) (Nat.cast_nonneg m)) htau
  obtain ⟨hresA, hresB⟩ := hres eta heta.le hscale
  have hforwardBudget : 80 * Real.exp ((17 + eta) / 8 - (3 * (m : ℝ)) / 16) ≤ rho := by
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)).trans hbudget
    linarith only [ha0]
  have hdiff : Hc - Hsc = H - Hsoft := by dsimp only [Hc, Hsc]; abel
  have hA : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (Hc - Hsc)).domRestrict (Submodule.spectralSpanLE hO.eigenvectorBasis
        hO.eigenvalues (minEigenvalue hO + eta))‖ ≤ rho := by
    rw [hdiff, ← hEcan]
    exact hresA.trans hforwardBudget
  have hB : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (Hc - Hsc)).domRestrict (Submodule.spectralSpanLE hS.eigenvectorBasis
        hS.eigenvalues (minEigenvalue hS + eta))‖ ≤ rho := by
    rw [hdiff, ← hEscan]
    exact hresB.trans hbudget
  have hclose := Matrix.isCloseTo_spectralSpanLE_pair_of_residuals
    Hc Hsc hO hS eta rho w delta heta hrho hrho1 hw.le hrhow hdelta.le hsmall hA hB
  rw [← hEcan, ← hEscan] at hclose
  exact ⟨Es, hS, hEscan, hsoftH, sub_nonneg.mpr hEs0,
    (le_abs_self _).trans hclose.1, hclose.2⟩

end TNLean.MPS.AreaLaw
