/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftResiduals
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.LowEnergyCluster
import QICLean.Analysis.LowEnergyCoordinates
import QICLean.Analysis.ShiftedLowEnergyCoordinates
import QICLean.Analysis.SpectralClusterNormPerturbation

/-!
# Physical soft clusters and their actual Hermitian approximants

The regional minima, centered original Hamiltonian and simultaneous soft
replacement are constructed once from the original local interactions.
Both physical restricted residuals are retained. An original spectral gap
and explicit scalar residual budgets derive the exact soft cluster; a
separate global Hermitian approximation then has its own invariant low
cluster, of the original ground-space dimension.

This is a corrected auxiliary for ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1420.
**Scope restriction (one-sided centers and explicit precision):** Regional
estimates lie in the actual ten-unit lower interval. Physical residuals
and the two norm-perturbation window losses remain explicit numerical
conditions. No uniform choice of soft scale or order, measurable adaptive
energy estimates or running time is asserted. See
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- One actual soft residual construction derives its low cluster from
primitive original spectral data and explicit scalar budgets. Every
Hermitian global norm approximant then has its own separated low cluster
and both directed comparisons to the original full ground space. The
regional minima, ground energies, actual eigenbases and both original
residual conclusions are retained, rather than selected a second time.
Auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420. -/
theorem exists_five_region_soft_clusters {L q k1 k2 k3 k4 : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ ∑ i ∈ I j, h i
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      H.IsHermitian ∧
      ∃ (bH : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
        (aH : (Fin L → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧ ∀ (S : Finset (Fin 5)) (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ S, e j - 10 ≤ p j) → (∀ j ∈ S, p j ≤ e j) → 0 < t → 2 ≤ m →
        let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
        let D := 10 * (S.card : ℝ)
        let G := B + Y
        ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ), G.IsHermitian ∧
          (B + (D : ℂ) • 1).PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧
          G *ᵥ w = (mu : ℂ) • w ∧ (G - (mu : ℂ) • 1).PosSemidef ∧
          -D ≤ mu ∧ mu ≤ E ∧ mu ≤ (J.card : ℝ) ∧
          ∃ (bG : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
            (aG : (Fin L → Fin q) → ℝ),
            (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G (bG v) =
              (aG v : ℂ) • bG v) ∧
          (∀ eta T : ℝ, 0 ≤ eta → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bH aH (E + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) *
                Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T : ℝ, 0 ≤ eta →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bG aG (mu + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (let Hraw := ∑ i, h i
          let hRaw : Hraw.IsHermitian :=
            (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
          ∀ mu0 g tau T0 T1 : ℝ, mu0 ∈ spectrum ℝ Hraw → 0 < g →
            0 < tau → tau ≤ 1 →
            (∀ z ∈ spectrum ℝ Hraw, z = mu0 ∨ mu0 + g ≤ z) →
            let etaR := E - mu + 19 * g / 20
            let U := 2 * (etaR + D + 3 * (J.card : ℝ) + 2)
            g / 40 + 3 * (J.card : ℝ) + 12 ≤ T0 → U ≤ t → U ≤ T1 →
            let rhoO := (S.card : ℝ) * ((8 * (J.card : ℝ)) *
              Real.exp (-(T0 - g / 40 - 3 * (J.card : ℝ) - 12) / 8) +
              (t / (m : ℝ)) * (T0 / t) ^ m)
            let rhoR := (S.card : ℝ) * ((8 * (J.card : ℝ)) *
              Real.exp (-(T1 - U) / 8) + (t / (m : ℝ)) * (T1 / t) ^ m)
            rhoO ≤ tau * g / 1000000 → rhoR ≤ tau * g / 1000000 →
            let original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
            let soft := Submodule.spectralSpanLE bG aG (E + g / 20)
            E + ∑ j, e j = mu0 ∧
              soft = Submodule.spectralSpanLE bG aG (E + 19 * g / 20) ∧
              Module.finrank ℂ soft = Module.finrank ℂ original ∧
              Submodule.IsCloseTo (tau / 200 : ℝ) soft original ∧
              Submodule.IsCloseTo (tau / 200 : ℝ) original soft ∧
            ∀ (Bhat : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
              (hBhat : Bhat.IsHermitian) (xi : ℝ), 0 < xi → ‖G - Bhat‖ ≤ xi →
              let V := ‖G‖ + xi
              let nLo := ⌈((E + g / 20) - min (E + g / 20 - 1) (-V)) / (2 * xi)⌉₊
              let nHi := ⌈((E + 3 * g / 4) - min (E + 3 * g / 4 - 1) (-V)) / (2 * xi)⌉₊
              let deltaLo := (nLo : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2
              let deltaHi := (nHi : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2
              deltaLo < 1 → deltaHi < 1 →
              let target := Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
                (E + g / 4)
              target = Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
                  (E + 3 * g / 4) ∧
                Module.finrank ℂ target = Module.finrank ℂ original ∧
                Submodule.IsCloseTo (2 * (deltaLo + tau / 200)) target original ∧
                Submodule.IsCloseTo (2 * (deltaHi + tau / 200)) original target) := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
    hH, bH, aH, hEigH, hfamily⟩ :=
    exists_five_region_soft_residuals hq h12 h23 h34 h4L h hs h0 h1
  refine ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
    hH, bH, aH, hEigH, ?_⟩
  intro S p t m hpl hpu ht hm B D G
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse⟩ := hfamily S p t m hpl hpu ht hm
  change G.IsHermitian at hG
  refine ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse, ?_⟩
  clear hfamily
  intro Hraw hRaw mu0 g tau T0 T1 hmu0 hg htau htau1 hgap
    etaR U hT0 hUt hUT1 rhoO rhoR hsmallO hsmallR original soft
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨hgroundShift, hrawEigen, hrawGap⟩ := hRaw.original_basis_centered_gap_data
    mu0 g (∑ j, e j) E hmu0 hgap hg z hz hHz hE
  have hspan (cutoff : ℝ) := Submodule.spectralSpanLE_eq_of_eigenbases
    bH hRaw.eigenvectorBasis aH (fun j ↦ hRaw.eigenvalues j - ∑ i, e i)
    hEigH hrawEigen cutoff
  have hOriginal : Submodule.spectralSpanLE hRaw.eigenvectorBasis
      (fun j ↦ hRaw.eigenvalues j - ∑ i, e i) E = original := by
    simpa only [show mu0 - ∑ i, e i = E by linarith only [hgroundShift]] using
      Submodule.spectralSpanLE_sub hRaw.eigenvectorBasis hRaw.eigenvalues (∑ j, e j) mu0
  have hresO : ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (Hraw - (((∑ j, e j) : ℝ) : ℂ) • 1) -
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G).domRestrict
        (Submodule.spectralSpanLE hRaw.eigenvectorBasis
          (fun j ↦ hRaw.eigenvalues j - ∑ i, e i) (E + g / 40))‖ ≤
      tau * g / 1000000 := by
    rw [← hspan (E + g / 40)]
    simpa only [map_sub] using
      (hforward (g / 40) T0 (by positivity) hT0).trans hsmallO
  have hresR : ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (Hraw - (((∑ j, e j) : ℝ) : ℂ) • 1) -
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G).domRestrict
        (Submodule.spectralSpanLE bG aG (E + 19 * g / 20))‖ ≤
      tau * g / 1000000 := by
    rw [show E + 19 * g / 20 = mu + etaR by dsimp only [etaR]; ring]
    simpa only [map_sub] using
      (hreverse etaR T1 (by dsimp only [etaR]; linarith only [hmuE, hg])
        hUt hUT1).trans hsmallR
  obtain ⟨hcluster, hdim, hsoftRaw, hrawSoft, _hwindow, _hspectrum⟩ :=
    Submodule.low_spectral_cluster_of_scaled_restricted_residuals
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (Hraw - (((∑ j, e j) : ℝ) : ℂ) • 1))
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G)
      hRaw.eigenvectorBasis bG (fun j ↦ hRaw.eigenvalues j - ∑ i, e i) aG
      hrawEigen hEigG E g (tau * g / 1000000) tau hg htau htau1
      (by positivity) le_rfl hrawGap hresO hresR
  rw [hOriginal] at hdim hsoftRaw hrawSoft
  refine ⟨hgroundShift.symm, hcluster, hdim, hsoftRaw, hrawSoft, ?_⟩
  intro Bhat hBhat xi hxi herr V nLo nHi deltaLo deltaHi hLo hHi target
  have hcanonical (cutoff : ℝ) := Submodule.spectralSpanLE_eq_of_eigenbases
    hG.eigenvectorBasis bG hG.eigenvalues aG hG.toEuclideanCLM_eigenvectorBasis hEigG cutoff
  have hcanCluster :
      Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (E + g / 20) =
        Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (E + 19 * g / 20) := by
    simpa only [hcanonical (E + g / 20), hcanonical (E + 19 * g / 20)] using hcluster
  have hApprox := hG.spectral_cluster_of_norm_sub_le hBhat
    (E + g / 20) (E + g / 4) (E + 3 * g / 4) (E + 19 * g / 20) xi
    (by linarith only [hg]) (by linarith only [hg]) (by linarith only [hg])
    hxi herr hcanCluster
  simp only [hcanonical (E + g / 20),
    show (E + g / 4) - (E + g / 20) = g / 5 by ring,
    show (E + 19 * g / 20) - (E + 3 * g / 4) = g / 5 by ring] at hApprox
  obtain ⟨hTarget, hdimTarget, hTargetSoft, hSoftTarget, _hTargetWindow⟩ := hApprox hLo hHi
  have hTargetOriginal : Submodule.IsCloseTo (2 * (deltaLo + tau / 200)) target original := by
    convert hTargetSoft.trans_weighted (θ := 1) hsoftRaw (by positivity) (by norm_num) using 1
    ring
  have hOriginalTarget : Submodule.IsCloseTo (2 * (deltaHi + tau / 200)) original target := by
    convert hrawSoft.trans_weighted (θ := 1) hSoftTarget (by positivity) (by norm_num) using 1
    ring
  exact ⟨hTarget, hdimTarget.trans
    ((congrArg (fun P : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) ↦
      Module.finrank ℂ P) (hcanonical (E + g / 20))).trans hdim),
    hTargetOriginal, hOriginalTarget⟩

end TNLean.MPS.AreaLaw.ALVV
