/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftClusters
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftNorm
import TNLean.MPS.AreaLaw.ALVV.SoftClusterPrecision
import QICLean.Analysis.ViableSubspaceOrder

/-!
# Physical soft clusters with uniform numerical precision

One construction of the original regional minima is retained throughout.
The three bulk regions are softened and the two windows remain unchanged.
The norm ceiling and residual budgets depend only on the prescribed scalar
parameters. They imply the two actual finite-window comparisons for every
Hermitian approximation at the displayed precision.

This is a corrected auxiliary for ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1420. **Scope restriction (numerical budgets):**
The soft order, scale and residual cutoffs satisfy explicit scalar inequalities.
Their existence and the final improving-family construction are separate
steps. No soft gap or subspace comparison is assumed. See
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- Uniform scalar residual conditions and an explicit norm precision give
an actual invariant low cluster of each Hermitian approximation, of the
original full ground-space dimension. The regional minima are selected once,
before every center and soft parameter. Auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420. -/
theorem exists_five_region_soft_uniform_clusters {L q k1 k2 k3 k4 ell : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (hwindow1 : k2 - k1 ≤ 2 * ell) (hwindow3 : k4 - k3 ≤ 2 * ell)
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
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      ∀ (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), e j - 10 ≤ p j) →
        (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), p j ≤ e j) → 0 < t → 2 ≤ m →
        let G := (∑ j, ((if j ∈ ({0, 2, 4} : Finset (Fin 5)) then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)) + Y
        let M := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
        G.IsHermitian ∧ ‖G‖ ≤ M ∧
        let Hraw := ∑ i, h i
        let hRaw : Hraw.IsHermitian :=
          (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
        ∀ mu0 g tau T0 T1 : ℝ, mu0 ∈ spectrum ℝ Hraw → 0 < g →
          0 < tau → tau ≤ 1 →
          (∀ z ∈ spectrum ℝ Hraw, z = mu0 ∨ mu0 + g ≤ z) →
          g / 40 + 24 ≤ T0 → 156 + 2 * g ≤ t → 156 + 2 * g ≤ T1 →
          3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) +
            (t / (m : ℝ)) * (T0 / t) ^ m) ≤ tau * g / 1000000 →
          3 * (32 * Real.exp (-(T1 - 156 - 2 * g) / 8) +
            (t / (m : ℝ)) * (T1 / t) ^ m) ≤ tau * g / 1000000 →
          let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
          let original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
          0 < xi ∧ xi ≤ 1 ∧ E + ∑ j, e j = mu0 ∧
          ∀ (Bhat : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
            (hBhat : Bhat.IsHermitian), ‖G - Bhat‖ ≤ xi →
            let target := Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
              (E + g / 4)
            target = Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
                (E + 3 * g / 4) ∧
              Module.finrank ℂ target = Module.finrank ℂ original ∧
              Submodule.IsCloseTo (3 * tau / 200) target original ∧
              Submodule.IsCloseTo (3 * tau / 200) original target := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
    hH, bH, aH, hEigH, hfamily⟩ :=
    exists_five_region_soft_clusters hq h12 h23 h34 h4L h hs h0 h1
  refine ⟨hJ, e, x, E, hx, hxe, he, hE0, hEC, ?_⟩
  intro p t m hpl hpu ht hm G M
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse, hclusters⟩ :=
      hfamily {0, 2, 4} p t m hpl hpu ht hm
  change G.IsHermitian at hG
  have hnorm : ‖G‖ ≤ M := norm_five_region_soft_three_bulk_le
    h12 h23 h34 h4L hwindow1 hwindow3 h hs h0 h1
    e x hx hxe he p t m hpl hpu ht (by omega)
  refine ⟨hG, hnorm, ?_⟩
  intro Hraw hRaw mu0 g tau T0 T1 hmu0 hg htau htau1 hgap
    hT0 htt hT1 hO hR xi original
  have hC4 : (J.card : ℝ) ≤ 4 := by exact_mod_cast hJ
  have hmu30 : -30 ≤ mu := by
    norm_num at hmuD
    exact hmuD
  obtain ⟨hT0actual, htactual, hT1actual, hOactual, hRactual⟩ :=
    soft_cluster_scalar_residual_budgets hC4 hEC hmu30 hg hT0 htt hT1 hO hR
  have hS : ({0, 2, 4} : Finset (Fin 5)).card = 3 := by decide
  simp only [hS, Nat.cast_ofNat, show (10 : ℝ) * 3 = 30 by norm_num] at hclusters
  obtain ⟨hshift, _hsoft, _hdim, _hsoftRaw, _hrawSoft, happrox⟩ :=
    hclusters mu0 g tau T0 T1 hmu0 hg htau htau1 hgap
      hT0actual htactual hT1actual hOactual hRactual
  obtain ⟨hxi, hxi1, hLo, hHi⟩ := soft_cluster_actual_window_losses
    (norm_nonneg G) hnorm hE0 (hEC.trans hC4) hg htau
  refine ⟨hxi, hxi1, hshift, ?_⟩
  intro Bhat hBhat herr target
  obtain ⟨hclosed, hdim, htargetOriginal, horiginalTarget⟩ :=
    happrox Bhat hBhat xi hxi herr
      (hLo.trans_lt (by linarith only [htau1] : tau / 400 < 1))
      (hHi.trans_lt (by linarith only [htau1] : tau / 400 < 1))
  refine ⟨hclosed, hdim, ?_, ?_⟩
  · exact htargetOriginal.of_le (by linarith only [hLo])
  · exact horiginalTarget.of_le (by linarith only [hHi])

end TNLean.MPS.AreaLaw.ALVV
