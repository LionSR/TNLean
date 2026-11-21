/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.EfficientSoftLowDensityCore
import TNLean.MPS.AreaLaw.ALVV.EfficientSoftLowDensityWindows

/-!
# An efficient soft improving family for low-density spectra

The original interactions construct one family of middle operators, each a matrix product
operator of open bond `(max 1 bond)^{2k}` with `bond = 2 (m + 1) ℓ_c² q^{ℓ_c}` for the
logarithmic cluster order `ℓ_c`, and at most
`(m k + 1)(q k)^{36 ℓ + 4 ⌊k / ℓ⌋}` members. The family is chosen before the three
estimated bulk energies, and before the band width `η`, the buffer `w` and the residual
scale. For each admissible estimate, the represented soft approximant `Ghat` has two windows
that bracket the original band `[E, E + η]` from above and the band `[E, E + η - 3 w]` from
below, with explicit losses, and the family improves every subspace viable for the upper
window into one viable for the lower window, with the Chebyshev contraction
`(2 e^{-2 k √((c₁ - c₀) / (M - c₀))})²`. No spectral gap is assumed.

This is the soft-truncated, matrix-product-operator version of the low-density improving
family of ALVV, arXiv:1602.08828v2, `t:aisgapless`, lines 1027–1041, as used in
`t:aisgaplessefficient`, lines 1424–1437.

**Local fix (cluster estimate, residuals and parameters):** the middle operator uses the
corrected interaction-label cluster estimate at an independent scale `t ≥ 3 m`, the window
comparisons use the corrected regional soft residuals, and the losses and contraction are
stated for explicit parameters rather than the source's parameter choice. The geometry is the
two-window five-region chain of the gapped family. See
`docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

open ManyBody (interval)

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- **Efficient soft improving family for low-density spectra.** The original
interactions construct one family of middle matrix product operators of explicit bond and
count, before every admissible estimate of the bulk energies and every band width. For each
estimate, two windows of the represented soft approximant bracket the original low-energy
bands from both sides with explicit losses, and the family improves viability from the upper
window to the lower one with the Chebyshev contraction. No gap is assumed. Corrected
version of ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1424–1437. -/
theorem exists_efficient_soft_low_density_family
    (q ell m k : ℕ) (t xi : ℝ)
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi)
    (N a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) (interval (N + 1) i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
  (by
    exact (show Prop from
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Sbulk : Finset (Fin 5) := {0, 2, 4}
    let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
    let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
      fun j ↦ ∑ i ∈ Finset.univ.filter
        (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ), h i
    let crossings := Finset.univ.filter
      (fun i : Fin N ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ crossings, h i
    let Ksites := interval (N + 1) (a + 2 * ell) (b + 1)
    let eK := intervalShiftOrderIso
      (hab.trans (Nat.le_succ b))
      (Nat.succ_le_succ ((Nat.le_add_right b (2 * ell)).trans hb))
    let J := interval (N + 1) (a + ell) (b + ell + 1)
    let eJ := intervalShiftOrderIso
      ((Nat.add_le_add_right ((Nat.le_add_right a (2 * ell)).trans hab) ell).trans
        (Nat.le_succ (b + ell)))
      (Nat.succ_le_succ ((Nat.add_le_add_left
        (Nat.le_mul_of_pos_left ell (by decide : 0 < 2)) b).trans hb))
    let beta := fun _ : Fin (N + 1) ↦ Fin q
    let midConfig := ManyBody.RegionConfig beta J
    let extConfig := ManyBody.RegionConfig beta Jᶜ
    let split := (ManyBody.splitEquiv beta J).trans (Equiv.prodComm _ _)
    let Tm := ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split).trans
      ((EuclideanSpace.basisFun extConfig ℂ).tensorProduct
        (EuclideanSpace.basisFun midConfig ℂ)).repr.symm).trans
      (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ extConfig)
        (EuclideanSpace ℂ midConfig))
    let heatWeight := t * (2 : ℝ) ^ (m + 1)
    let clusterBase := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / heatWeight))) / (-Real.log clusterBase)⌉₊
    let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
    ∃ (e : Fin 5 → ℝ) (x : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      (∃ z : (Fin (N + 1) → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
        (H - (E : ℂ) • 1).PosSemidef) ∧
      ∃ (bH : OrthonormalBasis (Fin (N + 1) → Fin q) ℂ
          (EuclideanSpace ℂ (Fin (N + 1) → Fin q)))
        (aH : (Fin (N + 1) → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧
      ∃ (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q bond)
        (C : Fin (m + 1) → Matrix (Fin bond) (Fin bond) ℂ),
        let Z := fun z : ℂ ↦ MPOTensor.traceChainOperator Acore
          (∑ j : Fin (m + 1), z ^ j.val • C j)
        let Zphys := fun z : ℂ ↦ QuantumCircuit.embedOp
          (Subtype.val : Ksites → Fin (N + 1)) (QuantumCircuit.embedOp eK (Z z))
        ∃ (n : ℕ) (W : Fin n → Matrix midConfig midConfig ℂ),
          n ≤ D ∧
          (∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
            ((max 1 bond) ^ (2 * k)) (fun w ↦ W i
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
          ∀ (p : Fin 5 → ℝ)
            (_hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ p j)
            (_hp1 : ∀ j : Fin 5, j ∈ Sbulk → p j ≤ e j),
            let z := Real.exp ((p 2 - e 2) / t)
            let Fraw : Fin 5 → Matrix (Fin (N + 1) → Fin q)
                (Fin (N + 1) → Fin q) ℂ := fun j ↦ (p j : ℂ) • 1 +
              cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
            let G : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
              (∑ j, ((if j ∈ Sbulk then Fraw j else A j) - (e j : ℂ) • 1)) + Y
            let Ghat : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
              G - Fraw 2 + (p 2 : ℂ) • 1 + Zphys (z : ℂ)
            ∃ (hGhat : Ghat.IsHermitian),
              ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ Msoft + xi ∧
              ∃ mu : ℝ, -30 ≤ mu ∧ mu ≤ E ∧
                ∀ (eta T hwin w : ℝ), 0 < hwin → 0 < w → 3 * w ≤ eta →
                  let C := (crossings.card : ℝ)
                  let U := 2 * (eta + 30 + 3 * C + 2)
                  U ≤ t → U ≤ T → eta + 3 * C + 12 ≤ T →
                  let eta1 := eta - 3 * w
                  let eta2 := eta - w / 2
                  let rhoH1 := 3 * ((8 * C) * Real.exp (-(T - eta1 - 3 * C - 12) / 8) +
                    (t / (m : ℝ)) * (T / t) ^ m)
                  let rho1 := 3 * ((8 * C) * Real.exp (-(T - 2 * (eta1 + 30 + 3 * C + 2)) / 8) +
                    (t / (m : ℝ)) * (T / t) ^ m)
                  let rho2 := 3 * ((8 * C) * Real.exp (-(T - 2 * (eta2 + 30 + 3 * C + 2)) / 8) +
                    (t / (m : ℝ)) * (T / t) ^ m)
                  let L1 := (⌈(eta1 + hwin) / (2 * hwin)⌉₊ : ℝ) *
                    (rhoH1 + hwin) ^ 2 / (w / 2 + hwin) ^ 2
                  let L2 := (⌈(eta2 + hwin) / (2 * hwin)⌉₊ : ℝ) *
                    (rho2 + hwin) ^ 2 / (w / 2 + hwin) ^ 2
                  let c1 := mu + eta - w
                  let c0 := mu + eta - 2 * w + rho1
                  let Thi := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues c1
                  let Tlo := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues c0
                  let Delta := (2 * Real.exp (-2 * (k : ℝ) *
                    Real.sqrt ((c1 - c0) / (Msoft + xi - c0)))) ^ 2
                  rho1 < w →
                  Tlo ≤ Thi ∧
                  Submodule.IsCloseTo (2 * (L2 + softWindowPerturbationLoss ‖G‖ xi w c1))
                    (Submodule.spectralSpanLE bH aH (E + eta)) Thi ∧
                  Submodule.IsCloseTo
                    (2 * (softWindowPerturbationLoss ‖G‖ xi w (c0 - w / 2) + L1))
                    Tlo (Submodule.spectralSpanLE bH aH (E + eta1)) ∧
                  ∀ (S : Submodule ℂ (EuclideanSpace ℂ midConfig)) (delta : ℝ),
                    Submodule.IsViable (F := EuclideanSpace ℂ extConfig) delta S
                      (Thi.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
                    let grow := ⨆ i : Fin n, S.map
                      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := midConfig) (W i)).toLinearMap
                    Module.finrank ℂ grow ≤ n * Module.finrank ℂ S ∧
                      Submodule.IsViable (F := EuclideanSpace ℂ extConfig)
                        (Delta / (1 - delta) ^ 2) grow
                        (Tlo.map Tm.toLinearEquiv.toLinearMap))) := by
  classical
  intro resultType
  unfold resultType
  intro Msoft D Sbulk cuts A crossings Y Ksites eK J eJ
    beta midConfig extConfig split Tm heatWeight clusterBase order bond
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, hground, bH, aH, hEigH, Acore, C, hrest⟩ :=
    exists_soft_low_density_polynomial_core q ell m k t xi hq hell hm hk hscale hxi
      N a b hab hb h hs h0 h1
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, hground, bH, aH, hEigH, Acore, C, ?_⟩
  intro Z Zphys
  obtain ⟨n, W, hnD, hWbond, hcenter⟩ := hrest
  refine ⟨n, W, hnD, hWbond, ?_⟩
  intro p hpl hpu z Fraw G Ghat
  obtain ⟨hG, hGhat, hError, hNorm, hpoly, mu, hmu30, hmuE, hwindows⟩ := hcenter p hpl hpu
  refine ⟨hGhat, hError, hNorm, mu, hmu30, hmuE, ?_⟩
  intro eta T hwin w hhwin hw h3w Cc U hUt hUT hTorig eta1 eta2 rhoH1 rho1 rho2 L1 L2
    c1 c0 Thi Tlo Delta hrho
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hC0 : 0 ≤ Cc := Nat.cast_nonneg _
  have hW1 := hwindows eta1 T hwin (w / 2) (by dsimp only [eta1]; linarith) hhwin
    (by positivity) (by dsimp only [U, eta1] at hUt ⊢; linarith)
    (by dsimp only [U, eta1] at hUT ⊢; linarith) (by dsimp only [eta1]; linarith)
  have hW2 := hwindows eta2 T hwin (w / 2) (by dsimp only [eta2]; linarith) hhwin
    (by positivity) (by dsimp only [U, eta2] at hUt ⊢; linarith)
    (by dsimp only [U, eta2] at hUT ⊢; linarith) (by dsimp only [eta2]; linarith)
  obtain ⟨-, -, hR1, -⟩ := hW1
  obtain ⟨-, -, -, hR2⟩ := hW2
  have hL2 : 0 ≤ L2 := by dsimp only [L2]; positivity
  obtain ⟨hHi, hLo⟩ := soft_low_density_window_closeness hG hGhat bH aH E mu eta w rho1 xi
    L1 L2 hxi hw hL2 hError hR1 hR2
  have hsep : c0 < c1 := by dsimp only [c0, c1]; linarith
  have hupper : c1 ≤ Msoft + xi := by
    have hU0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg _
    have ht3 : 2 * (eta + 30 + 3 * Cc + 2) ≤ t := hUt
    have hMs : 3 * t ≤ Msoft := by
      dsimp only [Msoft]
      nlinarith
    dsimp only [c1]
    linarith
  refine ⟨Submodule.spectralSpanLE_mono_cutoff _ _ hsep.le, hHi, hLo, ?_⟩
  exact soft_low_density_chebyshev_viability split Ghat hGhat W hpoly c0 c1 (Msoft + xi)
    hsep hupper hNorm

end TNLean.MPS.AreaLaw.ALVV
