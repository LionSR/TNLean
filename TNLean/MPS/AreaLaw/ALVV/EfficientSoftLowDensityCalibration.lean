/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.EfficientSoftLowDensityFamily
import TNLean.MPS.AreaLaw.ALVV.EfficientSoftLowDensityParameters
import QICLean.Analysis.SoftFamilyCalibration
import QICLean.Analysis.GeometricOrderPolynomialBound

/-!
# The calibrated efficient soft improving family for low-density spectra

For fixed local dimension `q ≥ 2` and buffer `0 < w ≤ 1`, one natural number `u` fixes the
soft order `m = u¹⁰`, scale `t = 3 m`, filter degree `k = u¹⁶`, window length `ℓ = u⁸`,
residual cutoff `T = u⁹` and precision `ξ`, before the chain length. The resulting
family of middle matrix product operators has a member bond bounded by a natural
polynomial in the chain length. For every chain, every estimate of the bulk energies and
every band width `3 w ≤ η ≤ 34`, two windows of the represented approximant bracket the
original bands at `E + η` and `E + η - 3 w` with losses at most `1 / 200`, and the family
improves viability between them with a contraction `Δ` satisfying `D¹² Δ ≤ 10⁻⁵`, as in the
hard-truncation low-density family. No spectral gap is assumed.

This calibrates the efficient low-density family supporting ALVV, arXiv:1602.08828v2,
`t:aisgaplessefficient`, lines 1424–1437, with the fixed bandwidth of Assumption (LD),
lines 281–284.

**Scope restriction (band width and buffer):** the band width is at most `34` and the buffer
satisfies `0 < w ≤ 1`, and the parameters are chosen from `q` and `w`; in particular they
depend on the chain length whenever the buffer does, as for a buffer `w = μ / (3 log n)`,
and the member bond is then polynomial in the chain length only for fixed `w`. The
parameters are a sufficient calibration, not the source's choice. See
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

open ManyBody (interval)

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- **Calibrated efficient soft improving family for low-density spectra.** For fixed
local dimension and buffer `0 < w ≤ 1`, the soft, filter and cluster parameters and a
polynomial member-bond ceiling are chosen before the chain length. For every chain the
family of middle matrix product operators is chosen before every bulk estimate and band
width `3 w ≤ η ≤ 34`; the two windows of the represented approximant bracket the original
bands with losses at most `1 / 200`, and the family improves viability between them with
`D¹² Δ ≤ 10⁻⁵`. No gap is assumed. Corrected version of ALVV, arXiv:1602.08828v2,
`t:aisgaplessefficient`, lines 1424–1437. -/
theorem exists_calibrated_efficient_soft_low_density_family (q : ℕ) (hq : 2 ≤ q)
    (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    ∃ u : ℕ, 2 ≤ u ∧
      let ell := u ^ 8
      let m := u ^ 10
      let t := 3 * (m : ℝ)
      let k := u ^ 16
      let T := (u : ℝ) ^ 9
      let Dc := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let Mc := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
      let tau := 1 / ((Dc : ℝ) ^ 24 * Mc ^ 10)
      let g := w ^ 2 / 2
      let xi := min 1 (tau * g ^ 2 / (20000 * (Mc + g + 8)))
      ∃ Cpoly ppoly : ℕ, 1 ≤ Cpoly ∧ 1 ≤ ell ∧ 2 ≤ m ∧ 1 ≤ k ∧ 0 < xi ∧
        (∀ N : ℕ,
          let base := 2 * (Real.exp (1 / 3 : ℝ) - 1)
          let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
            Real.log (Real.log (1 + xi / (t * 2 ^ (m + 1))))) / (-Real.log base)⌉₊
          let B := ((order ^ 2 * q ^ order) * 2) * (m + 1)
          (max 1 B) ^ (2 * k) ≤ Cpoly * (N + 1) ^ ppoly) ∧
        ∀ (N a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
          (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
          (_hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
            (h i) (interval (N + 1) i.val (i.val + 2)))
          (_h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
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
                    ∀ eta : ℝ, 3 * w ≤ eta → eta ≤ 34 →
                      let C := (crossings.card : ℝ)
                      let eta1 := eta - 3 * w
                      let rho1 := 3 * ((8 * C) *
                        Real.exp (-(T - 2 * (eta1 + 30 + 3 * C + 2)) / 8) +
                        (t / (m : ℝ)) * (T / t) ^ m)
                      let c1 := mu + eta - w
                      let c0 := mu + eta - 2 * w + rho1
                      let Thi := Submodule.spectralSpanLE hGhat.eigenvectorBasis
                        hGhat.eigenvalues c1
                      let Tlo := Submodule.spectralSpanLE hGhat.eigenvectorBasis
                        hGhat.eigenvalues c0
                      let Delta := (2 * Real.exp (-2 * (k : ℝ) *
                        Real.sqrt ((c1 - c0) / (Msoft + xi - c0)))) ^ 2
                      rho1 ≤ w ^ 2 / 2000000 ∧ Tlo ≤ Thi ∧
                      Submodule.IsCloseTo (1 / 200)
                        (Submodule.spectralSpanLE bH aH (E + eta)) Thi ∧
                      Submodule.IsCloseTo (1 / 200) Tlo
                        (Submodule.spectralSpanLE bH aH (E + eta1)) ∧
                      (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
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
  obtain ⟨u, hu, Cpoly, ppoly, hCpoly, hdata⟩ :=
    exists_soft_low_density_calibration_data q hq w hw
  refine ⟨u, hu, ?_⟩
  intro ell m t k T Dc Mc tau g xi
  obtain ⟨hell, hm, hk, htfloor, hTfloor, htau, htau1, hxi, hxi1, _hD1, hR, hDelta,
      hpolyb⟩ :=
    hdata ell m k t T (Dc : ℝ) Mc tau g xi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨Cpoly, ppoly, hCpoly, hell, hm, hk, hxi, hpolyb, ?_⟩
  intro N a b hab hb h hs h0 h1 resultType
  unfold resultType
  intro Msoft D Sbulk cuts A crossings Y Ksites eK J eJ
    beta midConfig extConfig split Tm heatWeight clusterBase order bond
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, hground, bH, aH, hEigH, Acore, C, hrest⟩ :=
    exists_efficient_soft_low_density_family q ell m k t xi hq hell hm hk le_rfl hxi
      N a b hab hb h hs h0 h1
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, hground, bH, aH, hEigH, Acore, C, ?_⟩
  intro Z Zphys
  obtain ⟨n, W, hnD, hWbond, hcenter⟩ := hrest
  refine ⟨n, W, hnD, hWbond, ?_⟩
  intro p hpl hpu z Fraw G Ghat
  obtain ⟨hGhat, hError, hNorm, mu, hmu30, hmuE, hwins⟩ := hcenter p hpl hpu
  refine ⟨hGhat, hError, hNorm, mu, hmu30, hmuE, ?_⟩
  intro eta h3w heta34 Cc eta1 rho1 c1 c0 Thi Tlo Delta
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hMdef : Msoft = 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34 := rfl
  have hMs : 3 * t ≤ Msoft := by
    have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg _
    have ht0 : 0 ≤ t := (by positivity : (0 : ℝ) ≤ 3 * (m : ℝ))
    rw [hMdef]
    nlinarith only [mul_nonneg ht0 hlogm, hell0]
  have hC4 : Cc ≤ 4 := by
    have hcard : crossings.card ≤ 4 := by
      calc crossings.card ≤ ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ).card :=
            Finset.card_le_card_of_injOn (fun i : Fin N ↦ i.val + 1)
              (by intro i hi; simpa [crossings] using hi)
              (by intro i _ j _ hij; exact Fin.ext (by simpa using hij))
        _ ≤ 4 := Finset.card_le_four
    change ((crossings.card : ℕ) : ℝ) ≤ 4
    exact_mod_cast hcard
  have hC0 : 0 ≤ Cc := Nat.cast_nonneg _
  have hGnorm : ‖G‖ ≤ Msoft + 2 := by
    linarith only [norm_le_norm_add_norm_sub' G Ghat, hNorm, hError, hxi1]
  have hD0 : (0 : ℝ) < D := by
    have hDdef : D = (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell)) := rfl
    have hqk : 0 < q * k := Nat.mul_pos (by omega) (by omega)
    have : 0 < D := by rw [hDdef]; positivity
    exact_mod_cast this
  obtain ⟨hhwin, hUt, hUT, hTo, hrho1, hrho1w, hlo1, hlo0, hDD⟩ :=
    soft_low_density_calibrated_losses (eta := eta) (mu := mu) (E := E) (R := ‖G‖)
      (D := (D : ℝ)) (Cc := Cc) (m := m) (k := k) hw hw1 h3w heta34 hmu30 hmuE hE4 hC0 hC4
      rfl htfloor hTfloor htau1 hxi hxi1 (min_le_right _ _) hMs hR hDelta hD0 hGnorm
  obtain ⟨hTlo, hHi, hLo, hview⟩ := hwins eta T _ w hhwin hw h3w hUt hUT hTo hrho1w
  exact ⟨hrho1, hTlo, hHi.of_le hlo1, hLo.of_le hlo0, hDD, hview⟩

end TNLean.MPS.AreaLaw.ALVV
