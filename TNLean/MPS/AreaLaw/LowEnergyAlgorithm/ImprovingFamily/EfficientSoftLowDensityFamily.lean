/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.EfficientSoftLowDensityWindows
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.EfficientSoftLowDensityParameters
import QICLean.Analysis.Parameter.SoftFamilyCalibration
import QICLean.Analysis.Real.GeometricOrderPolynomialBound
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.SoftTruncation.SoftFamilyResiduals
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.UniformPhysicalSoftImprovingFamily

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.ALVV.exists_calibrated_efficient_soft_low_density_family`: the calibrated
  efficient soft improving family for low-density spectra.
* `TNLean.MPS.AreaLaw.ALVV.exists_soft_low_density_polynomial_core`: a soft polynomial family with
  windowed spectral comparisons.
-/

open ManyBody (interval)
open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder

section EfficientSoftLowDensityCore

/-!
## A soft polynomial family with windowed spectral comparisons

One construction of the original regional minima determines the native soft middle
operator, its polynomial closing matrices and a common family of middle operators with
open matrix product bond. For every admissible estimate of the three bulk energies, the
represented approximant `Ghat` has a polynomial matrix decomposition through this family, and
the exact soft Hamiltonian `G` it approximates has the buffered windowed comparisons with
the original Hamiltonian. No spectral gap is assumed: these are the inputs of the efficient
low-density improving family.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`,
lines 1424–1437, built as the gapped family of `t:aisefficient`, lines 1373–1420.

**Local fix (cluster estimate and soft residuals):** the middle operator uses the corrected
interaction-label cluster estimate and an independent scale `t ≥ 3 m`, and the residuals are
the corrected regional ones. See `docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

open ManyBody.BondInteraction (isSupportedOn_sum_internal_bonds)

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The original interactions determine one common polynomial matrix family before every
admissible soft center. For each center, the represented approximant has a polynomial
decomposition through the family, and the exact soft Hamiltonian it approximates has both
buffered windowed comparisons with the original Hamiltonian. No gap is assumed. Auxiliary to
ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1424–1437. -/
theorem exists_soft_low_density_polynomial_core
    (q ell m k : ℕ) (t xi : ℝ)
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi)
    (N a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
    (Φ : ManyBody.BondInteraction (N + 1) q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
  (by
    exact (show Prop from
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Sbulk : Finset (Fin 5) := {0, 2, 4}
    let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
    let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
      fun j ↦ Φ.partialHamiltonian (Finset.univ.filter
        (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ))
    let crossings := Finset.univ.filter
      (fun i : Fin N ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := Φ.partialHamiltonian crossings
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
    let extConfig := ManyBody.ComplConfig beta J
    let split := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
    let heatWeight := t * (2 : ℝ) ^ (m + 1)
    let clusterBase := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / heatWeight))) / (-Real.log clusterBase)⌉₊
    let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
    ∃ (e : Fin 5 → ℝ) (x : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
      let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
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
        let Zphys := fun z : ℂ ↦ ManyBody.place (X := fun _ ↦ Fin q) Ksites
          (ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding (Z z))
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
            ∃ (hG : G.IsHermitian) (hGhat : Ghat.IsHermitian),
              ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ Msoft + xi ∧
              (∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
                ∃ M : Fin n → Matrix extConfig extConfig ℂ,
                  Polynomial.aeval Ghat Q = (∑ i, M i ⊗ₖ W i).submatrix split split) ∧
              ∃ mu : ℝ, -30 ≤ mu ∧ mu ≤ E ∧
                ∀ (eta T hwin wbuf : ℝ), 0 ≤ eta → 0 < hwin → 0 < wbuf →
                  let U := 2 * (eta + 30 + 3 * (crossings.card : ℝ) + 2)
                  U ≤ t → U ≤ T → eta + 3 * (crossings.card : ℝ) + 12 ≤ T →
                  let rhoH := 3 * ((8 * (crossings.card : ℝ)) *
                    Real.exp (-(T - eta - 3 * (crossings.card : ℝ) - 12) / 8) +
                    (t / (m : ℝ)) * (T / t) ^ m)
                  let rhoG := 3 * ((8 * (crossings.card : ℝ)) * Real.exp (-(T - U) / 8) +
                    (t / (m : ℝ)) * (T / t) ^ m)
                  let count := ⌈(eta + hwin) / (2 * hwin)⌉₊
                  0 ≤ E - mu ∧ E - mu ≤ rhoG ∧
                    Submodule.IsCloseTo ((count : ℝ) * (rhoH + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                      (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues
                        (mu + eta + rhoG + wbuf))
                      (Submodule.spectralSpanLE bH aH (E + eta)) ∧
                    Submodule.IsCloseTo ((count : ℝ) * (rhoG + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                      (Submodule.spectralSpanLE bH aH (E + eta + wbuf))
                      (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues
                        (mu + eta)))) := by
  classical
  intro resultType
  unfold resultType
  intro Msoft D Sbulk cuts A crossings Y Ksites eK J eJ
    beta midConfig extConfig split heatWeight clusterBase order bond
  have ht : 0 < t := lt_of_lt_of_le (by positivity : 0 < 3 * (m : ℝ)) hscale
  obtain ⟨hJ, e, x, z0, E, hx, hxe, he, hz0, hHz0, hE, hE0, hEC, _hH, bH, aH, hEigH,
      hfamily⟩ :=
    exists_five_region_soft_representation (N := N) (q := q)
      (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell)
      (by omega) (by omega) (by omega) (by omega) (by omega) Φ h0 h1
  have hE4 : E ≤ 4 := hEC.trans (by exact_mod_cast hJ)
  have hlo : (e 2 : ℂ) • 1 ≤ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1), Φ.term i := by
    exact Matrix.le_iff.mpr (he 2)
  obtain ⟨Acore, C, hZherm, hZerror⟩ := exists_uniform_native_soft_middle_mpo
    (N := N) (q := q) (l := a + 2 * ell) (r := b + 1) (m := m)
    (by omega) (by omega) (by omega) (by omega) Φ h0 h1 (e 2) t xi hlo hscale hxi
  let WL : Fin (2 * ell) → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun r ↦ Φ.term ⟨a + r.val, by omega⟩
  let WR : Fin (2 * ell) → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun r ↦ Φ.term ⟨b + r.val, by omega⟩
  have hWL (r : Fin (2 * ell)) : ManyBody.IsSupportedOn (WL r)
      (interval (N + 1) (a + r.val) (a + r.val + 2)) := Φ.mem ⟨a + r.val, by omega⟩
  have hWR (r : Fin (2 * ell)) : ManyBody.IsSupportedOn (WR r)
      (interval (N + 1) (b + r.val) (b + r.val + 2)) := Φ.mem ⟨b + r.val, by omega⟩
  obtain ⟨n, W, hn, hWbond, hWpoly⟩ :=
    exists_common_physical_polynomial_closing_family_fin
      (L := N + 1) (q := q) (ell := ell) (a := a) (b := b) (B := bond) (k := k)
      WL WR hWL hWR hab (by simpa using hb) hell hq hk Acore C
  have hnD : n ≤ D := by
    convert hn using 1
    dsimp only [D]
    rw [← pow_mul]
    congr 2
    omega
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, ⟨z0, hz0, hHz0, hE⟩, bH, aH, hEigH, Acore, C, ?_⟩
  intro Z Zphys
  refine ⟨n, W, hnD, hWbond, ?_⟩
  intro p hpl hpu z Fraw G Ghat
  obtain ⟨mu, w, hG, _hBpos, _hGH, hw, hGw, hGlow, hmuD, hmuE, _hmuC,
      bG, aG, hEigG, _hforward, _hreverse, hwindows, _hmpo⟩ :=
    hfamily Sbulk p t m hpl hpu ht hm
  change G.IsHermitian at hG
  have hGnorm : ‖G‖ ≤ Msoft :=
    norm_five_region_soft_three_bulk_le (L := N + 1) (q := q)
      (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell) (ell := ell)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      Φ h0 h1 e x hx hxe he p t m hpl hpu ht (by omega)
  have hp2upper : p 2 ≤ e 2 :=
    hpu 2 (by exact (by decide : (2 : Fin 5) ∈ ({0, 2, 4} : Finset (Fin 5))))
  obtain ⟨_hz0, _hz1, _hNativeError, hPlacedError⟩ := hZerror (p 2) hp2upper
  change ‖cfc (Real.softTruncation t m) (A 2 - (p 2 : ℂ) • 1) - Zphys (z : ℂ)‖ ≤ xi
    at hPlacedError
  have hp2 : ((p 2 : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
      (Fin (N + 1) → Fin q) ℂ)).IsHermitian :=
    isHermitian_one.smul (by simp [isSelfAdjoint_iff])
  have hF2 : (Fraw 2).IsHermitian := hp2.add
    (cfc_predicate (Real.softTruncation t m) (A 2 - (p 2 : ℂ) • 1))
  have hGhat : Ghat.IsHermitian := ((hG.sub hF2).add hp2).add (hZherm z).2
  have hError : ‖G - Ghat‖ ≤ xi := by
    convert hPlacedError using 1
    congr 1
    dsimp only [Ghat, Fraw]
    abel
  have hNorm : ‖Ghat‖ ≤ Msoft + xi :=
    (norm_le_norm_add_norm_sub G Ghat).trans (add_le_add hGnorm hError)
  have hSbulk : (Sbulk.card : ℝ) = 3 := by norm_num [Sbulk]
  have hDbulk : 10 * (Sbulk.card : ℝ) = 30 := by rw [hSbulk]; norm_num
  refine ⟨hG, hGhat, hError, hNorm, ?_, mu, by linarith [hmuD, hDbulk], hmuE, ?_⟩
  · let PL := Fraw 0 - ∑ j, (e j : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
      (Fin (N + 1) → Fin q) ℂ) + (p 2 : ℂ) • 1
    have hFsupport (j : Fin 5) : ManyBody.IsSupportedOn (Fraw j)
        (interval (N + 1) (cuts j.castSucc) (cuts j.succ)) := by
      change _ ∈ ManyBody.supportedOperators _ _
      let V := ManyBody.supportedOperators (fun _ ↦ Fin q)
        (interval (N + 1) (cuts j.castSucc) (cuts j.succ) : Finset (Fin (N + 1)))
      have hAmem : A j ∈ V :=
        isSupportedOn_sum_internal_bonds (N + 1) q (cuts j.castSucc) (cuts j.succ) Φ
      change _ ∈ ManyBody.supportedOperators _ _
      exact add_mem (SMulMemClass.smul_mem _ (one_mem (ManyBody.supportedOperators _ _)))
        (ManyBody.cfc_mem_supportedOperators _
          (sub_mem hAmem (SMulMemClass.smul_mem _ (one_mem (ManyBody.supportedOperators _ _)))))
    have hPL : ManyBody.IsSupportedOn PL (interval (N + 1) 0 (a + 1)) := by
      change _ ∈ ManyBody.supportedOperators _ _
      let V := ManyBody.supportedOperators (fun _ ↦ Fin q)
        (interval (N + 1) 0 (a + 1) : Finset (Fin (N + 1)))
      have hFmem : Fraw 0 ∈ V := hFsupport 0
      change _ ∈ ManyBody.supportedOperators _ _
      exact add_mem (sub_mem hFmem (sum_mem fun j _ ↦
        SMulMemClass.smul_mem _ (one_mem (ManyBody.supportedOperators _ _))))
        (SMulMemClass.smul_mem _ (one_mem (ManyBody.supportedOperators _ _)))
    have hPR : ManyBody.IsSupportedOn (Fraw 4) (interval (N + 1) (b + 2 * ell) (N + 1)) :=
      hFsupport 4
    have hAlphabet :
        (∑ i, Sum.elim (Sum.elim WL WR) ![PL, Zphys (z : ℂ), Fraw 4] i) = Ghat :=
      actual_three_bulk_replacement_sum (N + 1) a b ell hell hab (by simpa using hb) Φ.term
        Fraw (fun j ↦ (e j : ℂ) • 1) (Zphys (z : ℂ)) ((p 2 : ℂ) • 1)
    intro Q hQ
    obtain ⟨M, hMatrix, _hTensor⟩ := hWpoly (z : ℂ) PL (Fraw 4) hPL hPR Q hQ
    refine ⟨M, ?_⟩
    have hEval := congrArg (fun B : Matrix (Fin (N + 1) → Fin q)
        (Fin (N + 1) → Fin q) ℂ ↦ Polynomial.aeval B Q) hAlphabet.symm
    exact hEval.trans hMatrix
  · intro eta T hwin wbuf heta hhwin hwbuf U hUt hUT hTorig rhoH rhoG count
    have hG' (c : ℝ) := Submodule.spectralSpanLE_eq_of_eigenbases
      bG hG.eigenvectorBasis aG hG.eigenvalues hEigG hG.toEuclideanCLM_eigenvectorBasis c
    have h30 : (10 : ℝ) * 3 = 30 := by norm_num
    have hwins := hwindows eta T hwin wbuf heta hhwin hwbuf
    simp only [hSbulk, h30] at hwins
    obtain ⟨h1', h2', h3', h4'⟩ := hwins hUt hUT hTorig
    refine ⟨h1', h2', ?_, ?_⟩
    · rw [← hG']
      exact h3'
    · rw [← hG']
      exact h4'

end TNLean.MPS.AreaLaw.ALVV

end EfficientSoftLowDensityCore

namespace TNLean.MPS.AreaLaw.ALVV

section EfficientSoftLowDensityFamily

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
    (Φ : ManyBody.BondInteraction (N + 1) q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
  (by
    exact (show Prop from
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Sbulk : Finset (Fin 5) := {0, 2, 4}
    let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
    let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
      fun j ↦ Φ.partialHamiltonian (Finset.univ.filter
        (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ))
    let crossings := Finset.univ.filter
      (fun i : Fin N ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := Φ.partialHamiltonian crossings
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
    let extConfig := ManyBody.ComplConfig beta J
    let split := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
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
      let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
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
        let Zphys := fun z : ℂ ↦ ManyBody.place (X := fun _ ↦ Fin q) Ksites
          (ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding (Z z))
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
      N a b hab hb Φ h0 h1
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

end EfficientSoftLowDensityFamily

section EfficientSoftLowDensityCalibration

/-!
## The calibrated efficient soft improving family for low-density spectra

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
          (Φ : ManyBody.BondInteraction (N + 1) q)
          (_h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1),
      (by
        exact (show Prop from
        let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
        let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
        let Sbulk : Finset (Fin 5) := {0, 2, 4}
        let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
        let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
          fun j ↦ Φ.partialHamiltonian (Finset.univ.filter
            (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ))
        let crossings := Finset.univ.filter
          (fun i : Fin N ↦ i.val + 1 ∈
            ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
        let Y := Φ.partialHamiltonian crossings
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
        let extConfig := ManyBody.ComplConfig beta J
        let split := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
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
          let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
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
            let Zphys := fun z : ℂ ↦ ManyBody.place (X := fun _ ↦ Fin q) Ksites
              (ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding (Z z))
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
  intro N a b hab hb Φ h0 h1 resultType
  unfold resultType
  intro Msoft D Sbulk cuts A crossings Y Ksites eK J eJ
    beta midConfig extConfig split Tm heatWeight clusterBase order bond
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, hground, bH, aH, hEigH, Acore, C, hrest⟩ :=
    exists_efficient_soft_low_density_family q ell m k t xi hq hell hm hk le_rfl hxi
      N a b hab hb Φ h0 h1
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

end EfficientSoftLowDensityCalibration

end TNLean.MPS.AreaLaw.ALVV
