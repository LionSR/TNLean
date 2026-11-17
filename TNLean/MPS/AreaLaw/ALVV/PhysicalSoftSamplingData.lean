/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.UniformPhysicalSoftCalibration
import TNLean.MPS.AreaLaw.PhysicalGroundReferenceTrimming
import QICLean.Analysis.IntervalSamplingSchedule

/-!
# Uniform soft parameters, original-ground references and sampling schedules

At fixed local dimension and gap, the numerical soft parameters, a reference
profile and a sampling threshold coefficient precede the chain length and
Hamiltonian. Each actual original ground space then supplies a single reference
and one trimming radius before any interval, candidate or sample is chosen.
The full-exterior rank is the square of the whole-chain reference bond. Its
weighted trimming loss contains no candidate-dimension factor; the separate
coarse output-bond estimate retains that factor through the common count.

Supporting ALVV, arXiv:1602.08828v2, `lem:trimming`, lines 660–697,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1311–1420, and `t:alg1`,
lines 1777–1817. These are uniform data for the corrected construction, not a
sampling-success or running-time assertion.

**Local fix (corrected uniform parameters):** the data use the corrected soft
and cluster estimates in `docs/paper-gaps/alvv16_soft_regional_residuals.tex`
and `docs/paper-gaps/alvv16_cluster_approximation.tex`, and the corrected complex
sphere count recorded at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_random_sampling_net_count.pdf.
They do not identify the printed fourth-order choice or sharp gap dependence.
-/

open scoped BigOperators ComplexOrder MatrixOrder ENNReal

namespace TNLean.MPS.AreaLaw.ALVV

/-- Uniform numerical soft parameters, an independent original-ground reference,
and a scalar interval resampling schedule can be chosen in the required order.
The flat-spectrum case is included. Supporting ALVV, arXiv:1602.08828v2,
lines 660–697, 1311–1420 and 1777–1817. No sampled family or successful
sampling event is assumed. -/
theorem exists_physical_soft_sampling_data
    (q : ℕ) (hq : 2 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
    let g := min gamma 1
    let Numeric := fun u : ℕ ↦
      let ell := u ^ 8
      let m := u ^ 10
      let t := 3 * (m : ℝ)
      let k := u ^ 16
      let T := (u : ℝ) ^ 9
      let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let M := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
      let tau := 1 / ((D : ℝ) ^ 24 * M ^ 10)
      let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
      let Delta := (2 * Real.exp (-2 * (k : ℝ) *
        Real.sqrt ((g / 2) / (M + xi + 4 + g)))) ^ 2
      ∃ Cpoly ppoly : ℕ, 1 ≤ Cpoly ∧
        1 ≤ ell ∧ 2 ≤ m ∧ 1 ≤ k ∧
        156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
        2 ≤ D ∧ 34 ≤ M ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < xi ∧ xi ≤ 1 ∧
        3 * (32 * Real.exp (-(T - g / 40 - 24) / 8) +
          (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
        3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) +
          (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
        Delta ≤ 1 / ((D : ℝ) ^ 12 * M ^ 10) ∧
        3 * tau / 200 ≤ (((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2) / 100 ∧
        3 * tau / 200 ≤ 1 / 200 ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ N : ℕ,
          let base := 2 * (Real.exp (1 / 3 : ℝ) - 1)
          let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
            Real.log (Real.log (1 + xi / (t * 2 ^ (m + 1))))) / (-Real.log base)⌉₊
          let B := ((order ^ 2 * q ^ order) * 2) * (m + 1)
          (max 1 B) ^ (2 * k) ≤ Cpoly * (N + 1) ^ ppoly
    ∃ u : ℕ, 2 ≤ u ∧ Numeric u ∧
      let ell := u ^ 8
      let m := u ^ 10
      let k := u ^ 16
      let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let width := 4 * ell
      ∃ K Ccount : ℕ, 1 ≤ K ∧ 1 ≤ Ccount ∧
        Ccount = q ^ width + 4 * D ^ 2 * K ∧
        (∀ r len Q : ℕ, K * (r + 1) * (len + 2) ^ 2 ≤ Q →
          4 * D ^ 2 ≤ Q ∧
          Submodule.bootstrapFailure D Q r ≤
            (1 / (q : ℝ)) / ((len : ℝ) + 2) ^ 4) ∧
        ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ,
      ∀ (L : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1)
      ∃ B : ℕ, 1 ≤ B ∧
      let d := r ^ 2 * B
      let bRef := d ^ 2
      let xi := 1 / (1000 * (d : ℝ) * Real.sqrt ((L : ℝ) + 1))
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo (1 / 100000) U G ∧
        Submodule.IsCloseTo (1 / 100000) G U ∧
        (∀ v ∈ U, IsOpenMPS L q d (fun x ↦ v x)) ∧
        (bRef : ℝ) ≤ C * Z ^ P ∧
        0 < xi ∧ xi ≤ 1 ∧
        (∀ kCuts : ℕ, kCuts ≤ L →
          xi * Real.sqrt ((kCuts : ℝ) * (bRef : ℝ)) ≤ 1 / 1000) ∧
        (xi⁻¹) ^ 2 ≤ 1000000 * C * Z ^ (P + 1) ∧
        (∀ count : ℕ,
          ((1000000 * bRef * (L + 1) * count ^ 2 : ℕ) : ℝ) ≤
            1000000 * C * Z ^ (P + 1) * (count : ℝ) ^ 2) ∧
        (let threshold := K * (r + 1) * (L + 2) ^ 2
         let rounds := q * L
         let count := max (q ^ width) (D ^ 2 * threshold)
         2 ≤ threshold ∧ 4 * D ^ 2 ≤ threshold ∧
         (∀ Q : ℕ, threshold ≤ Q →
           Submodule.bootstrapFailure D Q r ≤
             (1 / (q : ℝ)) / ((L : ℝ) + 2) ^ 4) ∧
         (∀ p s : ℕ, Fintype.card (interval L p s → Fin q) ≤ q ^ L) ∧
         q ^ L ≤ 2 ^ rounds ∧
         count ≤ Ccount * ((L + 1) * (r + 1)) ^ 2 ∧
         ((L - 1 : ℕ) : ℝ≥0∞) * (rounds : ℝ≥0∞) *
           ENNReal.ofReal ((1 / (q : ℝ)) / ((L : ℝ) + 2) ^ 4) ≤
             ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2)) ∧
        ∀ p s : ℕ,
          let F := Entropy.regionConfigurationSplit q (interval L p s)
          Submodule.IsCloseTo (1 / 100000)
            (U.map F.toLinearEquiv.toLinearMap) (G.map F.toLinearEquiv.toLinearMap) ∧
          Submodule.IsCloseTo (1 / 100000)
            (G.map F.toLinearEquiv.toLinearMap) (U.map F.toLinearEquiv.toLinearMap) ∧
          ∀ t ∈ U.map F.toLinearEquiv.toLinearMap, ∀ j < s - p - 1,
            Matrix.schmidtRank (WithLp.ofLp
              (Entropy.cutEnvVector (n := fun _ : interval L p s ↦ q)
                (intervalTrimCut L p s j) t)) ≤ bRef := by
  classical
  intro g Numeric
  obtain ⟨u, hu, hNumeric⟩ := exists_uniform_soft_parameters q hq g
    (lt_min hgamma zero_lt_one)
  refine ⟨u, hu, hNumeric, ?_⟩
  intro ell m k D width
  have hD : 2 ≤ D := by
    obtain ⟨Cpoly, ppoly, _, _, _, _, _, _, _, hD, _⟩ := hNumeric
    exact hD
  obtain ⟨K, Ccount, hK, hCcount, hCeq, hschedule⟩ :=
    Submodule.exists_uniform_interval_sampling_schedule q D width hq hD
  obtain ⟨C, hC, P, href⟩ :=
    exists_physical_ground_reference_trimming_profile q (by omega) gamma hgamma
  refine ⟨K, Ccount, hK, hCcount, hCeq, ?_, C, hC, P, ?_⟩
  · intro r len Q hQ
    have h := hschedule len r
    exact ⟨h.2.1.trans hQ, h.2.2.1 Q hQ⟩
  · intro L h hs h0 h1 mu H hH hmu hgap G r Z
    obtain ⟨B, hB, U, hdim, hUG, hGU, hUMPS, hbound, hxi,
      hbudget, hinv, hcost, hinterval⟩ := href L h hs h0 h1 mu hmu hgap
    let d := r ^ 2 * B
    let bRef := d ^ 2
    let xi := 1 / (1000 * (d : ℝ) * Real.sqrt ((L : ℝ) + 1))
    have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
      (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
    have hd : 1 ≤ d := by
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr) hB
    have hxi1 : xi ≤ 1 := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hroot : 1 ≤ Real.sqrt ((L : ℝ) + 1) :=
        (Real.one_le_sqrt).mpr (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
      have hden : 1 ≤ 1000 * (d : ℝ) * Real.sqrt ((L : ℝ) + 1) := by
        nlinarith only [hdR, hroot, mul_le_mul hdR hroot (by norm_num) (by positivity)]
      simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hden
    refine ⟨B, hB, U, hdim, hUG, hGU, hUMPS, hbound, hxi, hxi1,
      hbudget, hinv, hcost, ?_, hinterval⟩
    obtain ⟨hthreshold, hthresholdD, hfailure, hambient, hcount, htotal⟩ := hschedule L r
    refine ⟨hthreshold, hthresholdD, hfailure, ?_, hambient L le_rfl, hcount, htotal⟩
    intro p s
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    apply Nat.pow_le_pow_right (by omega : 1 ≤ q)
    simpa only [Fintype.card_fin] using Finset.card_le_univ (interval L p s)
end TNLean.MPS.AreaLaw.ALVV
