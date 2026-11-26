/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.UniformPhysicalSoftCalibration
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalGroundReference
import QICLean.Probability.Sampling.IntervalSamplingSchedule
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.NativeLongIntervalSoftFamily
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalIntervalRawHistory
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalIntervalResamplingSelection
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalCollectiveTrimming
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.EnergyEstimate.SuccessfulTreeEnergyInduction

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.ALVV.exists_physical_soft_interval_history`: physical soft families and their
  original-ground sampling histories.
* `TNLean.MPS.AreaLaw.ALVV.IsPhysicalTerminalCertificate`,
  `TNLean.MPS.AreaLaw.ALVV.exists_physical_soft_resampling_tree`: physical soft families on the
  actual finite-resampling tree.
-/

open ManyBody (interval)

section PhysicalSoftSamplingData

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
      (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
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
  · intro L Φ h0 h1 mu H hH hmu hgap G r Z
    obtain ⟨B, hB, U, hdim, hUG, hGU, hUMPS, hbound, hxi,
      hbudget, hinv, hcost, hinterval⟩ := href L Φ h0 h1 mu hmu hgap
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

end PhysicalSoftSamplingData

section PhysicalSoftIntervalHistory

/-!
## Physical soft families and their original-ground sampling histories

One physical family is selected before every energy-center estimate, candidate
and finite sequence of Haar samples. The literal history concerns only the
original ground space; on that same event its last untrimmed image improves
every admissible represented target. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755, 1311–1420 and 1801–1813.

**Scope restriction (explicit numerical and reference certificates):** the
physical family is constructed from supported positive nearest-neighbor
contractions on one long interval. Reference-rank and numerical certificates
remain explicit inputs; the complete primitive-chain selection and running-time
claims are separate. The corrected residual and cluster conventions are in
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`. Repeated sampling and the
terminal image convention are documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
-/

open MeasureTheory Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator
  MatrixOrder ComplexOrder ENNReal

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- A physical long-interval family and the literal original-ground histories
of all candidates, with the same last image improving every admissible center.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1801–1813. -/
theorem exists_physical_soft_interval_history
    (q ell m k : ℕ) (g tau t T0 T1 : ℝ)
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hg : 0 < g) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hscale : 3 * (m : ℝ) ≤ t)
    (hT0 : g / 40 + 24 ≤ T0) (htfloor : 156 + 2 * g ≤ t)
    (hT1 : 156 + 2 * g ≤ T1)
    (hO : 3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) +
      (t / m) * (T0 / t) ^ m) ≤ tau * g / 1000000)
    (hR : 3 * (32 * Real.exp (-(T1 - 156 - 2 * g) / 8) +
      (t / m) * (T1 / t) ^ m) ≤ tau * g / 1000000)
    (N p r : ℕ) (hpr : p ≤ r) (hrN : r ≤ N + 1) (hlong : 4 * ell < r - p)
      (Φ : ManyBody.BondInteraction (N + 1) q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let samplingD := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let samplingM := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let precision := min 1 (tau * g ^ 2 / (20000 * (samplingM + g + 8)))
    let filterLoss := (2 * Real.exp (-2 * (k : ℝ) *
      Real.sqrt ((g / 2) / (samplingM + precision + 4 + g)))) ^ 2
    ∀ (K rho rounds bRef : ℕ) (xiTrim epsilonRef : ℝ),
      2 ≤ samplingD → 1 ≤ K →
      (∀ rho' len Q : ℕ, K * (rho' + 1) * (len + 2) ^ 2 ≤ Q →
        4 * samplingD ^ 2 ≤ Q ∧ Submodule.bootstrapFailure samplingD Q rho' ≤
          (1 / (q : ℝ)) / ((len : ℝ) + 2) ^ 4) →
      (samplingD : ℝ) ^ 12 * filterLoss ≤ 1 / 100000 →
      3 * tau / 200 ≤ (((3 / 100 : ℝ) / (samplingD : ℝ) ^ 2) ^ 2) / 100 →
      3 * tau / 200 ≤ 1 / 200 →
      0 < xiTrim → 0 ≤ epsilonRef → epsilonRef ≤ 1 / 100000 →
    let Hraw := Φ.hamiltonian
    let hRaw : Hraw.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    ∀ mu0 : ℝ, mu0 ∈ spectrum ℝ Hraw →
      (∀ y ∈ spectrum ℝ Hraw, y = mu0 ∨ mu0 + g ≤ y) →
    let Original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
    ∀ R : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1) → Fin q)),
      Submodule.IsCloseTo epsilonRef Original R →
      Submodule.IsCloseTo epsilonRef R Original →
      (∀ v ∈ R.map
        (Entropy.regionConfigurationSplit q (interval (N + 1) p r)).toLinearEquiv.toLinearMap,
        ∀ j < r - p - 1,
        Matrix.schmidtRank (WithLp.ofLp
          (Entropy.cutEnvVector (n := fun _ : interval (N + 1) p r ↦ q)
            (intervalTrimCut (N + 1) p r j) v)) ≤ bRef) →
      xiTrim * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (bRef : ℝ)) ≤ 1 / 1000 →
      Module.finrank ℂ Original ≤ rho →
      Fintype.card (interval (N + 1) p r → Fin q) ≤ 2 ^ rounds →
    ∃ (a b : ℕ) (_hab : a + 2 * ell ≤ b) (_hb : b + 2 * ell ≤ N),
      p ≤ a + ell ∧ b + ell + 1 ≤ r ∧
      (interval (N + 1) p r \ interval (N + 1) (a + ell) (b + ell + 1)).card ≤ 2 * ell ∧
      a + 2 * ell - p ≤ 2 * ell ∧ r - (b + 1) ≤ 2 * ell ∧
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let xi := min 1 (tau * g ^ 2 / (20000 * (Msoft + g + 8)))
    let upper := Msoft + xi + 4 + g
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Delta := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / upper))) ^ 2
    let Sbulk : Finset (Fin 5) := {0, 2, 4}
    let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
    let A := fun j : Fin 5 ↦ Φ.partialHamiltonian (Finset.univ.filter
      (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ))
    let Y := Φ.partialHamiltonian (Finset.univ.filter (fun i : Fin N ↦ i.val + 1 ∈
      ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)))
    let J := interval (N + 1) p r
    let eJ := intervalShiftOrderIso hpr hrN
    let midConfig := J → Fin q
    let HM := EuclideanSpace ℂ midConfig
    let coords := Entropy.regionTensorCoordinates q J
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / (t * (2 : ℝ) ^ (m + 1)))))/
        (-Real.log (2 * (Real.exp (1 / 3 : ℝ) - 1)))⌉₊
    let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
    let Hraw := Φ.hamiltonian
    let hRaw : Hraw.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    ∃ (e : Fin 5 → ℝ) (x : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
      ∃ (n : ℕ) (W : Fin n → Matrix midConfig midConfig ℂ),
        let Fops := fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := midConfig) (W i)
        let d := Fintype.card midConfig
        let coord := (Fintype.equivFin midConfig).symm
        let threshold := K * (rho + 1) * (N + 3) ^ 2
        let good := fun S ↦ canonicalHalfSampledIntervalHistory
          (N + 1) q p r D threshold rounds Fops xiTrim S Original
        let state := fun (S : Submodule ℂ HM)
          (U : Fin rounds → Matrix.rankUnitaryProduct d) j ↦
          let P := ((Matrix.toEuclideanCLM (n := midConfig) (𝕜 := ℂ)).symm
            S.starProjection).reindex coord.symm coord.symm
          Entropy.canonicalHalfSampleTrimIterate coord (intervalTrimCut (N + 1) p r)
            xiTrim (r - p - 1) D threshold (Entropy.nativeFamilyMatrix coord Fops) P
            (Entropy.halfSamplingSeedSequence U) j
        let image := fun S U ↦ (Matrix.toEuclideanLin (Matrix.familySupportProj
          (fun i ↦ Entropy.nativeFamilyMatrix coord Fops i * state S U rounds))).range
        let parent := fun S U ↦ canonicalHalfSampledIntervalParent
          (N + 1) q p r D threshold rounds Fops xiTrim S U
        let law := Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d)
        let fixedHistory := ∀ S : Submodule ℂ HM,
          Submodule.IsViable 0.04 S (Original.map coords.toLinearEquiv.toLinearMap) →
          MeasurableSet (good S) ∧
          law (good S)ᶜ ≤ (rounds : ℝ≥0∞) *
            ENNReal.ofReal ((1 / (q : ℝ)) / ((N : ℝ) + 3) ^ 4) ∧
          MeasurableSet {U | Submodule.IsViable (3 / 200) (parent S U)
            (Original.map coords.toLinearEquiv.toLinearMap)} ∧
          law {U | ¬Submodule.IsViable (3 / 200) (parent S U)
            (Original.map coords.toLinearEquiv.toLinearMap)} ≤ (rounds : ℝ≥0∞) *
              ENNReal.ofReal ((1 / (q : ℝ)) / ((N : ℝ) + 3) ^ 4) ∧
          ∀ U ∈ good S,
            Submodule.IsViable (27 / 2500) (image S U)
              (Original.map coords.toLinearEquiv.toLinearMap) ∧
            Submodule.IsViable (3 / 200) (parent S U)
              (Original.map coords.toLinearEquiv.toLinearMap)
        n ≤ D ^ 2 ∧
        (∀ i, IsOpenMPS (r - p) (q * q) (max 1 ((max 1 bond) ^ (2 * k)))
          (fun w ↦ W i
            (fun v ↦ (finProdFinEquiv.symm (w (eJ.symm v))).1)
            (fun v ↦ (finProdFinEquiv.symm (w (eJ.symm v))).2))) ∧
        fixedHistory ∧
        ∀ (pc : Fin 5 → ℝ)
          (_hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ pc j)
          (_hp1 : ∀ j : Fin 5, j ∈ Sbulk → pc j ≤ e j),
          let Fraw := fun j : Fin 5 ↦ (pc j : ℂ) • 1 +
            cfc (Real.softTruncation t m) (A j - (pc j : ℂ) • 1)
          let G := (∑ j, ((if j ∈ Sbulk then Fraw j else A j) - (e j : ℂ) • 1)) + Y
          ∃ (Ghat : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
            (hGhat : Ghat.IsHermitian),
            ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ Msoft + xi ∧
              let original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
              let target := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                (E + g / 4)
              let Tc := target.map coords.toLinearEquiv.toLinearMap
              E + ∑ j, e j = mu0 ∧
              target = Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                (E + 3 * g / 4) ∧
              Module.finrank ℂ target = Module.finrank ℂ original ∧
              Submodule.IsCloseTo (3 * tau / 200) target original ∧
              Submodule.IsCloseTo (3 * tau / 200) original target ∧
              (∀ S : Submodule ℂ HM,
                Submodule.IsViable 0.04 S (Original.map coords.toLinearEquiv.toLinearMap) →
                ∀ U ∈ good S, Submodule.IsViable (Delta / (91 / 100 : ℝ) ^ 2)
                  (image S U) Tc) := by
  intro samplingD samplingM precision filterLoss K rho rounds bRef xiTrim epsilonRef
    hD hK hThreshold hDelta hepsilon hreverse hxi hepsilonRef0 hepsilonRef
    rawH hermRaw mu0 hmu0 hgap Original R hRawRef hRefRaw hRank hbudget hdim hrounds
  obtain ⟨a, b, hab, hb, hpc, hdr, hcard, hleft, hright, hFamily⟩ :=
    exists_uniform_native_long_interval_soft_improving_family q ell m k g tau t T0 T1
      hq hell hm hk hg htau htau1 hscale hT0 htfloor hT1 hO hR
      N p r hpr hrN hlong Φ h0 h1
  refine ⟨a, b, hab, hb, hpc, hdr, hcard, hleft, hright, ?_⟩
  intro Msoft xi upper D Delta Sbulk cuts A Y J eJ midConfig HM coords order bond Hraw hRaw
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, n, W, hn, hW, hCenter⟩ := hFamily
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, n, W, ?_⟩
  intro Fops d coord threshold good state image parent law fixedHistory
  have history (T : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1) → Fin q)))
      (hGT : Submodule.IsCloseTo (3 * tau / 200) Original T)
      (hTG : Submodule.IsCloseTo (3 * tau / 200) T Original)
      (hA : ∀ delta, delta < 1 → ∀ S : Submodule ℂ HM,
        Submodule.IsViable delta S (T.map coords.toLinearEquiv.toLinearMap) →
        Submodule.IsViable (Delta / (1 - delta) ^ 2)
          (⨆ i, S.map (Fops i).toLinearMap) (T.map coords.toLinearEquiv.toLinearMap))
      (S : Submodule ℂ HM)
      (hS : Submodule.IsViable 0.04 S (Original.map coords.toLinearEquiv.toLinearMap)) :=
    canonicalHalfSampledIntervalHistory_probability D 4 K hD (1 / (q : ℝ)) hK hThreshold
      (N + 1) q p r n rho rounds bRef Delta (3 * tau / 200) epsilonRef xiTrim
      Original R () (fun _ : Unit ↦ T) Fops S hn (fun _ ↦ hGT)
      (fun _ ↦ hTG.of_le hreverse) (fun _ ↦ hA) hDelta hepsilon
      hxi hepsilonRef0 hepsilonRef hRawRef hRefRaw hRank hbudget hdim hrounds hS
  refine ⟨hn, hW, ?_, ?_⟩
  · let point := hCenter e (fun j _ ↦ by linarith) (fun _ _ ↦ le_rfl)
    let Ghat := Classical.choose point
    let matrixCertificate := Classical.choose_spec point
    let hGhat := Classical.choose matrixCertificate
    have bounds := Classical.choose_spec matrixCertificate
    have spectral := bounds.2.2 mu0 hmu0 hgap
    obtain ⟨Kwhole, M, packet⟩ := spectral.2.2.2.2.2
    let target := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
      (E + g / 4)
    have hGT : Submodule.IsCloseTo (3 * tau / 200) Original target :=
      spectral.2.2.2.2.1
    have hTG : Submodule.IsCloseTo (3 * tau / 200) target Original :=
      spectral.2.2.2.1
    have improve (delta : ℝ) (hdelta : delta < 1) (V : Submodule ℂ HM)
        (hV : Submodule.IsViable delta V (target.map coords.toLinearEquiv.toLinearMap)) :
        Submodule.IsViable (Delta / (1 - delta) ^ 2)
          (⨆ i, V.map (Fops i).toLinearMap) (target.map coords.toLinearEquiv.toLinearMap) :=
      (packet.2.2.2.2.2.2 V delta hV hdelta).2
    intro S hS
    obtain ⟨hGood, hFailure, hParentMeas, hParentFailure, hOnGood⟩ :=
      history target hGT hTG improve S hS
    refine ⟨hGood, ?_, hParentMeas, ?_, ?_⟩
    · simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num]
        using hFailure
    · simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num]
        using hParentFailure
    · intro U hU
      exact ⟨(hOnGood U hU).2.1, (hOnGood U hU).2.2⟩
  · intro pc hp0 hp1 Fraw G
    let point := hCenter pc hp0 hp1
    let Ghat := Classical.choose point
    let matrixCertificate := Classical.choose_spec point
    let hGhat := Classical.choose matrixCertificate
    have bounds := Classical.choose_spec matrixCertificate
    refine ⟨Ghat, hGhat, bounds.1, bounds.2.1, ?_⟩
    intro original target Tc
    have spectral := bounds.2.2 mu0 hmu0 hgap
    obtain ⟨Kwhole, M, packet⟩ := spectral.2.2.2.2.2
    have hGT : Submodule.IsCloseTo (3 * tau / 200) Original target :=
      spectral.2.2.2.2.1
    have hTG : Submodule.IsCloseTo (3 * tau / 200) target Original :=
      spectral.2.2.2.1
    have improve (delta : ℝ) (hdelta : delta < 1) (V : Submodule ℂ HM)
        (hV : Submodule.IsViable delta V (target.map coords.toLinearEquiv.toLinearMap)) :
        Submodule.IsViable (Delta / (1 - delta) ^ 2)
          (⨆ i, V.map (Fops i).toLinearMap) (target.map coords.toLinearEquiv.toLinearMap) :=
      (packet.2.2.2.2.2.2 V delta hV hdelta).2
    refine ⟨spectral.1, spectral.2.1, spectral.2.2.1, hTG, hGT, ?_⟩
    intro S hS U hU
    exact ((history target hGT hTG improve S hS).2.2.2.2 U hU).1 ()

end TNLean.MPS.AreaLaw.ALVV

end PhysicalSoftIntervalHistory

section PhysicalSoftResampling

/-!
## Physical soft families on the actual finite-resampling tree

The interval families are selected once before every regional center and seed.
Their physical certificates are retained for the energy argument on the same
terminal images. The success event is the existing original-target history
event on the actual root and its internal interval list.

Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817.
**Local fix (corrected soft construction):** the soft and cluster estimates
use `docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`. Repeated sampling and the
terminal full image follow the corrected convention at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf;
the threshold uses the corrected complex sphere count at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_random_sampling_net_count.pdf.
This theorem does not identify the printed fourth-order parameter choice,
assert sharp inverse-gap dependence, or give a running-time estimate.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The terminal-image certificate retained by one physical soft interval family: geometry,
five attained regional minima, and, for every admissible center triple, a represented target
close to the ground space for which the terminal untrimmed image on the literal history of every
`0.04`-viable candidate is viable. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777--1818. -/
def IsPhysicalTerminalCertificate {L q width : ℕ} (ell : ℕ)
    (Φ : ManyBody.BondInteraction L q)
    (t : ℝ) (m D threshold rounds : ℕ) (xiInit g precision Msoft tau Delta mu : ℝ)
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (rho : ℕ)
    (J : LongIntervalIndex L width) (n : ℕ)
    (Aops : Fin n → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) : Prop :=
  let p := J.val.1
  let r := J.val.2
  let midConfig := interval L p r → Fin q
  let HM := EuclideanSpace ℂ midConfig
  let coords := Entropy.regionTensorCoordinates q (interval L p r)
  ∃ a b : ℕ, a + 2 * ell ≤ b ∧ b + 2 * ell ≤ L - 1 ∧
    p ≤ a + ell ∧ b + ell + 1 ≤ r ∧
    (interval L p r \ interval L (a + ell) (b + ell + 1)).card ≤ 2 * ell ∧
    a + 2 * ell - p ≤ 2 * ell ∧ r - (b + 1) ≤ 2 * ell ∧
  let Sbulk : Finset (Fin 5) := {0, 2, 4}
  let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
  let A := fun j : Fin 5 ↦ ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ), Φ.term i
  let Y := ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈
    ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), Φ.term i
  ∃ (e : Fin 5 → ℝ) (x : (Fin L → Fin q) → ℂ) (E : ℝ),
    star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
    (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
  ∃ W : Fin n → Matrix midConfig midConfig ℂ,
    Aops = (fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := midConfig) (W i)) ∧
    let image := canonicalHalfSampledIntervalImage L q p r D threshold rounds Aops xiInit
    let good := fun S ↦ canonicalHalfSampledIntervalHistory
      L q p r D threshold rounds (Aops) xiInit S G
    ∀ (pc : Fin 5 → ℝ)
      (_hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ pc j)
      (_hp1 : ∀ j : Fin 5, j ∈ Sbulk → pc j ≤ e j),
      let Fraw := fun j : Fin 5 ↦ (pc j : ℂ) • 1 +
        cfc (Real.softTruncation t m) (A j - (pc j : ℂ) • 1)
      let Gsoft := (∑ j, ((if j ∈ Sbulk then Fraw j else A j) - (e j : ℂ) • 1)) + Y
      ∃ (Ghat : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hGhat : Ghat.IsHermitian),
        ‖Gsoft - Ghat‖ ≤ precision ∧ ‖Ghat‖ ≤ Msoft + precision ∧
        let target := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
          (E + g / 4)
        let Tc := target.map coords.toLinearEquiv.toLinearMap
        E + ∑ j, e j = mu ∧
        target = Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
          (E + 3 * g / 4) ∧
        Module.finrank ℂ target = rho ∧
        Submodule.IsCloseTo (3 * tau / 200) target G ∧
        Submodule.IsCloseTo (3 * tau / 200) G target ∧
        ∀ S : Submodule ℂ HM,
          Submodule.IsViable 0.04 S (G.map coords.toLinearEquiv.toLinearMap) →
          ∀ U ∈ good S, Submodule.IsViable (Delta / (91 / 100 : ℝ) ^ 2)
            (image S U) Tc

open Classical in
/-- The terminal-image certificate of one physical soft family supplies the per-interval
hypothesis of the energy induction: the middle region with its attained minimum and the exact
center target. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777--1818. -/
private theorem terminalCertificate_of_isPhysicalTerminalCertificate {L q width ell : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (t : ℝ) (m D threshold rounds : ℕ) (xiInit g precision Msoft tau Delta mu : ℝ)
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (rho : ℕ) (hrho : Module.finrank ℂ G = rho)
    (J : LongIntervalIndex L width) (n : ℕ)
    (Aops : Fin n → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) :
    IsPhysicalTerminalCertificate ell Φ t m D threshold rounds xiInit g precision Msoft tau Delta
      mu G rho J n Aops →
    let l := J.val.1
    let r := J.val.2
    let coords := Entropy.regionTensorCoordinates q (interval L l r)
    let regional := fun (a b : ℕ) ↦ ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ a ≤ i.val ∧ i.val + 1 < b), Φ.term i
    ∃ u v : ℕ, l ≤ u ∧ u ≤ v ∧ v ≤ r ∧ u - l ≤ 2 * ell ∧ r - v ≤ 2 * ell ∧
      (∃ (e2 : ℝ) (x2 : (Fin L → Fin q) → ℂ), star x2 ⬝ᵥ x2 = 1 ∧
        regional u v *ᵥ x2 = (e2 : ℂ) • x2 ∧ (regional u v - (e2 : ℂ) • 1).PosSemidef) ∧
      ∃ T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ T = Module.finrank ℂ G ∧ Submodule.IsCloseTo (3 * tau / 200) G T ∧
        ∀ W : Submodule ℂ (EuclideanSpace ℂ (interval L l r → Fin q)),
          Submodule.IsViable 0.04 W (G.map coords.toLinearEquiv.toLinearMap) →
          ∀ V ∈ canonicalHalfSampledIntervalHistory L q l r D threshold rounds Aops xiInit W G,
            Submodule.IsViable (Delta / (91 / 100 : ℝ) ^ 2)
              (canonicalHalfSampledIntervalImage L q l r D threshold rounds Aops xiInit W V)
              (T.map coords.toLinearEquiv.toLinearMap) := by
  intro hcert l r coords regional
  obtain ⟨a, b, _hab, _hb, hp, hr, _hcardJ, hleft, hright, e, x, E, hx, hxe, he, _hE0, _hE4,
    W, _hW, hcenter⟩ := hcert
  obtain ⟨Ghat, hGhat, _hn1, _hn2, _hEsum, _htarget, hrank, _hclose1, hclose2, hview⟩ :=
    hcenter e (fun _ _ ↦ by linarith) (fun _ _ ↦ le_rfl)
  refine ⟨a + 2 * ell, b + 1, by omega, by omega, by omega, hleft, hright,
    ⟨e 2, x, hx, hxe 2, he 2⟩, _, hrank.trans hrho.symm, hclose2, hview⟩

open Classical in
/-- The primitive gapped chain determines the same physical soft interval
families and the actual finite-resampling tree, with a measurable joint
original-ground history event and unconditional size bounds. All family choices
precede regional centers, seed sequences and final approximation accuracies.
Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817. -/
theorem exists_physical_soft_resampling_tree
    (q : ℕ) (hq : 2 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ u K Ccount : ℕ, 2 ≤ u ∧ 1 ≤ K ∧ 1 ≤ Ccount ∧
    let g := min gamma 1
    let ell := u ^ 8
    let m := u ^ 10
    let k := u ^ 16
    let t := 3 * (m : ℝ)
    let T := (u : ℝ) ^ 9
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let tau := 1 / ((D : ℝ) ^ 24 * Msoft ^ 10)
    let precision := min 1 (tau * g ^ 2 / (20000 * (Msoft + g + 8)))
    let Delta := (2 * Real.exp (-2 * (k : ℝ) *
      Real.sqrt ((g / 2) / (Msoft + precision + 4 + g)))) ^ 2
    let width := 4 * ell
    2 ≤ D ∧ 34 ≤ Msoft ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < precision ∧ precision ≤ 1 ∧
    156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
    3 * (32 * Real.exp (-(T - g / 40 - 24) / 8) +
      (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
    3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) +
      (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
    Delta ≤ 1 / ((D : ℝ) ^ 12 * Msoft ^ 10) ∧
    3 * tau / 200 ≤ (((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2) / 100 ∧
    3 * tau / 200 ≤ 1 / 200 ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
    ∃ Cxi : ℝ, 0 < Cxi ∧ ∃ Pxi : ℕ,
    ∀ (L : ℕ)
      (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu : ℝ),
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rho := Module.finrank ℂ G
    let Z := ((L : ℝ) + 1) * ((rho : ℝ) + 1)
    let threshold := K * (rho + 1) * (L + 2) ^ 2
    let rounds := q * L
    let count := max (q ^ width) (D ^ 2 * threshold)
    ∃ xiInit : ℝ, 0 < xiInit ∧ xiInit ≤ 1 ∧ (xiInit⁻¹) ^ 2 ≤ Cxi * Z ^ Pxi ∧
    ∃ hwidth : 1 ≤ width,
    let Certificate := IsPhysicalTerminalCertificate (width := width) ell Φ t m D threshold
      rounds xiInit g precision Msoft tau Delta mu G rho
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      let thresholdFamily := fun _ : LongIntervalIndex L width ↦ threshold
      let Good := canonicalIntervalResamplingGood D rounds hwidth thresholdFamily N F xiInit G 0 L
      (∀ J : LongIntervalIndex L width, N J ≤ D ^ 2 ∧ Certificate J (N J) (F J)) ∧
      MeasurableSet Good ∧
      intervalResamplingMeasure L q rounds Goodᶜ ≤ ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2) ∧
      (L ≤ width → Good = Set.univ) ∧
      count ≤ Ccount * ((L + 1) * (rho + 1)) ^ 2 ∧
      (∀ (U : IntervalResamplingChoices L q rounds) (p r : ℕ)
        (_hpr : p ≤ r) (_hrL : r ≤ L),
        let S := balancedIntervalSpace (canonicalIntervalResamplingOperation
          D rounds thresholdFamily N F xiInit U) width hwidth p r
        Module.finrank ℂ S ≤ count ∧
          IsIntervalSpanWithRankBound L q p r count xiInit S) ∧
      ∀ U ∈ Good, IsTerminalRitzEnergyAssignment (Nat.lt_of_lt_of_le two_pos hq) hwidth Φ ell t m
        D rounds thresholdFamily N F xiInit U := by
  classical
  obtain ⟨u, hu, hnumeric, hprofile⟩ :=
    exists_physical_soft_sampling_data q hq gamma hgamma
  obtain ⟨K, Ccount, hK, hCcount, hCeq, hThreshold, C, hC, P, href⟩ := hprofile
  refine ⟨u, K, Ccount, hu, hK, hCcount, ?_⟩
  intro g ell m k t T D Msoft tau precision Delta width
  obtain ⟨Cpoly, ppoly, hCpoly, hell, hm, hk, htfloor, hTfloor, hT0,
    hD, hM, htau, htau1, hprecision, hprecision1, hO, hR, hDelta,
    hepsilon, hreverse, hSmall, hBond⟩ := hnumeric
  change 2 ≤ D at hD
  change 34 ≤ Msoft at hM
  change 0 < tau at htau
  change tau ≤ 1 at htau1
  change 0 < precision at hprecision
  change precision ≤ 1 at hprecision1
  change 156 + 2 * g ≤ t at htfloor
  change 156 + 2 * g ≤ T at hTfloor
  change g / 40 + 24 ≤ T at hT0
  change 3 * (32 * Real.exp (-(T - g / 40 - 24) / 8) +
    (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 at hO
  change 3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) +
    (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 at hR
  change Delta ≤ 1 / ((D : ℝ) ^ 12 * Msoft ^ 10) at hDelta
  change 3 * tau / 200 ≤ (((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2) / 100 at hepsilon
  change 3 * tau / 200 ≤ 1 / 200 at hreverse
  change (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 at hSmall
  change ∀ r len Q : ℕ, K * (r + 1) * (len + 2) ^ 2 ≤ Q →
    4 * D ^ 2 ≤ Q ∧ Submodule.bootstrapFailure D Q r ≤
      (1 / (q : ℝ)) / ((len : ℝ) + 2) ^ 4 at hThreshold
  clear hBond hCpoly Cpoly ppoly hCeq
  refine ⟨hD, hM, htau, htau1, hprecision, hprecision1, htfloor, hTfloor, hT0,
    hO, hR, hDelta, hepsilon, hreverse, hSmall,
    1000000 * C, mul_pos (by norm_num) hC, P + 1, ?_⟩
  clear hM hprecision hprecision1
  intro L Φ h0 h1 mu H hH hmu hgap G rho Z threshold rounds count
  obtain ⟨B, hB, Ref, hdim, hRefG, hGRef, hRefMPS, hRefBound, hxi,
    hxi1, hbudget, hinv, hcost, hschedule, hRefIntervals⟩ :=
    href L Φ h0 h1 mu hmu hgap
  clear href hdim hRefMPS hRefBound hcost
  let dRef := rho ^ 2 * B
  let bRef := dRef ^ 2
  let xiInit := 1 / (1000 * (dRef : ℝ) * Real.sqrt ((L : ℝ) + 1))
  have hwidth : 1 ≤ width := by
    change 0 < width
    dsimp only [width, ell]
    positivity
  refine ⟨xiInit, hxi, hxi1, hinv, hwidth, ?_⟩
  intro Certificate
  obtain ⟨hthreshold, hthresholdD, hfailure, hcard, hfull, hcount, htotal⟩ := hschedule
  have hg : 0 < g := lt_min hgamma zero_lt_one
  have hgapg : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + g ≤ z := by
    intro z hz
    have hbound : mu + g ≤ mu + gamma := add_le_add le_rfl (min_le_left gamma 1)
    exact (hgap z hz).imp id (fun hz' ↦ hbound.trans hz')
  let beta := (rounds : ℝ≥0∞) *
    ENNReal.ofReal ((1 / (q : ℝ)) / ((L : ℝ) + 2) ^ 4)
  obtain ⟨N, F, hFamilies, hGood, hprob, hshort, hsize⟩ :=
    exists_canonical_interval_resampling_tree_with_certificate (L := L) (q := q) (width := width)
      (D := D) (rounds := rounds) (count := count) hwidth (by omega) threshold hthreshold
      (le_max_right _ _) (le_max_left _ _)
      (fun J ↦ (hcard J.val.1 J.val.2).trans hfull)
      xiInit hxi hxi1 G beta Certificate (by
        intro J
        cases L with
        | zero =>
          have hj := J.property
          omega
        | succ L0 =>
          have hcuts : J.val.2 - J.val.1 - 1 ≤ L0 + 1 :=
            (Nat.sub_le _ 1).trans ((Nat.sub_le _ _).trans J.property.2.1)
          obtain ⟨a, b, hab, hb, hp, hr, hcardJ, hleft, hright, hFamily⟩ :=
            exists_physical_soft_interval_history q ell m k g tau t
              T T
              hq hell hm hk hg htau htau1 le_rfl hT0 htfloor hTfloor hO hR
              L0 J.val.1 J.val.2 J.property.1 J.property.2.1 J.property.2.2 Φ h0 h1
              K rho rounds bRef xiInit (1 / 100000)
              hD hK hThreshold hSmall hepsilon hreverse hxi (by norm_num) le_rfl
              mu hmu hgapg Ref hGRef hRefG
              (hRefIntervals J.val.1 J.val.2).2.2
              (hbudget _ hcuts) le_rfl ((hcard J.val.1 J.val.2).trans hfull)
          obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, n, W, hn, hW, hfixed, hcenter⟩ := hFamily
          let Fops := fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
            (n := interval (L0 + 1) J.val.1 J.val.2 → Fin q) (W i)
          refine ⟨n, Fops, ?_, hn, ?_⟩
          · refine ⟨a, b, hab, hb, hp, hr, hcardJ, hleft, hright,
              e, x, E, hx, hxe, he, hE0, hE4, W, rfl, ?_⟩
            exact hcenter
          · intro S hS
            have history := hfixed S hS
            refine ⟨?_, fun U hU ↦ (history.2.2.2.2 U hU).2⟩
            have hhist := history.2.1
            simp only [beta, Nat.cast_add, Nat.cast_one, add_assoc,
              show (1 : ℝ) + 2 = 3 by norm_num] at hhist ⊢
            exact hhist)
  refine ⟨N, F, (fun J ↦ ⟨(hFamilies J).2.1, (hFamilies J).1⟩),
    hGood, ?_, hshort, hcount, hsize, ?_⟩
  · exact hprob.trans (by simpa only [beta, mul_assoc] using htotal)
  -- The energy induction on the same families, from their terminal-image certificates.
  intro U hU
  have hq0 : 0 < q := Nat.lt_of_lt_of_le two_pos hq
  have hm2 : 2 ≤ m := hu.trans (Nat.le_self_pow (by norm_num) u)
  have hlow : ∀ z ∈ spectrum ℝ H, mu ≤ z := fun z hz ↦
    (hgap z hz).elim (fun h ↦ h.ge) (fun h ↦ by linarith)
  refine exists_successful_tree_energy_induction (ell := ell) hq0 hwidth Φ h0 h1 g hg t T m D
    hm2 hD htfloor hTfloor Delta (by positivity) mu rounds _ N F xiInit hmu hlow hDelta hR ?_ U hU
  exact fun J ↦ terminalCertificate_of_isPhysicalTerminalCertificate Φ t m D threshold rounds
    xiInit g precision Msoft tau Delta mu G rho rfl J (N J) (F J) (hFamilies J).1

end TNLean.MPS.AreaLaw.ALVV

end PhysicalSoftResampling
