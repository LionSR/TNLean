/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.NativeLongIntervalSoftFamily
import TNLean.MPS.AreaLaw.CanonicalIntervalRawProbability

/-!
# Physical soft families and their original-ground sampling histories

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
      (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
      (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (h i) (interval (N + 1) i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
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
    let Hraw := ∑ i, h i
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
    let A := fun j : Fin 5 ↦ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ), h i
    let Y := ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ i.val + 1 ∈
      ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), h i
    let J := interval (N + 1) p r
    let eJ := intervalShiftOrderIso hpr hrN
    let midConfig := J → Fin q
    let HM := EuclideanSpace ℂ midConfig
    let coords := Entropy.regionTensorCoordinates q J
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / (t * (2 : ℝ) ^ (m + 1)))))/
        (-Real.log (2 * (Real.exp (1 / 3 : ℝ) - 1)))⌉₊
    let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
    let Hraw := ∑ i, h i
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
      N p r hpr hrN hlong h hs h0 h1
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
