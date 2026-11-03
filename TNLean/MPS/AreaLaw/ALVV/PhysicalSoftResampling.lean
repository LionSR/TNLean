/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.PhysicalSoftSamplingData
import TNLean.MPS.AreaLaw.ALVV.PhysicalSoftIntervalHistory
import TNLean.MPS.AreaLaw.CanonicalIntervalResamplingSelection
import TNLean.MPS.AreaLaw.CanonicalHalfSampledIntervalImage

/-!
# Physical soft families on the actual finite-resampling tree

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
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu : ℝ),
    let H := ∑ i, h i
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
    let Certificate := fun (J : LongIntervalIndex L width) (n : ℕ)
      (Aops : Fin n → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) ↦
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
        (fun i : Fin (L - 1) ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ), h i
      let Y := ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), h i
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
      ∀ (U : IntervalResamplingChoices L q rounds) (p r : ℕ)
        (_hpr : p ≤ r) (_hrL : r ≤ L),
        let S := balancedIntervalSpace (canonicalIntervalResamplingOperation
          D rounds thresholdFamily N F xiInit U) width hwidth p r
        Module.finrank ℂ S ≤ count ∧
          IsIntervalSpanWithRankBound L q p r count xiInit S := by
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
  clear hM hprecision hprecision1 hDelta
  intro L h hs h0 h1 mu H hH hmu hgap G rho Z threshold rounds count
  obtain ⟨B, hB, Ref, hdim, hRefG, hGRef, hRefMPS, hRefBound, hxi,
    hxi1, hbudget, hinv, hcost, hschedule, hRefIntervals⟩ :=
    href L h hs h0 h1 mu hmu hgap
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
              L0 J.val.1 J.val.2 J.property.1 J.property.2.1 J.property.2.2 h hs h0 h1
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
            simpa only [beta, Nat.cast_add, Nat.cast_one, add_assoc,
              show (1 : ℝ) + 2 = 3 by norm_num] using history.2.1)
  refine ⟨N, F, (fun J ↦ ⟨(hFamilies J).2.1, (hFamilies J).1⟩),
    hGood, ?_, hshort, hcount, hsize⟩
  exact hprob.trans (by simpa only [beta, mul_assoc] using htotal)

end TNLean.MPS.AreaLaw.ALVV
