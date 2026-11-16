/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGAutomaticRefinement
import TNLean.MPS.AreaLaw.PhysicalFlatGroundRitz
import QICLean.Analysis.RefinementOutputPolynomialBound

/-!
# Polynomial refinement of any actual viable root

One positive refinement radius and number of literal rounds precede every
initial candidate. The resulting Ritz space is extracted from that same
candidate's actual filter-and-trim iterate. The coefficient of the squared
candidate count has a polynomial bound fixed before length, multiplicity
and accuracy. No initial matrix product representation is assumed.

This is a conditional final-refinement auxiliary for ALVV,
arXiv:1602.08828v2, lines 1801–1817. It does not construct an initial tree
or identify its trimming radius with the final refinement radius.

**Scope restriction (reference gap dependence):** The reference estimate
uses the capped gap; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
**Local fix (normalized gain):** The iterate is the corrected literal raw
filter from `docs/paper-gaps/alvv16_final_filter_gain.tex`. In the flat
spectral branch zero rounds retain the given root exactly.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Any actual original-ground viable root has a polynomial-size literal
refinement and actual Ritz extraction. All refinement choices precede the
count and candidate; the gap implication includes flat spectra. Auxiliary
to ALVV, arXiv:1602.08828v2, final refinement, lines 1809–1817. -/
theorem exists_physical_same_root_polynomial_refinement
    (q Dfilter : ℕ) (hq : 1 ≤ q) (hDfilter : 1 ≤ Dfilter)
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (L : ℕ)
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
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    ∀ eta : ℝ, 0 < eta →
    let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)
    ∃ (rounds : ℕ) (xi : ℝ) (Bscale : ℕ), 0 < xi ∧ (Bscale : ℝ) ≤ C * Z ^ k ∧
      ∀ (count : ℕ) (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
      Module.finrank ℂ S0 ≤ count →
      Submodule.IsCloseTo (3 / 200) (nativeFullIntervalSpace L q S0) G →
      let S := fullIntervalFilterTrimIterate L q Kraw xi S0 rounds
      let W := nativeFullIntervalSpace L q S
      let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
      Module.finrank ℂ S ≤ count ∧ R ≤ W ∧ Module.finrank ℂ R = r ∧
        Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
        ∀ v ∈ R, IsOpenMPS L q (Bscale * count ^ 2) (fun x ↦ v x) := by
  classical
  obtain ⟨Kref, hKref, hautomatic⟩ :=
    exists_physical_dg_automatic_same_candidate_refinement
  let g := min gamma 1
  let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hu : 0 ≤ u := by
    dsimp only [u]
    have hginv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
    linarith [Real.log_nonneg hq1, Real.log_nonneg hginv]
  obtain ⟨C0, hC0, k, hpoly⟩ := Real.exists_refinement_output_polynomial_bound
    gamma g u 0 Kref Dfilter hgamma hg hg1 hu (by norm_num) hKref.le hDfilter
  refine ⟨max C0 1, lt_max_of_lt_left hC0, k, ?_⟩
  intro L h hs h0 h1 mu H hH hmu hgap G r Kraw eta heta Z
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  by_cases hexcited : ∃ nu ∈ spectrum ℝ H, mu < nu
  · obtain ⟨nu, hnu, hmunu⟩ := hexcited
    let A := ‖H‖ - mu
    let c := gamma / A
    let rho := eta * gamma / (2 * A + eta * gamma)
    let rounds := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
    obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
      physical_dg_normalized_ground_filter_spec h h0 mu nu gamma hgamma hmu hnu hmunu hgap
    have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
    have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
      (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
    have hnorm : ‖H‖ ≤ ((L - 1 : ℕ) : ℝ) := by
      simpa using norm_sum_le_of_le (Finset.univ : Finset (Fin (L - 1)))
        (fun i _ ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg (h i) (h0 i)).mpr (h1 i))
    have hAL : A ≤ (L : ℝ) + 1 := by
      have hlen : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 1 := by
        exact_mod_cast (show L - 1 ≤ L + 1 by omega)
      dsimp only [A]
      linarith only [hnorm, hmu0, hlen]
    obtain ⟨B, hB, hlogB, hprecision⟩ :=
      hautomatic L q h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
        1 Dfilter (by norm_num) hDfilter eta heta
    let b := r ^ 2 * B
    let common := max 1 b
    let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / (c * rho))
    let xi := 1 / (1000 * ((common * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
    obtain ⟨_U, _hdimU, _hUG, _hGU, _hUMPS, hxi, _hxiTree, _hxiSource, hterminal⟩ := hprecision
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hDreal : (1 : ℝ) ≤ Dfilter := by exact_mod_cast hDfilter
    have hlogs : 1 ≤ 1 + Real.log (r : ℝ) + Real.log (Dfilter : ℝ) + Real.log 2 := by
      linarith only [Real.log_nonneg hrR, Real.log_nonneg hDreal,
        Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hsampleOne : (1 : ℝ) ≤
        4097 * (r : ℝ) * (1 + Real.log (r : ℝ) + Real.log (Dfilter : ℝ) + Real.log 2) :=
      (by linarith only [hrR] : (1 : ℝ) ≤ 4097 * (r : ℝ)).trans
        (le_mul_of_one_le_right (by positivity) hlogs)
    have hbudget := hpoly L r A eta hr hgammaA hAL heta
      1 B (by norm_num) hB (by norm_num) hlogB 1
        (by simpa only [Nat.cast_one] using hsampleOne)
    have hb1 : 1 ≤ b :=
      one_le_mul_of_one_le_of_one_le (Nat.one_le_pow 2 r hr) hB
    have hcommon : common = r ^ 2 * B := max_eq_right hb1
    have htreeCommon : max (r ^ 2 * 1) (r ^ 2 * B) = common := by
      rw [hcommon, Nat.mul_one,
        max_eq_right (le_mul_of_one_le_right (Nat.zero_le (r ^ 2)) hB)]
    change ((1000000 * (max (r ^ 2 * 1) (r ^ 2 * B) * N) ^ 2 * (L + 1) *
      (Dfilter ^ 6 * 1 ^ 3) ^ 2 : ℕ) : ℝ) ≤ C0 * Z ^ k at hbudget
    rw [htreeCommon] at hbudget
    simp only [one_pow, mul_one] at hbudget
    let Bscale := 1000000 * (common * N) ^ 2 * (L + 1)
    have hscale : (Bscale : ℝ) ≤ C0 * Z ^ k := by
      have hDcount : 1 ≤ (Dfilter ^ 6) ^ 2 :=
        Nat.one_le_pow 2 _ (Nat.one_le_pow 6 Dfilter hDfilter)
      have hcost : Bscale ≤ Bscale * (Dfilter ^ 6) ^ 2 :=
        le_mul_of_one_le_right (Nat.zero_le Bscale) hDcount
      exact (show (Bscale : ℝ) ≤ ((Bscale * (Dfilter ^ 6) ^ 2 : ℕ) : ℝ) by
        exact_mod_cast hcost).trans hbudget
    refine ⟨rounds, xi, Bscale, hxi,
      hscale.trans (mul_le_mul_of_nonneg_right (le_max_left C0 1) (by positivity)), ?_⟩
    intro count S0 hcount hclose S W R
    obtain ⟨_hn, _hcloseW, hdimS, hRW, hdimR, hGR, hRG, hMPS⟩ :=
      hterminal count S0 hcount hclose
    exact ⟨hdimS, hRW, hdimR, hGR, hRG, hMPS⟩
  · have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by
      linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      linarith only [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have heta1 : (1 : ℝ) ≤ 1 + 1 / eta := le_add_of_nonneg_right (by positivity)
    have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hL1 hr1) heta1
    refine ⟨0, 1, 1, by norm_num, ?_, ?_⟩
    · simpa only [Nat.cast_one] using
        (one_le_mul_of_one_le_of_one_le (le_max_right C0 1)
          (one_le_pow₀ hZ : (1 : ℝ) ≤ Z ^ k))
    · intro count S0 hcount hclose S W R
      obtain ⟨_hGtop, _hS0top, _hSsame, _hWG, hRW, hdimR, hGR, hRG, _hrcount, hMPS⟩ :=
        flat_ground_same_root_ritz_exact hH mu gamma (3 / 200) hgamma hmu hgap
          hexcited S0 hcount hclose (by norm_num) 1
      have hdimS : Module.finrank ℂ S ≤ count := by
        change Module.finrank ℂ S0 ≤ count
        exact hcount
      refine ⟨hdimS, hRW.le, hdimR,
        hGR.of_le (by positivity), hRG.of_le (by positivity), ?_⟩
      intro v hv
      simpa only [one_mul] using (hMPS v hv).2.mono
        (by simpa only [pow_two] using Nat.le_mul_self count)

end TNLean.MPS.AreaLaw
