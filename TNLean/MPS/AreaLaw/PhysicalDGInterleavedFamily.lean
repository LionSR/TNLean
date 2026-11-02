/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGClippedReference
import TNLean.MPS.AreaLaw.InterleavedFilterSuppression
import TNLean.MPS.AreaLaw.IndependentPhysicalDGPower
import TNLean.MPS.AreaLaw.IntervalFamilyTrimming
import QICLean.Analysis.InterleavedTrimmingParameters
import QICLean.Analysis.ViableTrimmingRadius

/-!
# Physically calibrated families for interleaved interval trimming

The original nearest-neighbour Hamiltonian supplies the actual clipped
target and tensor-factor family. Independent scales derive the tiny
original-to-clipped error and suppression at the same count. One actual
physical reference is chosen before every interval and controls every
clipped target at that accuracy. The operators precede every child space,
radius and viable input; the failure scale is fixed by the chain length.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the parameter selection, lines 1797–1805.
It derives one actual current-space family application and collective trim.
The initial sampling event, stopping envelope and adaptive probability
remain separate.

**Scope restriction (long intervals and capped gap):** The family is for
intervals longer than `4 * ell`, and the quantitative estimates use
`min gamma 1`. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (recursive assignment):** The actual family acts on the current
space; the unchanged-sample assignment and integer-round issue are recorded
in the same paper-gap note. No printed running time is asserted.
-/

open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- An actual physical improving family and a common reference give every
interleaved current-space step, with all numerical filter, clipping and
reference conditions derived. The families are fixed before the radius
and input space. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670, and lines 1797–1805. -/
theorem exists_physical_dg_interleaved_filter_family :
    ∃ Ctail C Kref : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let m := max q 50
    let w := 1 + Real.log (rG : ℝ) + 2 * Real.log ((L : ℝ) + 1)
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g) + Real.log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let s := Nat.ceil (4096 * (rG : ℝ) * (Real.log (D : ℝ) + w))
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let epsilon := 200 * tau
    let t := Ctail * (1 + Real.log (1 / g) + Real.log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
      0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let bref := 16 + Real.log (1 / g) + Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / tau)
    ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧ ∀ (p endR : ℕ), p ≤ endR → endR ≤ L → 4 * ell < endR - p →
      ∃ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (N : ℕ)
        (F : Fin N → EuclideanSpace ℂ (interval L p endR → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L p endR → Fin q)),
        N ≤ D ^ 2 ∧ Module.finrank ℂ T = rG ∧
        Submodule.IsCloseTo tau T G ∧ Submodule.IsCloseTo tau G T ∧
        Submodule.IsCloseTo (4 * tau) T U ∧ Submodule.IsCloseTo (4 * tau) U T ∧
        ∀ xi : ℝ, 0 < xi → xi ≤ xiMax → ∀ delta : ℝ, 0 ≤ delta → delta < 1 →
        ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)),
        Submodule.IsViable delta S
          (T.map (Entropy.regionTensorCoordinates q
            (interval L p endR)).toLinearEquiv.toLinearMap) →
        let f := Delta * delta / (1 - delta + Delta * delta)
        let V := intervalFamilyTrimStep L q p endR F xi S
        Module.finrank ℂ V ≤ N * Module.finrank ℂ S ∧
          IsIntervalSpanWithRankBound L q p endR (N * Module.finrank ℂ S) xi V ∧
          Submodule.IsViable (f + a / 16) V
            (T.map (Entropy.regionTensorCoordinates q
              (interval L p endR)).toLinearEquiv.toLinearMap) ∧
          Submodule.IsViable (2 * (f + a / 16 + tau)) V
            (G.map (Entropy.regionTensorCoordinates q
              (interval L p endR)).toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨Ctail, C, hCtail, hC, hparameters⟩ := Real.exists_interleaved_physical_scalar_parameters
  obtain ⟨Kref, hKref, hreference⟩ := exists_physical_dg_common_reference_for_clipped_targets
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hm : 50 ≤ m := Nat.le_max_right q 50
  obtain ⟨hell, hD, hs, ha, haSmall, htau, htau1, hepsilon, hepsilon1,
    ht, htail, htradeoff, _hlogD, hfilter⟩ := hparameters m rG L g hm hrG hg hg1
  change 21 ≤ ell at hell
  change 2 ≤ D at hD
  change 1 ≤ s at hs
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  obtain ⟨B, hB, hlogB, U, hdimU, _hUG, _hGU, hUMPS, hreferenceBudget, htargets⟩ :=
    hreference L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      a ha (haSmall.trans (by norm_num))
  refine ⟨B, hB, hlogB, U, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  have hDref : 1 ≤ Dref := by
    simpa only [Dref, one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hB
  have hDref0 : (0 : ℝ) < Dref := by exact_mod_cast (show 0 < Dref by omega)
  have hroot : 0 < Real.sqrt ((L : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hxiMax : 0 < xiMax := by dsimp only [xiMax]; positivity
  refine ⟨hxiMax, ?_⟩
  intro p endR hpr hrL hlong
  have hq : 2 ≤ q := hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hgapg : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + g ≤ z := by
    intro z hz
    rcases hgap z hz with heq | hge
    · exact Or.inl heq
    · exact Or.inr (by dsimp only [g]; linarith only [min_le_left gamma 1, hge])
  obtain ⟨T, N, F, hN, hTG, hGT, hdimT, K, Rop, hdec, hKT, hKTo, hlow, hhigh, _hwords⟩ :=
    exists_independent_long_middle_actual_dg_filter_family m q ell t g epsilon Delta
      hq (Nat.le_max_left q 50) (by omega) ht hg hg1 hepsilon hepsilon1 htail hfilter
      L p endR hpr hrL hlong h hsupp h0 h1 mu hmu hgapg
  have hepsilonTau : epsilon / 200 = tau := by dsimp only [epsilon]; ring
  rw [hepsilonTau] at hTG hGT
  obtain ⟨hTU, hUT⟩ := htargets T hGT hTG
  have hdata :
      let Tc := T.map
        (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap
      (∀ x ∈ Tc, K x ∈ Tc) ∧ (∀ z ∈ Tcᗮ, K z ∈ Tcᗮ) ∧
        (∀ x ∈ Tc, ‖x‖ ≤ ‖K x‖) ∧
        (∀ z ∈ Tcᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) := by
    dsimp only
    rw [Entropy.regionTensorCoordinates_eq_exteriorFirst]
    exact ⟨hKT, hKTo, hlow, hhigh⟩
  obtain ⟨hKT', hKTo', hlow', hhigh'⟩ := hdata
  clear hparameters hreference _hwords
  refine ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, ?_⟩
  intro xi hxi hxiMax delta hdelta0 hdelta S hS f V
  have hDelta : 0 ≤ Delta := by dsimp only [Delta]; positivity
  let xiOld := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
  have hOld := (Real.viable_node_trimming_radius_budget
    (L := L) (cuts := endR - p - 1) (D := Dref) (by omega) hDref).2
  have hbudget : xi * Real.sqrt (((endR - p - 1 : ℕ) : ℝ) * (Dref ^ 2 : ℕ)) ≤ a / 256 := by
    simp only [Nat.cast_pow]
    calc
      _ ≤ xiMax * Real.sqrt (((endR - p - 1 : ℕ) : ℝ) * (Dref : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hxiMax (Real.sqrt_nonneg _)
      _ = (250 * a / 256) *
          (4 * xiOld * Real.sqrt (((endR - p - 1 : ℕ) : ℝ) * (Dref : ℝ) ^ 2)) := by
        dsimp only [xiMax, xiOld]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (250 * a / 256) * (1 / 250) :=
        mul_le_mul_of_nonneg_left hOld (by positivity)
      _ = _ := by ring
  have hden : 0 < 1 - delta + Delta * delta := by
    nlinarith only [hdelta, mul_nonneg hDelta hdelta0]
  have hf0 : 0 ≤ f := div_nonneg (mul_nonneg hDelta hdelta0) hden.le
  have hf1 : f ≤ 1 := (div_le_one hden).mpr (by linarith only [hdelta])
  obtain ⟨hdim, hranks, hviable⟩ := isViable_intervalFamilyTrimStep_of_tensor_decomposition
    hDref (by positivity) hdelta0 hdelta hDelta hxi (show 0 < a / 64 by positivity)
    hTU hUT hUMPS F Rop K hdec hKT' hKTo' hlow' hhigh' S hS
  have herror := Real.weighted_reference_trim_error_le_filter_add ha
    (haSmall.trans (by norm_num)) hf0 hf1 (by positivity) hreferenceBudget
    (mul_nonneg hxi.le (Real.sqrt_nonneg _)) hbudget
  have htarget : Submodule.IsViable (f + a / 16) V
      (T.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) :=
    hviable.of_le herror
  have hTGmap : Submodule.IsCloseTo tau
      (T.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) :=
    (Submodule.isCloseTo_map_iff (Entropy.regionTensorCoordinates q (interval L p endR))).mpr hTG
  have herror0 : 0 ≤ f + a / 16 := add_nonneg hf0 (div_nonneg ha.le (by norm_num))
  have horiginal : Submodule.IsViable (2 * (f + a / 16 + tau)) V
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) :=
    Submodule.IsCloseTo.trans htarget hTGmap herror0
  exact ⟨hdim, hranks, htarget, horiginal⟩

end TNLean.MPS.AreaLaw
