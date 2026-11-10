/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalGroundReferencePolynomial
import TNLean.MPS.AreaLaw.IntervalReferenceTrimming
import QICLean.Analysis.ViableTrimmingRadius

/-!
# A common original-ground reference and trimming radius

One reference space, constructed from the original ground space, controls every
interval with its full exterior. Its squared whole-chain bond is the reference
rank. A single positive radius is fixed before all intervals, candidates, and
samples. The exact weighted loss has no candidate-dimension factor. The latter
appears separately in the coarse polynomial ceiling for the output bond.

This supports ALVV, arXiv:1602.08828v2, collective trimming, lines 660–697,
and `t:alg1`, lines 1801–1813. No sampled output is used to construct the reference.
The asserted polynomial dependence is at fixed local dimension and gap; no
running-time or sharp inverse-gap estimate is asserted. The trimming loss is the
corrected weighted reference loss, recorded in
https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The original ground space supplies one fixed reference and one positive
trimming radius for every interval. The two-boundary reference rank, exact
weighted loss, inverse-square profile, and separate candidate-count cost are
retained. Supporting ALVV, arXiv:1602.08828v2, lines 660–697 and 1801–1813. -/
theorem exists_physical_ground_reference_trimming_profile
    (q : ℕ) (hq : 1 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
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
        0 < xi ∧
        (∀ kCuts : ℕ, kCuts ≤ L →
          xi * Real.sqrt ((kCuts : ℝ) * (bRef : ℝ)) ≤ 1 / 1000) ∧
        (xi⁻¹) ^ 2 ≤ 1000000 * C * Z ^ (P + 1) ∧
        (∀ count : ℕ,
          ((1000000 * bRef * (L + 1) * count ^ 2 : ℕ) : ℝ) ≤
            1000000 * C * Z ^ (P + 1) * (count : ℝ) ^ 2) ∧
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
  obtain ⟨C, hC, P, href⟩ :=
    exists_physical_ground_reference_polynomial q hq gamma hgamma
  refine ⟨C, hC, P, ?_⟩
  intro L h hs h0 h1 mu H hH hmu hgap G r Z
  obtain ⟨B, hB, hbound, U, hdim, hUG, hGU, hUMPS⟩ :=
    href L h hs h0 h1 mu hmu hgap
  let d := r ^ 2 * B
  let bRef := d ^ 2
  let xi := 1 / (1000 * (d : ℝ) * Real.sqrt ((L : ℝ) + 1))
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hd : 1 ≤ d := by
    change 0 < d
    dsimp only [d]
    positivity
  have hxi : 0 < xi := (Real.viable_node_trimming_radius_budget
    (L := L) (cuts := 0) (Nat.zero_le L) hd).1
  have hbudget (kCuts : ℕ) (hk : kCuts ≤ L) :
      xi * Real.sqrt ((kCuts : ℝ) * (bRef : ℝ)) ≤ 1 / 1000 := by
    have h := (Real.viable_node_trimming_radius_budget hk hd).2
    change 4 * xi * Real.sqrt ((kCuts : ℝ) * (d : ℝ) ^ 2) ≤ 1 / 250 at h
    dsimp only [bRef]
    push_cast
    linarith only [h]
  have hinv : (xi⁻¹) ^ 2 = 1000000 * (bRef : ℝ) * ((L : ℝ) + 1) := by
    dsimp only [xi, bRef]
    rw [one_div, inv_inv, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    push_cast
    norm_num
  have hLZ : (L : ℝ) + 1 ≤ Z := by
    dsimp only [Z]
    nlinarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hcost : 1000000 * (bRef : ℝ) * ((L : ℝ) + 1) ≤
      1000000 * C * Z ^ (P + 1) := by
    calc
      _ ≤ 1000000 * (C * Z ^ P) * Z := by gcongr
      _ = _ := by rw [pow_succ]; ring
  refine ⟨B, hB, U, hdim, hUG, hGU, hUMPS, hbound, hxi, hbudget, ?_, ?_, ?_⟩
  · exact hinv.le.trans hcost
  · intro count
    push_cast
    simpa only [bRef, d, Nat.cast_pow, Nat.cast_mul] using
      mul_le_mul_of_nonneg_right hcost (sq_nonneg (count : ℝ))
  · intro p s F
    refine ⟨(Submodule.isCloseTo_map_iff F).mpr hUG,
      (Submodule.isCloseTo_map_iff F).mpr hGU, ?_⟩
    intro t ht j hj
    exact schmidtRank_cutEnvVector_interval_reference_le hd hUMPS p s ht j hj

end TNLean.MPS.AreaLaw
