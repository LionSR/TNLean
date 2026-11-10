/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGInterleavedIteration
import TNLean.MPS.AreaLaw.CanonicalSampledIntervalBounds
import TNLean.MPS.AreaLaw.AdjacentIntervalMerge
import QICLean.Probability.NativeRankUnitarySampling

/-!
# Uniform true failure for the physical canonical parent

One physical family and its word certificates are chosen before the
children and sampling seed. The native canonical Haar estimate is
composed with the existing deterministic iteration for arbitrary sampled
initial spaces. The true original-ground-space failure event is Borel
and has the prescribed uniform measure bound. Dimension and recorded
ranks hold for every seed, without viability assumptions on the history.

Source: ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558,
Figure `fig:merge-prime`, lines 1668–1670, and lines 1797–1805.

**Scope restriction (block leaves, fixed failure scale and capped gap):**
This parent theorem retains long intervals, the fixed failure scale
(L+1)^(-2), independent truncation and polynomial scales and min(gamma,1).
Its family is polynomial in the actual hard-clipped Hamiltonian. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (assignment and integer rounds):** Each round acts on the
current space, with the larger integer count documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. Adaptive tree
probability and runtime are separate assertions.
-/

open MeasureTheory
open scoped TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The physical chain chooses the actual target, reference and same
operator family before all children and seeds. Every canonical parent has
the deterministic output profile, and viable bounded children give a
uniform bound on its true original-target failure probability. -/
theorem exists_physical_dg_canonical_interval_parent_failure :
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
        (∀ (power : ℕ)
          (S : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S
            (T.map (Entropy.regionTensorCoordinates q
              (interval L p endR)).toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ w : Fin power → Fin N,
            S.map ((List.ofFn (fun j ↦ F (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
              (T.map (Entropy.regionTensorCoordinates q
                (interval L p endR)).toLinearEquiv.toLinearMap)) ∧
        ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
        (∀ (W : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)))
          (seed : Matrix.rankUnitaryProduct (Fintype.card (interval L p endR → Fin q))),
          let output := canonicalSampledIntervalInterleavedTrim L q p endR D s F xi W seed
          Module.finrank ℂ output ≤ D ^ 6 * s ^ 3 ∧
            IsIntervalSpanWithRankBound L q p endR (D ^ 6 * s ^ 3) xi output) ∧
        ∀ (k : ℕ) (hpk : p ≤ k) (hkr : k ≤ endR),
        ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
          (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k endR → Fin q))),
        Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3 →
        Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3 →
        Submodule.IsViable (3 / 200 : ℝ) S1
          (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap) →
        Submodule.IsViable (3 / 200 : ℝ) S2
          (G.map (Entropy.regionTensorCoordinates q
            (interval L k endR)).toLinearEquiv.toLinearMap) →
        let W := adjacentIntervalMerge L q p k endR hpk hkr S1 S2
        let beta : ℝ := 1 / ((L : ℝ) + 1) ^ 2
        let Bad := {seed : Matrix.rankUnitaryProduct (Fintype.card (interval L p endR → Fin q)) |
          ¬ Submodule.IsViable (3 / 200 : ℝ)
            (canonicalSampledIntervalInterleavedTrim L q p endR D s F xi W seed)
            (G.map (Entropy.regionTensorCoordinates q
              (interval L p endR)).toLinearEquiv.toLinearMap)}
        MeasurableSet Bad ∧
          Matrix.rankUnitaryHaar (Fintype.card (interval L p endR → Fin q)) Bad ≤
            ENNReal.ofReal beta := by
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfamily⟩ :=
    exists_physical_dg_interleaved_interval_iterates_with_word_powers
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hinterval⟩ :=
    hfamily L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  change 2 ≤ D at hD
  change 1 ≤ s at hs
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Uref, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro p endR hpr hrL hlong
  obtain ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, hwords, hiterate⟩ :=
    hinterval p endR hpr hrL hlong
  clear hfamily hinterval
  refine ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, hwords, ?_⟩
  intro xi hxi hxiMax
  refine ⟨fun W seed ↦ canonicalSampledIntervalInterleavedTrim_profile hD hs hN F hxi W seed, ?_⟩
  intro k hpk hkr S1 S2 hd1 hd2 hS1 hS2 W beta Bad
  let coords := Entropy.regionTensorCoordinates q (interval L p endR)
  let e := (Fintype.equivFin (interval L p endR → Fin q)).symm
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
  have hmerged := isViable_adjacentIntervalMerge hpk hkr G S1 S2 hS1 hS2
  have hQ : Module.finrank ℂ W ≤ D ^ 12 * s ^ 6 := by
    calc
      _ ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
        finrank_adjacentIntervalMerge_le hpk hkr S1 S2
      _ ≤ (D ^ 6 * s ^ 3) * (D ^ 6 * s ^ 3) := Nat.mul_le_mul hd1 hd2
      _ = _ := by ring
  have htau : tau ≤ 1 / 10000 := by
    have haSq : a ^ 2 ≤ 1 / 10000 := by nlinarith only [ha, haSmall]
    dsimp only [tau]
    linarith only [haSq]
  have hGTmap : Submodule.IsCloseTo tau
      (G.map coords.toLinearEquiv.toLinearMap) (T.map coords.toLinearEquiv.toLinearMap) :=
    (Submodule.isCloseTo_map_iff coords).mpr hGT
  have hWT : Submodule.IsViable (1 / 4 : ℝ) W (T.map coords.toLinearEquiv.toLinearMap) := by
    apply (Submodule.IsCloseTo.trans hmerged hGTmap (by norm_num)).of_le
    linarith only [htau]
  have hdimTc : Module.finrank ℂ (T.map coords.toLinearEquiv.toLinearMap) = rG := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdimT
  have hL : 1 ≤ (L : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith only [h]
  have hbeta : 0 < beta := by dsimp only [beta]; positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hL)
  have hlogbeta : Real.log (1 / beta) = 2 * Real.log ((L : ℝ) + 1) := by
    dsimp only [beta]
    rw [one_div_div, div_one, Real.log_pow]
    norm_num
  have hscale : 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta) =
      Real.log (D : ℝ) + w := by
    rw [hlogbeta]
    dsimp only [w]
    ring
  have hsampling := Submodule.rankUnitaryHaar_not_isViable_native_randomRangeSubspace_uniform_le
    (F := EuclideanSpace ℂ (↥((interval L p endR)ᶜ) → Fin q)) e hD hrG hbeta hbeta1
  rw [hscale] at hsampling
  obtain ⟨_hs, _hsize, hprob⟩ := hsampling
  have hbadSample := hprob W hQ (T.map coords.toLinearEquiv.toLinearMap) hdimTc.le hWT
  have hgood := measurableSet_isViable_canonicalSampledIntervalInterleavedTrim
    D s F xi (fun _ : Unit ↦ W) measurable_const (3 / 200 : ℝ) G
  have hm : Measurable (fun seed : Matrix.rankUnitaryProduct
      (Fintype.card (interval L p endR → Fin q)) ↦ ((() : Unit), seed)) :=
    measurable_const.prodMk measurable_id
  have hBad : MeasurableSet Bad := by
    have h := hgood.preimage hm
    change MeasurableSet {seed | Submodule.IsViable (3 / 200 : ℝ)
      (canonicalSampledIntervalInterleavedTrim L q p endR D s F xi W seed)
        (G.map coords.toLinearEquiv.toLinearMap)} at h
    exact h.compl
  refine ⟨hBad, ?_⟩
  refine (measure_mono ?_).trans hbadSample
  intro seed hbad hsampleGood
  let P := ((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  let sample := (Matrix.randomRangeSubspace P s seed).map
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  have hsampleDim : Module.finrank ℂ sample ≤ s :=
    Matrix.finrank_map_randomRangeSubspace_le P s seed
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  have hsampleViable : Submodule.IsViable (1 - a) sample
      (T.map coords.toLinearEquiv.toLinearMap) := by
    have haForm : 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)) = a := by
      change 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)) =
        3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
      rw [mul_assoc]
    rw [haForm] at hsampleGood
    exact hsampleGood
  exact hbad (hiterate xi hxi hxiMax sample hsampleDim hsampleViable).2.2.2.2

end TNLean.MPS.AreaLaw
