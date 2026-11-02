/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalSampledImage
import TNLean.MPS.AreaLaw.IndependentPhysicalDGPower
import TNLean.MPS.AreaLaw.PhysicalDGIntervalTrimming
import QICLean.Analysis.ViableTrimmingRadius

/-!
# One actual sampled and trimmed physical parent

The original Hamiltonian determines the improving target and actual finite
family before the child spaces and Haar sample. A common physical reference
bound is fixed before all parent intervals. Every unitary in a measurable
success event gives the literal sampled word-image and its actual collective
trim, with error at most `3/200` for the same original full ground space.

**Scope restriction (one long parent and capped gap):** This is one parent
with length greater than `4 * ell`, explicit independent scalar tail/filter
conditions and `min gamma 1`. It is not the sampled tree, the uniform choice
of the sampling size, or the efficient source algorithm. Gap dependence is
documented in `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (complex sphere net count):** The event uses the corrected net
count documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_random_sampling_net_count.pdf.
The event is for fixed child spaces; no adaptive measurability is asserted.
-/

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw

/-- One actual long physical parent has a measurable Haar-success event for
its literal sampled-word image and collective trim. The target and family
are constructed before all child spaces and powers; the common reference
bound is chosen before every parent interval. No spectral basis, tensor
factor, rank, overlap or final viable-space witness is supplied.
Supporting ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558, `l:er`,
lines 597–622, `lem:trimming`, lines 660–697, and `t:alg1`, lines 1777–1817. -/
theorem exists_physical_dg_sampled_interval_node_event :
    ∃ K : ℝ, 0 < K ∧ ∀ (L q : ℕ),
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
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let epsilonRef : ℝ := 1 / 10000
    let b := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log b) ∧
    let Dref := rG ^ 2 * B
    let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    ∀ (m ell : ℕ) (t Delta : ℝ), q ≤ m → 50 ≤ m → 1 ≤ ell → 21 ≤ t →
    (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤
      (1 / (m : ℝ)) * g / 1000000 →
    (∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta) →
    let D := (m * ell ^ 2) ^ (22 * ell)
    (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 →
    ∀ (p r : ℕ), p ≤ r → r ≤ L → 4 * ell < r - p →
    ∃ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (N : ℕ)
      (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L p r → Fin q)),
      N ≤ D ^ 2 ∧ Module.finrank ℂ T = rG ∧
      ∀ (k s : ℕ) (hpk : p ≤ k) (hkr : k ≤ r), 1 ≤ s →
      ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        (G.map (Entropy.regionTensorCoordinates q (interval L k r)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3 → Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3 →
      let W := adjacentIntervalMerge L q p k r hpk hkr S1 S2
      let Q := Module.finrank ℂ W
      let power := Nat.clog D (D ^ 2 * s)
      let eta : ℝ := if Q ≤ s then 0 else
        (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * rG) * Q *
          Real.exp (-(s / 16 : ℝ))
      ∃ Good : Set (Matrix.unitaryGroup (Fin Q) ℂ),
        MeasurableSet Good ∧ Matrix.unitaryHaar (Fin Q) Goodᶜ ≤ ENNReal.ofReal eta ∧
        1 - ENNReal.ofReal eta ≤ Matrix.unitaryHaar (Fin Q) Good ∧
        ∀ U ∈ Good,
          let V := Submodule.sampledWordImage F power s W U
          let basis := stdOrthonormalBasis ℂ V
          let output := intervalTrimSubspace L q p r xi
            (fun i ↦ (basis i : EuclideanSpace ℂ (interval L p r → Fin q)))
          Module.finrank ℂ output ≤ D ^ 6 * s ^ 3 ∧
            Submodule.IsViable (3 / 200 : ℝ) output
              (G.map
                (Entropy.regionTensorCoordinates q
                  (interval L p r)).toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨K, hK, hreference⟩ := exists_physical_dg_interval_collective_trimming_bound
  refine ⟨K, hK, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b
  obtain ⟨B, hB, hlogB, htrim⟩ :=
    hreference L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilonRef (by norm_num [epsilonRef]) (by norm_num [epsilonRef])
  refine ⟨B, hB, hlogB, ?_⟩
  intro Dref xi
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
  have hDref : 1 ≤ Dref := by dsimp only [Dref]; nlinarith only [hrG, hB]
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hgapg : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + g ≤ z := by
    intro z hz
    rcases hgap z hz with hzmu | hzlower
    · exact Or.inl hzmu
    · exact Or.inr (by dsimp only [g]; linarith only [min_le_left gamma 1, hzlower])
  intro m ell t Delta hqm hm hell ht htail hfilter D htrade p r hpr hrL hlong
  have hmR : (50 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  let epsilon : ℝ := 1 / (m : ℝ)
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hepsilon1 : epsilon ≤ 1 := by
    dsimp only [epsilon]
    apply (div_le_iff₀ hm0).mpr
    linarith only [hmR]
  have htarget : epsilon / 200 ≤ 1 / 10000 := by
    dsimp only [epsilon]
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < (m : ℝ) * 200)).mpr
    linarith only [hmR]
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg ell
  have hDelta : 0 ≤ Delta :=
    (sq_nonneg _).trans (hfilter 1 (by norm_num) (by linarith only [ht, hell0]))
  have hbase : 2 ≤ m * ell ^ 2 := by
    have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell hell
    nlinarith only [hm, hell2]
  have hD : 2 ≤ D := Nat.one_lt_pow (by omega : 22 * ell ≠ 0) (by omega)
  obtain ⟨T, N, F, hN, hTG, hGT, hdim, hwords⟩ :=
    exists_independent_long_middle_actual_dg_word_family m q ell t g epsilon Delta
      hq hqm hell ht hg hg1 hepsilon hepsilon1 htail hfilter
      L p r hpr hrL hlong h hsupp h0 h1 mu hmu hgapg
  have himprove : ∀ (a : ℕ)
      (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (delta : ℝ),
      Submodule.IsViable delta S
        (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) →
      delta < 1 →
      Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2)
        (⨆ w : Fin a → Fin N, S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (T.map (Entropy.regionTensorCoordinates q
                  (interval L p r)).toLinearEquiv.toLinearMap) := by
    intro a S delta hS hdelta
    rw [Entropy.regionTensorCoordinates_eq_exteriorFirst] at hS ⊢
    exact (hwords a S delta hS hdelta).2
  refine ⟨T, N, F, hN, hdim, ?_⟩
  intro k s hpk hkr hs S1 S2 hS1 hS2 hd1 hd2 W Q power eta
  obtain ⟨Good, hGood, hbad, hprob, himages⟩ :=
    exists_measurable_interval_word_image_event hpk hkr hD hs G T hG
      (by positivity : 0 ≤ epsilon / 200)
      htarget hGT hTG hDelta htrade F hN himprove S1 S2 hS1 hS2 hd1 hd2
  have hdimMap : Module.finrank ℂ
      (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) =
      rG := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdim
  rw [hdimMap] at hbad hprob
  refine ⟨Good, hGood, hbad, hprob, ?_⟩
  intro U hU V basis output
  obtain ⟨hdimV, hviableV⟩ := himages U hU
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hden : (1 : ℝ) ≤ (s : ℝ) ^ 2 := one_le_pow₀ hsR
  have hratio : (1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 ≤
      (1024 / 9 : ℝ) * (1 / 100000) := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hden)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hden
      (by norm_num : (0 : ℝ) ≤ (1024 / 9 : ℝ) * (1 / 100000))
  have hsmall : Submodule.IsViable (1 / 400 : ℝ) V
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) :=
    hviableV.of_le (by linarith only [hratio, htarget])
  have hradius := Real.viable_node_trimming_radius_budget (L := L) (D := Dref)
    (show r - p - 1 ≤ L by omega) hDref
  have htrimmed := htrim p r hpr hrL V (1 / 400) (by norm_num) xi hradius.1 hsmall
  constructor
  · exact (finrank_intervalTrimSubspace_le L q p r xi
      (fun i ↦ (basis i : EuclideanSpace ℂ (interval L p r → Fin q)))).trans hdimV
  · apply htrimmed.of_le
    have hbudget : 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) *
        ((rG : ℝ) ^ 2 * (B : ℝ)) ^ 2) ≤ 1 / 250 := by
      simpa only [xi, Dref, Nat.cast_mul, Nat.cast_pow] using hradius.2
    change 4 * (1 / 400 : ℝ) + 6 * (1 / 10000 : ℝ) +
      4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * ((rG : ℝ) ^ 2 * (B : ℝ)) ^ 2) ≤ 3 / 200
    linarith only [hbudget]

end TNLean.MPS.AreaLaw
