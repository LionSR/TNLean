/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.DGCanonicalNodeEvent
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.DGConstantNodeParent

/-!
# One canonical physical parent of the degenerate-gap tree with `k` rounds

Under Assumption (DG) of ALVV, arXiv:1602.08828v2, lines 275–279, the original Hamiltonian
determines, for every long interval, the improving family of Theorem 4.7 (`t:ais`, from
Corollary 4.6 `c:goodagsphardtrunc`) and its intermediate target, before the number of rounds, the
sampling size and the child spaces. For every `k ≥ 1` and every sampling size `s ≤ D^{2k}`, and
children of dimension at most `D^{2k} s`, the canonical parent with `k` rounds and one collective
trim fails to be `3/200`-viable for the original ground space on a set of rank-independent Haar
coordinates of measure at most the failure probability of Lemma `l:rs`. This is the fixed-child
estimate that the independent-tree failure bound composes along the tree of Theorem `t:alg1`,
lines 1777–1818.

**Scope restriction (one long parent, one final trim and capped gap):** one parent of length
greater than `4 ℓ`, one collective trim after the `k` rounds, explicit scalar tail and filter
conditions and `min γ 1`; the bound is for fixed children. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw

/-- One long physical parent of the degenerate-gap tree: for every number of rounds `k ≥ 1`,
sampling size `1 ≤ s ≤ D^{2k}` and children of dimension at most `D^{2k} s`, the canonical
parent with `k` rounds and one collective trim fails to be `3/200`-viable for the original ground
space on a set of rank-independent Haar coordinates of measure at most the failure probability of
Lemma `l:rs`. The family and its target precede `k`, `s`, the trimming radius and the children;
the reference bound precedes every parent. Auxiliary to ALVV, arXiv:1602.08828v2, `l:rs`,
lines 530–558, `l:er`, lines 597–622, `lem:trimming`, lines 660–697, and `t:alg1`,
lines 1777–1818. -/
theorem exists_physical_dg_canonical_interval_node_failure_of_power :
    ∃ K : ℝ, 0 < K ∧ ∀ (L q : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
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
    let xiMax := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    ∀ (m ell : ℕ) (t Delta : ℝ), q ≤ m → 50 ≤ m → 1 ≤ ell → 21 ≤ t →
    (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤
      (1 / (m : ℝ)) * g / 1000000 →
    (∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta) →
    let D := (m * ell ^ 2) ^ (22 * ell)
    (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 →
    ∀ (p r : ℕ), p ≤ r → r ≤ L → 4 * ell < r - p →
    ∃ (N : ℕ) (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L p r → Fin q)),
      N ≤ D ^ 2 ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      ∀ (power s : ℕ), 1 ≤ power → 1 ≤ s → s ≤ D ^ (2 * power) →
      ∀ (k : ℕ) (hpk : p ≤ k) (hkr : k ≤ r)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        (G.map (Entropy.regionTensorCoordinates q (interval L k r)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ D ^ (2 * power) * s → Module.finrank ℂ S2 ≤ D ^ (2 * power) * s →
      let W := adjacentIntervalMerge L q p k r hpk hkr S1 S2
      let Q := Module.finrank ℂ W
      let eta : ℝ := if Q ≤ s then 0 else
        (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * rG) * Q *
          Real.exp (-(s / 16 : ℝ))
      Matrix.rankUnitaryHaar (Fintype.card (interval L p r → Fin q))
        {U | ¬Submodule.IsViable (3 / 200 : ℝ)
          (canonicalSampledIntervalWordTrim L q p r F power s xi W U)
          (G.map
            (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)} ≤
        ENNReal.ofReal eta := by
  classical
  obtain ⟨K, hK, hreference⟩ := exists_physical_dg_interval_collective_trimming_bound
  refine ⟨K, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b
  obtain ⟨B, hB, hlogB, htrim⟩ :=
    hreference L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilonRef (by norm_num [epsilonRef]) (by norm_num [epsilonRef])
  refine ⟨B, hB, hlogB, ?_⟩
  intro Dref xiMax
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
      L p r hpr hrL hlong Φ h0 h1 mu hmu hgapg
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
  refine ⟨N, F, hN, ?_⟩
  intro xi hxi hxiMax power s hpower hs hspower k hpk hkr S1 S2 hS1 hS2 hd1 hd2 W Q eta
  have hbad := rankUnitaryHaar_canonical_interval_word_image_failure_le hpk hkr hD hs hpower
    hspower G T hG htarget hGT hTG hDelta htrade F himprove S1 S2 hS1 hS2 hd1 hd2
  have hdimMap : Module.finrank ℂ
      (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) =
      rG := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdim
  simp only [hdimMap] at hbad
  refine (measure_mono ?_).trans hbad
  intro U hfail himage
  apply hfail
  have hsmall : Submodule.IsViable (1 / 400 : ℝ)
      (⨆ i, (canonicalIntervalRangeSample L q p r s W U).map
        (wordFamily F power i).toLinearMap)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) := by
    rw [iSup_map_wordFamily]
    exact himage.of_le (by linarith only [htarget])
  have hradius := Real.viable_node_trimming_radius_budget (L := L) (D := Dref)
    (show r - p - 1 ≤ L by omega) hDref
  have htrimmed := htrim p r hpr hrL _ (1 / 400) (by norm_num) xi hxi hsmall
  apply htrimmed.of_le
  have hbudget : 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) *
      ((rG : ℝ) ^ 2 * (B : ℝ)) ^ 2) ≤ 1 / 250 := by
    have hbudgetMax : 4 * xiMax * Real.sqrt (((r - p - 1 : ℕ) : ℝ) *
        ((rG : ℝ) ^ 2 * (B : ℝ)) ^ 2) ≤ 1 / 250 := by
      simpa only [xiMax, Dref, Nat.cast_mul, Nat.cast_pow] using hradius.2
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hxiMax (by norm_num : (0 : ℝ) ≤ 4))
      (Real.sqrt_nonneg _)).trans hbudgetMax
  change 4 * (1 / 400 : ℝ) + 6 * (1 / 10000 : ℝ) +
    4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * ((rG : ℝ) ^ 2 * (B : ℝ)) ^ 2) ≤ 3 / 200
  linarith only [hbudget]

end TNLean.MPS.AreaLaw.ALVV
