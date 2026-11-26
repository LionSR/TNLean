/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.Models
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalWordTrim
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.MergeRounds
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGIntervalTrimming

/-!
# One physical parent of the degenerate-gap tree with `k` rounds

Under Assumption (DG) of ALVV, arXiv:1602.08828v2, lines 275–279, the original Hamiltonian
determines, for every long interval, the improving family of Theorem 4.7 (`t:ais`, from
Corollary 4.6 `c:goodagsphardtrunc`)
and its intermediate target, before the number of rounds, the sampling size and the
child spaces. For every `k ≥ 1` and every sampling size `s ≤ D^{2k}`, children of dimension at most
`D^{2k} s` have a measurable Haar success event, with the failure probability of Lemma `l:rs`, on
which the literal sampled word image with `k` rounds and its collective trim are `3/200`-viable for
the original ground space. This is the node step of Theorem `t:alg1`, lines 1777–1818, at the
source's number of rounds.

**Scope restriction (one long parent, one final trim and capped gap):** one parent of length
greater than `4 ℓ`, one collective trim after the `k` rounds, explicit scalar tail and filter
conditions and `min γ 1`; the event is for fixed children. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.ALVV.rankUnitaryHaar_canonical_interval_word_image_failure_le`: the canonical
  sample of one degenerate-gap parent with `k` rounds.
* `TNLean.MPS.AreaLaw.ALVV.exists_physical_dg_canonical_interval_node_failure_of_power`: one
  canonical physical parent of the degenerate-gap tree with `k` rounds.
* `TNLean.MPS.AreaLaw.ALVV.exists_measurable_interval_word_image_event_of_power`: one sampled parent
  of the degenerate-gap tree with `k` rounds.
-/

open ManyBody (interval)
open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

section DGConstantNodeEvent

/-!
## One sampled parent of the degenerate-gap tree with `k` rounds

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, merges two viable spaces of dimension
at most `D^{2k} s`, samples `s` vectors of the merged space, and applies `k` rounds of the improving
family of Theorem 4.7 (`t:ais`, from Corollary 4.6 `c:goodagsphardtrunc`), a family of at most
`D²` operators. This file
proves, for one long parent and every number of rounds `k ≥ 1` with `s ≤ D^{2k}`, that the literal
sampled word image followed by one collective trim is `3/200`-viable for the original ground space
on a measurable Haar event with the failure probability of Lemma `l:rs`. The earlier node event
takes the larger power `⌈log_D (D² s)⌉` and the children of dimension `D⁶ s³`.

**Scope restriction (one long parent, one final trim and capped gap):** one parent of length
greater than `4 ℓ`, with the trim applied once after the `k` rounds rather than after each round,
explicit scalar tail and filter conditions, and `min γ 1` in place of `γ`; the event is for fixed
children. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open TNLean.MPS.AreaLaw

/-- The sampled word image of a merged space has a measurable Haar success event at every
number of rounds `k ≥ 1` with `s ≤ D^{2k}` and children of dimension at most `D^{2k} s`; on it
the image is viable for the original target `G` with error
`2 ((1024/9) · 10⁻⁵ + ε)`, through the intermediate target `T` of the family. Auxiliary to
ALVV, arXiv:1602.08828v2, Lemmas `l:rs` and `l:er`, lines 530–558 and 597–622, and
Theorem `t:alg1`, lines 1777–1818. -/
theorem exists_measurable_interval_word_image_event_of_power
    {L q p k r D N s power : ℕ} (hpk : p ≤ k) (hkr : k ≤ r) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (hpower : 1 ≤ power) (hspower : s ≤ D ^ (2 * power))
    (G T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (hG : G ≠ ⊥)
    {epsilon Delta : ℝ} (hepsilon1 : epsilon ≤ 1 / 10000)
    (hGT : Submodule.IsCloseTo epsilon G T) (hTG : Submodule.IsCloseTo epsilon T G)
    (hDelta : 0 ≤ Delta) (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (himprove : ∀ (a : ℕ)
      (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (delta : ℝ),
      Submodule.IsViable delta S
        (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) →
      delta < 1 →
      Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2)
        (⨆ w : Fin a → Fin N, S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (h1 : Submodule.IsViable (3 / 200 : ℝ) S1
      (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap))
    (h2 : Submodule.IsViable (3 / 200 : ℝ) S2
      (G.map (Entropy.regionTensorCoordinates q (interval L k r)).toLinearEquiv.toLinearMap))
    (hd1 : Module.finrank ℂ S1 ≤ D ^ (2 * power) * s)
    (hd2 : Module.finrank ℂ S2 ≤ D ^ (2 * power) * s) :
    let C := Entropy.regionTensorCoordinates q (interval L p r)
    let W := adjacentIntervalMerge L q p k r hpk hkr S1 S2
    let Q := Module.finrank ℂ W
    let eta : ℝ := if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^
        (2 * Module.finrank ℂ (T.map C.toLinearEquiv.toLinearMap)) * Q *
          Real.exp (-(s / 16 : ℝ))
    ∃ Good : Set (Matrix.unitaryGroup (Fin Q) ℂ),
      MeasurableSet Good ∧ Matrix.unitaryHaar (Fin Q) Goodᶜ ≤ ENNReal.ofReal eta ∧
      1 - ENNReal.ofReal eta ≤ Matrix.unitaryHaar (Fin Q) Good ∧
      ∀ U ∈ Good,
        Submodule.IsViable (2 * ((1024 / 9 : ℝ) * (1 / 100000) + epsilon))
          (Submodule.sampledWordImage F power s W U)
          (G.map C.toLinearEquiv.toLinearMap) := by
  intro C W Q eta
  have hmerged := isViable_adjacentIntervalMerge hpk hkr G S1 S2 h1 h2
  have hGmap : G.map C.toLinearEquiv.toLinearMap ≠ ⊥ :=
    (Submodule.map_ne_bot_iff (e := C.toLinearEquiv)).mpr hG
  have hW : W ≠ ⊥ :=
    Submodule.isViable_ne_bot_of_target_ne_bot hmerged (by norm_num) hGmap
  have hQ0 : 0 < Q := Nat.zero_lt_of_lt (Submodule.one_le_finrank_iff.mpr hW)
  have hQbound : Q ≤ (D ^ (2 * power) * s) ^ 2 := by
    calc
      Q ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
        finrank_adjacentIntervalMerge_le hpk hkr S1 S2
      _ ≤ (D ^ (2 * power) * s) * (D ^ (2 * power) * s) := Nat.mul_le_mul hd1 hd2
      _ = (D ^ (2 * power) * s) ^ 2 := by ring
  have hGTmap := (Submodule.isCloseTo_map_iff C).mpr hGT
  have hTGmap := (Submodule.isCloseTo_map_iff C).mpr hTG
  have hWT : Submodule.IsViable (1 / 4 : ℝ) W (T.map C.toLinearEquiv.toLinearMap) := by
    apply (Submodule.IsCloseTo.trans hmerged hGTmap (by norm_num)).of_le
    linarith only [hepsilon1]
  obtain ⟨_hc, herror⟩ := merge_power_error_le hD hpower hspower hQ0 hQbound hDelta htrade
  obtain ⟨Good, hGood, hbad, hprob, houtput⟩ :=
    Submodule.exists_measurable_sampledWordImage_event F
      (T.map C.toLinearEquiv.toLinearMap) Delta himprove power s hs W hW hWT (by norm_num)
  refine ⟨Good, hGood, hbad, hprob, ?_⟩
  intro U hU
  obtain ⟨_hdimension, hfiltered⟩ := houtput U hU
  have hback := Submodule.IsCloseTo.trans hfiltered hTGmap (by positivity)
  exact hback.of_le (by linarith only [herror])

end DGConstantNodeEvent

section DGConstantNodeParent

open TNLean.MPS.AreaLaw

/-- One long physical parent of the degenerate-gap tree has, for every number of rounds `k ≥ 1`
and sampling size `1 ≤ s ≤ D^{2k}`, a measurable Haar success event for children of dimension at
most `D^{2k} s`; on it the literal sampled word image with `k` rounds and its collective trim
are `3/200`-viable for the original ground space. The family and its target precede `k`, `s`,
the trimming radius and the children; the reference bound precedes every parent. Auxiliary to
ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558, `l:er`, lines 597–622, `lem:trimming`,
lines 660–697, and `t:alg1`, lines 1777–1818. -/
theorem exists_physical_dg_sampled_interval_node_event_of_power :
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
      ∃ Good : Set (Matrix.unitaryGroup (Fin Q) ℂ),
        MeasurableSet Good ∧ Matrix.unitaryHaar (Fin Q) Goodᶜ ≤ ENNReal.ofReal eta ∧
        ∀ U ∈ Good,
          Submodule.IsViable (3 / 200 : ℝ) (sampledIntervalTrim L q p r F power s xi W U)
            (G.map
              (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) := by
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
  obtain ⟨Good, hGood, hbad, -, himages⟩ :=
    exists_measurable_interval_word_image_event_of_power hpk hkr hD hs hpower hspower G T hG
      htarget hGT hTG hDelta htrade F himprove
      S1 S2 hS1 hS2 hd1 hd2
  have hdimMap : Module.finrank ℂ
      (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) =
      rG := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdim
  rw [hdimMap] at hbad
  refine ⟨Good, hGood, hbad, ?_⟩
  intro U hU
  have hsmall : Submodule.IsViable (1 / 400 : ℝ) (Submodule.sampledWordImage F power s W U)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) :=
    (himages U hU).of_le (by linarith only [htarget])
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

end DGConstantNodeParent

section DGCanonicalNodeEvent

/-!
## The canonical sample of one degenerate-gap parent with `k` rounds

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, merges two viable spaces of dimension
at most `D^{2k} s`, samples `s` vectors of the merged space and applies `k` rounds of the improving
family of Theorem 4.7 (`t:ais`, from Corollary 4.6 `c:goodagsphardtrunc`). This file bounds, for
fixed children, the Haar measure of the set of rank-independent coordinates on which the image of
the canonical range sample under all words of length `k` fails to be viable for the original ground
space. The bound is the failure probability of Lemma `l:rs`. The companion event for a sample drawn
from the unitary group of the merged dimension is in `DGConstantNodeEvent`.

**Scope restriction (one long parent, one final trim and capped gap):** one parent of length
greater than `4 ℓ`, with the trim applied once after the `k` rounds rather than after each round,
explicit scalar tail and filter conditions, and `min γ 1` in place of `γ`; the bound is for fixed
children. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open TNLean.MPS.AreaLaw

/-- For fixed children of dimension at most `D^{2k} s`, every number of rounds `k ≥ 1` with
`s ≤ D^{2k}`, and the canonical range sample of the merged space, the image under all words of
length `k` fails to be viable for the original target `G` with error
`2 ((1024/9) · 10⁻⁵ + ε)` on a set of coordinates of rank-independent Haar measure at most the
failure probability of Lemma `l:rs`. Auxiliary to ALVV, arXiv:1602.08828v2, Lemmas `l:rs` and
`l:er`, lines 530–558 and 597–622, and Theorem `t:alg1`, lines 1777–1818. -/
theorem rankUnitaryHaar_canonical_interval_word_image_failure_le
    {L q p k r D N s power : ℕ} (hpk : p ≤ k) (hkr : k ≤ r) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (hpower : 1 ≤ power) (hspower : s ≤ D ^ (2 * power))
    (G T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (hG : G ≠ ⊥)
    {epsilon Delta : ℝ} (hepsilon1 : epsilon ≤ 1 / 10000)
    (hGT : Submodule.IsCloseTo epsilon G T) (hTG : Submodule.IsCloseTo epsilon T G)
    (hDelta : 0 ≤ Delta) (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (himprove : ∀ (a : ℕ)
      (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (delta : ℝ),
      Submodule.IsViable delta S
        (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) →
      delta < 1 →
      Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2)
        (⨆ w : Fin a → Fin N, S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (T.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (h1 : Submodule.IsViable (3 / 200 : ℝ) S1
      (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap))
    (h2 : Submodule.IsViable (3 / 200 : ℝ) S2
      (G.map (Entropy.regionTensorCoordinates q (interval L k r)).toLinearEquiv.toLinearMap))
    (hd1 : Module.finrank ℂ S1 ≤ D ^ (2 * power) * s)
    (hd2 : Module.finrank ℂ S2 ≤ D ^ (2 * power) * s) :
    let C := Entropy.regionTensorCoordinates q (interval L p r)
    let W := adjacentIntervalMerge L q p k r hpk hkr S1 S2
    let Q := Module.finrank ℂ W
    let eta : ℝ := if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^
        (2 * Module.finrank ℂ (T.map C.toLinearEquiv.toLinearMap)) * Q *
          Real.exp (-(s / 16 : ℝ))
    Matrix.rankUnitaryHaar (Fintype.card (interval L p r → Fin q))
      {U | ¬Submodule.IsViable (2 * ((1024 / 9 : ℝ) * (1 / 100000) + epsilon))
        (⨆ w : Fin power → Fin N, (canonicalIntervalRangeSample L q p r s W U).map
          (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (G.map C.toLinearEquiv.toLinearMap)} ≤ ENNReal.ofReal eta := by
  intro C W Q eta
  have hmerged := isViable_adjacentIntervalMerge hpk hkr G S1 S2 h1 h2
  have hGmap : G.map C.toLinearEquiv.toLinearMap ≠ ⊥ :=
    (Submodule.map_ne_bot_iff (e := C.toLinearEquiv)).mpr hG
  have hW : W ≠ ⊥ :=
    Submodule.isViable_ne_bot_of_target_ne_bot hmerged (by norm_num) hGmap
  have hQ0 : 0 < Q := Nat.zero_lt_of_lt (Submodule.one_le_finrank_iff.mpr hW)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQbound : Q ≤ (D ^ (2 * power) * s) ^ 2 := by
    calc
      Q ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
        finrank_adjacentIntervalMerge_le hpk hkr S1 S2
      _ ≤ (D ^ (2 * power) * s) * (D ^ (2 * power) * s) := Nat.mul_le_mul hd1 hd2
      _ = (D ^ (2 * power) * s) ^ 2 := by ring
  have hGTmap := (Submodule.isCloseTo_map_iff C).mpr hGT
  have hTGmap := (Submodule.isCloseTo_map_iff C).mpr hTG
  have hWT : Submodule.IsViable (1 / 4 : ℝ) W (T.map C.toLinearEquiv.toLinearMap) := by
    apply (Submodule.IsCloseTo.trans hmerged hGTmap (by norm_num)).of_le
    linarith only [hepsilon1]
  obtain ⟨hc, herror⟩ := merge_power_error_le hD hpower hspower hQ0 hQbound hDelta htrade
  set c := (1 - (1 / 4 : ℝ)) * ((min s Q : ℕ) : ℝ) / (8 * Q) with hcdef
  have hcle : c ≤ 3 / 32 := by
    have hmin : ((min s Q : ℕ) : ℝ) ≤ Q := by exact_mod_cast min_le_right s Q
    rw [hcdef, div_le_iff₀ (by positivity)]
    nlinarith only [hmin, hQR]
  -- Viability of the sample implies viability of its word image for the original target.
  have hgood : ∀ U, Submodule.IsViable (1 - c) (canonicalIntervalRangeSample L q p r s W U)
      (T.map C.toLinearEquiv.toLinearMap) →
      Submodule.IsViable (2 * ((1024 / 9 : ℝ) * (1 / 100000) + epsilon))
        (⨆ w : Fin power → Fin N, (canonicalIntervalRangeSample L q p r s W U).map
          (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (G.map C.toLinearEquiv.toLinearMap) := by
    intro U hU
    have hfiltered := himprove power _ (1 - c) hU (by linarith only [hc])
    rw [sub_sub_cancel] at hfiltered
    have hback := Submodule.IsCloseTo.trans hfiltered hTGmap (by positivity)
    exact hback.of_le (by linarith only [herror])
  have hsub : {U | ¬Submodule.IsViable (2 * ((1024 / 9 : ℝ) * (1 / 100000) + epsilon))
        (⨆ w : Fin power → Fin N, (canonicalIntervalRangeSample L q p r s W U).map
          (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (G.map C.toLinearEquiv.toLinearMap)} ⊆
      {U | ¬Submodule.IsViable (1 - c) (canonicalIntervalRangeSample L q p r s W U)
        (T.map C.toLinearEquiv.toLinearMap)} :=
    fun U hbad hsample ↦ hbad (hgood U hsample)
  refine (measure_mono hsub).trans ?_
  by_cases hQs : Q ≤ s
  · have hempty : {U | ¬Submodule.IsViable (1 - c) (canonicalIntervalRangeSample L q p r s W U)
        (T.map C.toLinearEquiv.toLinearMap)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro U hU
      apply hU
      rw [canonicalIntervalRangeSample_eq_self_of_finrank_le W hQs U]
      exact hWT.of_le (by linarith only [hcle])
    rw [hempty, measure_empty]
    exact zero_le
  · have hmin : min s Q = s := min_eq_left (le_of_lt (not_le.mp hQs))
    have hfailure := rankUnitaryHaar_not_isViable_canonicalIntervalRangeSample_le
      L q p r s W hWT
    refine hfailure.trans (le_of_eq ?_)
    have hmin' : min s (Module.finrank ℂ W) = s := hmin
    simp only [eta, hQs, ↓reduceIte, hmin']
    rfl

end DGCanonicalNodeEvent

section DGCanonicalNodeParent

/-!
## One canonical physical parent of the degenerate-gap tree with `k` rounds

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

end DGCanonicalNodeParent

end TNLean.MPS.AreaLaw.ALVV
