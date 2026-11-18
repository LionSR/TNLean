/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.CanonicalWordTrim
import TNLean.MPS.AreaLaw.ALVV.DGConstantNodeEvent

/-!
# The canonical sample of one degenerate-gap parent with `k` rounds

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, merges two viable spaces of
dimension at most `D^{2k} s`, samples `s` vectors of the merged space and applies `k` rounds of
the improving family of Corollary 4.6 and the proof of Theorem 4.9. This file bounds, for fixed
children, the Haar measure of the set of rank-independent coordinates on which the image of the
canonical range sample under all words of length `k` fails to be viable for the original ground
space. The bound is the failure probability of Lemma `l:rs`. The companion event for a sample
drawn from the unitary group of the merged dimension is in `DGConstantNodeEvent`.

**Scope restriction (one long parent, one final trim and capped gap):** one parent of length
greater than `4 ℓ`, with the trim applied once after the `k` rounds rather than after each round,
explicit scalar tail and filter conditions, and `min γ 1` in place of `γ`; the bound is for fixed
children. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

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

end TNLean.MPS.AreaLaw.ALVV
