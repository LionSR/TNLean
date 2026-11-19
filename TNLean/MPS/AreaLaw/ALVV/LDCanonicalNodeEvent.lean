/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.CanonicalWordTrim
import TNLean.MPS.AreaLaw.IntervalSampledImage

/-!
# The canonical sample of one low-density parent

ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, runs the merge of Theorem `t:alg1`,
lines 1777–1817, with families that carry an upper window to a lower one. This file bounds, for
fixed children of dimension at most `D⁶ s³` viable for the upper window, the Haar measure of the
set of rank-independent coordinates on which the image of the canonical range sample under all
words of length `⌈log_D (D² s)⌉` fails to be viable for the lower window. The bound is the
failure probability of Lemma `l:rs`. The companion event for a sample drawn from the unitary
group of the merged dimension is `exists_measurable_interval_word_image_event_of_nested`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw

/-- For fixed children of dimension at most `D⁶ s³`, viable for an upper target `G` that is close
to the input target `Thi` of a family improving viability from `Thi` to `Tlo`, with `Tlo` close
to a lower target `Gout`, the image of the canonical range sample of the merged space under all
words of length `⌈log_D (D² s)⌉` fails to be viable for `Gout` with error
`2 ((1024/9) · 10⁻⁵ / s² + ε)` on a set of rank-independent coordinates of measure at most the
failure probability of Lemma `l:rs`. Auxiliary to ALVV, arXiv:1602.08828v2, Lemmas `l:rs` and
`l:er`, lines 530–558 and 597–622, and Theorem `t:alg2`, lines 1869–1878. -/
theorem rankUnitaryHaar_canonical_interval_word_image_failure_le_of_nested
    {L q p k r D N s : ℕ} (hpk : p ≤ k) (hkr : k ≤ r) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (G Gout Thi Tlo : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (hG : G ≠ ⊥)
    {epsilon Delta : ℝ} (hepsilon1 : epsilon ≤ 1 / 10000)
    (hGT : Submodule.IsCloseTo epsilon G Thi) (hTG : Submodule.IsCloseTo epsilon Tlo Gout)
    (hDelta : 0 ≤ Delta) (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (himprove : ∀ (a : ℕ)
      (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (delta : ℝ),
      Submodule.IsViable delta S
        (Thi.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) →
      delta < 1 →
      Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2)
        (⨆ w : Fin a → Fin N, S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (Tlo.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (h1 : Submodule.IsViable (3 / 200 : ℝ) S1
      (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap))
    (h2 : Submodule.IsViable (3 / 200 : ℝ) S2
      (G.map (Entropy.regionTensorCoordinates q (interval L k r)).toLinearEquiv.toLinearMap))
    (hd1 : Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3)
    (hd2 : Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3) :
    let C := Entropy.regionTensorCoordinates q (interval L p r)
    let W := adjacentIntervalMerge L q p k r hpk hkr S1 S2
    let Q := Module.finrank ℂ W
    let power := Nat.clog D (D ^ 2 * s)
    let eta : ℝ := if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^
        (2 * Module.finrank ℂ (Thi.map C.toLinearEquiv.toLinearMap)) * Q *
          Real.exp (-(s / 16 : ℝ))
    Matrix.rankUnitaryHaar (Fintype.card (interval L p r → Fin q))
      {U | ¬Submodule.IsViable (2 * ((1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 + epsilon))
        (⨆ w : Fin power → Fin N, (canonicalIntervalRangeSample L q p r s W U).map
          (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (Gout.map C.toLinearEquiv.toLinearMap)} ≤ ENNReal.ofReal eta := by
  intro C W Q power eta
  have hmerged := isViable_adjacentIntervalMerge hpk hkr G S1 S2 h1 h2
  have hGmap : G.map C.toLinearEquiv.toLinearMap ≠ ⊥ :=
    (Submodule.map_ne_bot_iff (e := C.toLinearEquiv)).mpr hG
  have hW : W ≠ ⊥ :=
    Submodule.isViable_ne_bot_of_target_ne_bot hmerged (by norm_num) hGmap
  have hQ0 : 0 < Q := Nat.zero_lt_of_lt (Submodule.one_le_finrank_iff.mpr hW)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQbound : Q ≤ D ^ 12 * s ^ 6 := by
    calc
      Q ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
        finrank_adjacentIntervalMerge_le hpk hkr S1 S2
      _ ≤ (D ^ 6 * s ^ 3) * (D ^ 6 * s ^ 3) := Nat.mul_le_mul hd1 hd2
      _ = D ^ 12 * s ^ 6 := by ring
  have hGTmap := (Submodule.isCloseTo_map_iff C).mpr hGT
  have hTGmap := (Submodule.isCloseTo_map_iff C).mpr hTG
  have hWT : Submodule.IsViable (1 / 4 : ℝ) W (Thi.map C.toLinearEquiv.toLinearMap) := by
    apply (Submodule.IsCloseTo.trans hmerged hGTmap (by norm_num)).of_le
    linarith only [hepsilon1]
  have hratio := Real.viable_node_power_error_bound hD hs hQ0 hQbound
    (delta := (1 / 4 : ℝ)) le_rfl hDelta (by norm_num : (0 : ℝ) < 1 / 100000)
      (by norm_num : (1 / 100000 : ℝ) < 1) htrade
  set c := (1 - (1 / 4 : ℝ)) * ((min s Q : ℕ) : ℝ) / (8 * Q) with hcdef
  have hc : 0 < c := hratio.1
  have herror : Delta ^ power / c ^ 2 ≤ (1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 :=
    hratio.2
  have hcle : c ≤ 3 / 32 := by
    have hmin : ((min s Q : ℕ) : ℝ) ≤ Q := by exact_mod_cast min_le_right s Q
    rw [hcdef, div_le_iff₀ (by positivity)]
    nlinarith only [hmin, hQR]
  have hsub : {U | ¬Submodule.IsViable
        (2 * ((1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 + epsilon))
        (⨆ w : Fin power → Fin N, (canonicalIntervalRangeSample L q p r s W U).map
          (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)
        (Gout.map C.toLinearEquiv.toLinearMap)} ⊆
      {U | ¬Submodule.IsViable (1 - c) (canonicalIntervalRangeSample L q p r s W U)
        (Thi.map C.toLinearEquiv.toLinearMap)} := by
    intro U hbad hsample
    apply hbad
    have hfiltered := himprove power _ (1 - c) hsample (by linarith only [hc])
    rw [sub_sub_cancel] at hfiltered
    have hback := Submodule.IsCloseTo.trans hfiltered hTGmap (by positivity)
    exact hback.of_le (by linarith only [herror])
  refine (measure_mono hsub).trans ?_
  by_cases hQs : Q ≤ s
  · have hempty : {U | ¬Submodule.IsViable (1 - c) (canonicalIntervalRangeSample L q p r s W U)
        (Thi.map C.toLinearEquiv.toLinearMap)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro U hU
      apply hU
      rw [canonicalIntervalRangeSample_eq_self_of_finrank_le W hQs U]
      exact hWT.of_le (by linarith only [hcle])
    rw [hempty, measure_empty]
    exact zero_le
  · have hmin : min s (Module.finrank ℂ W) = s := min_eq_left (le_of_lt (not_le.mp hQs))
    have hfailure := rankUnitaryHaar_not_isViable_canonicalIntervalRangeSample_le
      L q p r s W hWT
    refine hfailure.trans (le_of_eq ?_)
    simp only [eta, hQs, ↓reduceIte, hmin]
    rfl

end TNLean.MPS.AreaLaw.ALVV
