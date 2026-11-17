/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.MergeRounds
import TNLean.MPS.AreaLaw.PhysicalDGSampledNode

/-!
# One sampled parent of the degenerate-gap tree with `k` rounds

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, merges two viable spaces of
dimension at most `D^{2k} s`, samples `s` vectors of the merged space, and applies `k` rounds of
the improving family of Theorems 4.2 and 4.3, a family of at most `D²` operators. This file
proves, for one long parent and every number of rounds `k ≥ 1` with `s ≤ D^{2k}`, that the
literal sampled word image followed by one collective trim is `3/200`-viable for the original
ground space on a measurable Haar event with the failure probability of Lemma `l:rs`. The
earlier node event takes the larger power `⌈log_D (D² s)⌉` and the children of dimension
`D⁶ s³`.

**Scope restriction (one long parent, one final trim and capped gap):** one parent of length
greater than `4 ℓ`, with the trim applied once after the `k` rounds rather than after each round,
explicit scalar tail and filter conditions, and `min γ 1` in place of `γ`; the event is for fixed
children. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

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

end TNLean.MPS.AreaLaw.ALVV
