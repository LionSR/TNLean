/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AdjacentIntervalMerge
import TNLean.MPS.AreaLaw.IntervalGenerators
import QICLean.Probability.Sampling.SampledWordImageBounds

/-!
# Actual sampled word images on a parent interval

The original global target is retained through the actual adjacent merge,
the transfer to one fixed improving target, the actual Haar sample and the
literal operator-word image. A measurable event certifies every output in
that event for each fixed pair of input spaces.

The finite family and its powered improvement are explicit inputs here;
the physical construction supplies them before the input spaces. This is
an auxiliary composition for ALVV, arXiv:1602.08828v2, `l:t`, lines 500–523,
`l:rs`, lines 530–558, and `l:er`, lines 597–622. No recursively selected
family or measurability as the input spaces vary is asserted.

**Local fix (complex sphere net count):** The failure bound uses the
corrected exponent and net scale documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_random_sampling_net_count.pdf.
-/

open ManyBody (interval)

open scoped TensorProduct
open MeasureTheory

namespace TNLean.MPS.AreaLaw

/-- The actual sampled word-image followed by one collective interval trim.
Supporting ALVV, arXiv:1602.08828v2, `l:er`, lines 597–622, and
`lem:trimming`, lines 660–697. This definition does not identify one final
trim with the source's interleaved-trim operation. -/
noncomputable def sampledIntervalTrim (L q p r : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (power s : ℕ) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let V := Submodule.sampledWordImage F power s W U
  let basis := stdOrthonormalBasis ℂ V
  intervalTrimSubspace L q p r xi (fun i ↦ (basis i : _))

/-- The actual output retains a bounded recorded family, for every unitary.
Supporting ALVV, arXiv:1602.08828v2, error reduction, lines 597–622,
and collective trimming, lines 660–697. The bound concerns the recorded
vectors rather than every linear combination in their span. -/
theorem isIntervalSpanWithRankBound_sampledIntervalTrim {L q p r N D s : ℕ}
    (hD : 2 ≤ D) (hs : 1 ≤ s) {xi : ℝ} (hxi : 0 < xi)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (hN : N ≤ D ^ 2)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ) :
    IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi
      (sampledIntervalTrim L q p r F (Nat.clog D (D ^ 2 * s)) s xi W U) := by
  apply isIntervalSpanWithRankBound_intervalTrimSubspace hxi
  exact Submodule.finrank_sampledWordImage_le_cubic hD hs F
    (by simpa only [Fintype.card_fin] using hN) W U

/-- A measurable fixed-input Haar event certifies the actual word image when
the words improve one target `Thi` into a possibly different target `Tlo`.
The sample is taken for viability for `Thi`; its word image is viable for
`Tlo`. This is the nested form of the merge analysis of ALVV,
arXiv:1602.08828v2, `l:rs`, lines 530–558, and `l:er`, lines 597–622, used
for the two low-energy windows of Theorem `t:alg2`, lines 1869–1878.
No adaptive measurability or physical existence of the family is asserted. -/
lemma _root_.Submodule.exists_measurable_sampledWordImage_event_of_nested
    {M E iota : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [FiniteDimensional ℂ M] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype iota]
    (F : iota → M →L[ℂ] M) (Thi Tlo : Submodule ℂ (M ⊗[ℂ] E)) (Delta : ℝ)
    (himprove : ∀ (a : ℕ) (S : Submodule ℂ M) (delta : ℝ),
      Submodule.IsViable delta S Thi → delta < 1 →
      Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2)
        (⨆ w : Fin a → iota, S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap) Tlo)
    (power s : ℕ) (hs : 1 ≤ s) (W : Submodule ℂ M) (hW : W ≠ ⊥)
    {delta : ℝ} (hviable : Submodule.IsViable delta W Thi) (hdelta : delta < 1) :
    let q := Module.finrank ℂ W
    let c := (1 - delta) * (min s q : ℕ) / (8 * q)
    let eta : ℝ := if q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - delta) * (s : ℝ) / (8 * q))) ^
        (2 * Module.finrank ℂ Thi) * q * Real.exp (-(s / 16 : ℝ))
    ∃ Good : Set (Matrix.unitaryGroup (Fin q) ℂ),
      MeasurableSet Good ∧ Matrix.unitaryHaar (Fin q) Goodᶜ ≤ ENNReal.ofReal eta ∧
      1 - ENNReal.ofReal eta ≤ Matrix.unitaryHaar (Fin q) Good ∧
      ∀ U ∈ Good,
        Module.finrank ℂ (Submodule.sampledWordImage F power s W U) ≤
          Fintype.card iota ^ power * min s q ∧
        Submodule.IsViable (Delta ^ power / c ^ 2)
          (Submodule.sampledWordImage F power s W U) Tlo := by
  intro q c eta
  have hq : 1 ≤ q := Submodule.one_le_finrank_iff.mpr hW
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hnR : (0 : ℝ) < (min s q : ℕ) := by exact_mod_cast (by omega : 0 < min s q)
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨Good, hGood, hbad, hprob, hsample⟩ :=
    Submodule.exists_measurable_randomSubspace_min_event (stdOrthonormalBasis ℂ W) s
      hviable hdelta.le
  refine ⟨Good, hGood, hbad, hprob, ?_⟩
  intro U hU
  refine ⟨Submodule.finrank_sampledWordImage_le F power s W U, ?_⟩
  have hfiltered := himprove power _ (1 - c) (hsample U hU) (by linarith)
  simpa only [Submodule.sampledWordImage, sub_sub_cancel] using hfiltered

/-- The actual sampled word image has a measurable fixed-input success
event, a cubic dimension bound and controlled error, when the children are
viable for a global target `G`, `G` is `epsilon`-close to `Thi`, the word family
improves viability for `Thi` into viability for `Tlo`, and `Tlo` is
`epsilon`-close to the output target `Gout`.
The fixed improving family precedes both child spaces and
the sample. Supporting ALVV, arXiv:1602.08828v2, `l:t`, lines 500–523,
`l:rs`, lines 530–558, and `l:er`, lines 597–622. This composition does not
assert the physical existence of the family or an adaptive probability law. -/
theorem exists_measurable_interval_word_image_event_of_nested
    {L q p k r D N s : ℕ} (hpk : p ≤ k) (hkr : k ≤ r) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (G Gout Thi Tlo : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (hG : G ≠ ⊥)
    {epsilon Delta : ℝ} (_hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1 / 10000)
    (hGT : Submodule.IsCloseTo epsilon G Thi) (hTG : Submodule.IsCloseTo epsilon Tlo Gout)
    (hDelta : 0 ≤ Delta) (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (hN : N ≤ D ^ 2)
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
    ∃ Good : Set (Matrix.unitaryGroup (Fin Q) ℂ),
      MeasurableSet Good ∧ Matrix.unitaryHaar (Fin Q) Goodᶜ ≤ ENNReal.ofReal eta ∧
      1 - ENNReal.ofReal eta ≤ Matrix.unitaryHaar (Fin Q) Good ∧
      ∀ U ∈ Good,
        Module.finrank ℂ (Submodule.sampledWordImage F power s W U) ≤ D ^ 6 * s ^ 3 ∧
        Submodule.IsViable
          (2 * ((1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 + epsilon))
          (Submodule.sampledWordImage F power s W U)
          (Gout.map C.toLinearEquiv.toLinearMap) := by
  intro C W Q power eta
  have hmerged := isViable_adjacentIntervalMerge hpk hkr G S1 S2 h1 h2
  have hGmap : G.map C.toLinearEquiv.toLinearMap ≠ ⊥ :=
    (Submodule.map_ne_bot_iff (e := C.toLinearEquiv)).mpr hG
  have hW : W ≠ ⊥ :=
    Submodule.isViable_ne_bot_of_target_ne_bot hmerged (by norm_num) hGmap
  have hQ0 : 0 < Q := by
    exact Nat.zero_lt_of_lt (Submodule.one_le_finrank_iff.mpr hW)
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
  let c := (1 - (1 / 4 : ℝ)) * (min s Q : ℕ) / (8 * Q)
  have hc : 0 < c := hratio.1
  have herror : Delta ^ power / c ^ 2 ≤ (1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 :=
    hratio.2
  obtain ⟨Good, hGood, hbad, hprob, houtput⟩ :=
    Submodule.exists_measurable_sampledWordImage_event_of_nested F
      (Thi.map C.toLinearEquiv.toLinearMap) (Tlo.map C.toLinearEquiv.toLinearMap) Delta
      himprove power s hs W hW hWT (by norm_num)
  refine ⟨Good, hGood, hbad, hprob, ?_⟩
  intro U hU
  obtain ⟨_hdimension, hfiltered⟩ := houtput U hU
  constructor
  · exact Submodule.finrank_sampledWordImage_le_cubic hD hs F
      (by simpa only [Fintype.card_fin] using hN) W U
  · change Submodule.IsViable (Delta ^ power / c ^ 2)
      (Submodule.sampledWordImage F power s W U) (Tlo.map C.toLinearEquiv.toLinearMap) at hfiltered
    have hback := Submodule.IsCloseTo.trans hfiltered hTGmap (by positivity)
    exact hback.of_le (by linarith only [herror])

/-- The actual sampled word image has a measurable fixed-input success
event, a cubic dimension bound and controlled error for the same original
global target. The fixed improving family precedes both child spaces and
the sample. Supporting ALVV, arXiv:1602.08828v2, `l:t`, lines 500–523,
`l:rs`, lines 530–558, and `l:er`, lines 597–622. This composition does not
assert the physical existence of the family or an adaptive probability law. -/
theorem exists_measurable_interval_word_image_event
    {L q p k r D N s : ℕ} (hpk : p ≤ k) (hkr : k ≤ r) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (G T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (hG : G ≠ ⊥)
    {epsilon Delta : ℝ} (_hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1 / 10000)
    (hGT : Submodule.IsCloseTo epsilon G T) (hTG : Submodule.IsCloseTo epsilon T G)
    (hDelta : 0 ≤ Delta) (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (hN : N ≤ D ^ 2)
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
    (hd1 : Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3)
    (hd2 : Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3) :
    let C := Entropy.regionTensorCoordinates q (interval L p r)
    let W := adjacentIntervalMerge L q p k r hpk hkr S1 S2
    let Q := Module.finrank ℂ W
    let power := Nat.clog D (D ^ 2 * s)
    let eta : ℝ := if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^
        (2 * Module.finrank ℂ (T.map C.toLinearEquiv.toLinearMap)) * Q *
          Real.exp (-(s / 16 : ℝ))
    ∃ Good : Set (Matrix.unitaryGroup (Fin Q) ℂ),
      MeasurableSet Good ∧ Matrix.unitaryHaar (Fin Q) Goodᶜ ≤ ENNReal.ofReal eta ∧
      1 - ENNReal.ofReal eta ≤ Matrix.unitaryHaar (Fin Q) Good ∧
      ∀ U ∈ Good,
        Module.finrank ℂ (Submodule.sampledWordImage F power s W U) ≤ D ^ 6 * s ^ 3 ∧
        Submodule.IsViable
          (2 * ((1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 + epsilon))
          (Submodule.sampledWordImage F power s W U)
          (G.map C.toLinearEquiv.toLinearMap) := by
  exact exists_measurable_interval_word_image_event_of_nested hpk hkr hD hs G G T T hG
    _hepsilon hepsilon1 hGT hTG hDelta htrade F hN himprove S1 S2 h1 h2 hd1 hd2

end TNLean.MPS.AreaLaw
