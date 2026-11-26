/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalIntervalResampling
import QICLean.ManyBody.Subspace.Sampling.StoppedHalfSamplingProbability
import QICLean.ManyBody.Subspace.Sampling.CanonicalHalfSamplingParentProperties
import QICLean.ManyBody.Entropy.Cut.RegionalViability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.BalancedIntervalFailure

/-!
# The literal original-target history of an interval parent

The event is the existing native stopped-run event for the actual candidate
projection, fixed interval cuts and prescribed finite sequence. Its target
is the original whole-chain space in interval and full-exterior coordinates.
The event is jointly measurable when the actual candidate projection is
measurable; no sampling-success condition is assumed. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817.

It also contains the following results.

* `TNLean.MPS.AreaLaw.isViable_of_mem_canonicalHalfSampledIntervalHistory`: initial viability
  recorded by the actual interval history.
* `TNLean.MPS.AreaLaw.canonicalHalfSampledIntervalHistory_probability`: fixed-input probability for
  an actual interval history and terminal image.
* `TNLean.MPS.AreaLaw.intervalResamplingMeasure_canonical_tree_joint_history_failure_le`: joint
  original-target histories of the actual repeated-sampling tree.
-/

open ManyBody (interval)

section CanonicalIntervalRawHistory

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The existing literal Raw history event for this actual interval
candidate and fixed original global target. It records all stopped ranges
and active next ranges, rather than only the final retained space.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
noncomputable def canonicalHalfSampledIntervalHistory (L q p r D threshold rounds : ℕ)
    {N : ℕ} (F : Fin N →
      EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) :
    Set (Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) :=
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  let Graw := G.map
    (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap
  Entropy.canonicalHalfSamplingRawGood (R := rounds) (n := fun _ : interval L p r ↦ q)
    e (intervalTrimCut L p r) xi (r - p - 1) D threshold
    (Entropy.nativeFamilyMatrix e F) P Graw

/-- The actual original-target history is jointly measurable in a varying
candidate and its full finite sequence. No initial viability or measurable
basis selection is assumed. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem measurableSet_canonicalHalfSampledIntervalHistory
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ}
    (D threshold rounds : ℕ)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection))
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) :
    MeasurableSet {z : X × (Fin rounds → Matrix.rankUnitaryProduct
        (Fintype.card (interval L p r → Fin q))) |
      z.2 ∈ canonicalHalfSampledIntervalHistory L q p r D threshold rounds F xi (W z.1) G} := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := fun x ↦ ((Matrix.toEuclideanCLM
    (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection).reindex e.symm e.symm
  let Graw := G.map
    (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap
  let input := fun z : X × (Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) ↦ (P z.1, z.2)
  have hP : Measurable P :=
    ((continuous_id : Continuous (fun M : Matrix (interval L p r → Fin q)
      (interval L p r → Fin q) ℂ ↦ M)).matrix_reindex e.symm e.symm).measurable.comp hW
  have hInput : Measurable input := (hP.comp measurable_fst).prodMk measurable_snd
  exact (Entropy.measurableSet_canonicalHalfSamplingRawGood (R := rounds)
    (n := fun _ : interval L p r ↦ q) e (intervalTrimCut L p r) xi
    (r - p - 1) D threshold (Entropy.nativeFamilyMatrix e F) Graw).preimage (f := input) hInput

/-- The literal history event at an actual balanced long parent, using its
same two child spaces and its own finite sequence. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
noncomputable def canonicalIntervalResamplingHistory {L q width : ℕ}
    (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (J : LongIntervalIndex L width) : Set (IntervalResamplingChoices L q rounds) :=
  let l := J.val.1
  let r := J.val.2
  let k := l + (r - l) / 2
  let hpk : l ≤ k := by dsimp only [l, r, k]; omega
  let hkr : k ≤ r := by dsimp only [l, r, k]; omega
  let S := fun p r U ↦ balancedIntervalSpace
    (canonicalIntervalResamplingOperation D rounds threshold N F xi U) width hwidth p r
  {U | U (LongIntervalIndex.coordinate J) ∈
    canonicalHalfSampledIntervalHistory L q l r D (threshold J) rounds (F J) xi
      (adjacentIntervalMerge L q l k r hpk hkr (S l k U) (S k r U)) G}

/-- The actual original-target history of a long parent is measurable
in the full collection of interval sequences. Candidate projections and
its own-coordinate evaluation are derived from the same actual tree.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem measurableSet_canonicalIntervalResamplingHistory {L q width : ℕ}
    (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (J : LongIntervalIndex L width) :
    MeasurableSet (canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J) := by
  let l := J.val.1
  let r := J.val.2
  let k := l + (r - l) / 2
  have hpk : l ≤ k := by dsimp only [l, r, k]; omega
  have hkr : k ≤ r := by dsimp only [l, r, k]; omega
  let S := fun p r U ↦ balancedIntervalSpace
    (canonicalIntervalResamplingOperation D rounds threshold N F xi U) width hwidth p r
  let W := fun U ↦ adjacentIntervalMerge L q l k r hpk hkr (S l k U) (S k r U)
  have hleft := (measurable_projectionMatrix_and_dependsOn_canonicalIntervalResamplingTree
    D rounds hwidth threshold N F xi l k hpk (hkr.trans J.property.2.1)).1
  have hright := (measurable_projectionMatrix_and_dependsOn_canonicalIntervalResamplingTree
    D rounds hwidth threshold N F xi k r hkr J.property.2.1).1
  have hW := measurable_projectionMatrix_adjacentIntervalMerge hpk hkr
    (S l k) (S k r) hleft hright
  let input := fun U : IntervalResamplingChoices L q rounds ↦
    (U, U (LongIntervalIndex.coordinate J))
  have hInput : Measurable input :=
    measurable_id.prodMk (measurable_pi_apply (LongIntervalIndex.coordinate J))
  exact (measurableSet_canonicalHalfSampledIntervalHistory D (threshold J) rounds
    (F J) xi W hW G).preimage (f := input) hInput

private theorem resampling_tree_update_of_length_lt {L q width : ℕ}
    (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (U : IntervalResamplingChoices L q rounds) (I : Fin (L + 1) × Fin (L + 1))
    (v : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L I.1.val I.2.val → Fin q)))
    (hlong : r - p < I.2.val - I.1.val) :
    balancedIntervalSpace (canonicalIntervalResamplingOperation
      D rounds threshold N F xi (Function.update U I v)) width hwidth p r =
    balancedIntervalSpace (canonicalIntervalResamplingOperation
      D rounds threshold N F xi U) width hwidth p r := by
  unfold canonicalIntervalResamplingOperation
  exact independentIntervalTree_update_of_length_lt
    (Ω := fun J ↦ Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W u ↦ canonicalHalfSampledIntervalParent L q J.val.1 J.val.2
      D (threshold J) rounds (F J) xi W u)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalHalfSampledIntervalParent
      D (threshold J) rounds (F J) xi W hW) hwidth p r hpr hrL U I v hlong

/-- Varying a parent's own sequence tests its literal history with the
same two baseline child spaces. No comparison candidate is substituted.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem canonicalIntervalResamplingHistory_update_parent {L q width : ℕ}
    (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (J : LongIntervalIndex L width) (U : IntervalResamplingChoices L q rounds)
    (v : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.val.1 J.val.2 → Fin q))) :
    let l := J.val.1
    let r := J.val.2
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [l, r, k]; omega
    let hkr : k ≤ r := by dsimp only [l, r, k]; omega
    let S := fun p r U ↦ balancedIntervalSpace
      (canonicalIntervalResamplingOperation D rounds threshold N F xi U) width hwidth p r
    Function.update U (LongIntervalIndex.coordinate J) v ∈
      canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J ↔
    v ∈ canonicalHalfSampledIntervalHistory L q l r D (threshold J) rounds (F J) xi
      (adjacentIntervalMerge L q l k r hpk hkr (S l k U) (S k r U)) G := by
  classical
  intro l r k hpk hkr S
  have hleft := resampling_tree_update_of_length_lt D rounds hwidth threshold N F xi
    l k hpk (hkr.trans J.property.2.1) U (LongIntervalIndex.coordinate J) v
    (by dsimp only [l, r, k, LongIntervalIndex.coordinate]; omega)
  have hright := resampling_tree_update_of_length_lt D rounds hwidth threshold N F xi
    k r hkr J.property.2.1 U (LongIntervalIndex.coordinate J) v
    (by dsimp only [l, r, k, LongIntervalIndex.coordinate]; omega)
  change Function.update U (LongIntervalIndex.coordinate J) v
      (LongIntervalIndex.coordinate J) ∈
    canonicalHalfSampledIntervalHistory L q l r D (threshold J) rounds (F J) xi
      (adjacentIntervalMerge L q l k r hpk hkr
        (S l k (Function.update U (LongIntervalIndex.coordinate J) v))
        (S k r (Function.update U (LongIntervalIndex.coordinate J) v))) G ↔ _
  have hleft' : S l k (Function.update U (LongIntervalIndex.coordinate J) v) = S l k U := hleft
  have hright' : S k r (Function.update U (LongIntervalIndex.coordinate J) v) = S k r U := hright
  dsimp only [LongIntervalIndex.coordinate] at *
  rw [Function.update_self, hleft', hright']
  rfl

end TNLean.MPS.AreaLaw

end CanonicalIntervalRawHistory

section CanonicalIntervalRawHistoryProperties

/-!
## Initial viability recorded by the actual interval history

The original-target history tests the initial state as well as every later
state. Its initial projection is the candidate's actual orthogonal
projection, so membership in this history gives initial viability directly.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The literal original-target history records viability of the actual
initial candidate. This follows from its zeroth-state test and the exact
transported range of the candidate projection. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem isViable_of_mem_canonicalHalfSampledIntervalHistory
    (L q p r D threshold rounds : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (U : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q)))
    (hU : U ∈ canonicalHalfSampledIntervalHistory L q p r D threshold rounds F xi W G) :
    Submodule.IsViable 0.04 W
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  let Graw := G.map
    (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap
  have h0 : Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap)
          ({v // v ∉ interval L p r} → Fin q)) Graw :=
    hU.1 ⟨0, Nat.zero_lt_succ rounds⟩
  have hRange : (Matrix.toEuclideanLin P).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W := by
    change (Matrix.toEuclideanLin
      (((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        W.starProjection).submatrix e e)).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W
    rw [Matrix.map_range_toEuclideanLin_submatrix]
    change ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ))
      ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        W.starProjection)).toLinearMap.range = W
    rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection]
  rw [hRange] at h0
  exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p r) W G).mp h0

end TNLean.MPS.AreaLaw

end CanonicalIntervalRawHistoryProperties

section CanonicalIntervalRawProbability

/-!
## Fixed-input probability for an actual interval history and terminal image

The candidate's actual orthogonal projection is put in the prescribed finite
coordinates. The fixed-K resampling theorem then bounds its literal original-target
history under the actual finite product Haar law. On that one event, the same
complete interval parent is viable for the original global target, and its same
last untrimmed image has the quantitative bound for every improving target.

This is a conditional analytic auxiliary to ALVV, arXiv:1602.08828v2,
lines 749–755 and 1801–1813. The family, targets, reference and numerical
certificates are explicit inputs. No successful sample or energy trial is assumed.

**Local fix (repeated sampling and terminal amplification):** This is the
corrected stopped-resampling parent with terminal image and trim; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
It is not a running-time or complete physical construction theorem.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

namespace TNLean.MPS.AreaLaw

/-- The actual candidate and finite sequence have the literal original-target
history bound. The same history gives the same parent's viability and the
same untrimmed image's bound for all centers. Family and reference conditions
are explicit analytic certificates, not a supplied sampling-success event.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1801–1813. -/
theorem canonicalHalfSampledIntervalHistory_probability
    {X : Type*} (D a K : ℕ) (hD : 2 ≤ D) (eta : ℝ) (hK : 1 ≤ K)
    (hThreshold : ∀ rho len Q : ℕ, K * (rho + 1) * (len + 2) ^ 2 ≤ Q →
      4 * D ^ 2 ≤ Q ∧ Submodule.bootstrapFailure D Q rho ≤ eta / ((len : ℝ) + 2) ^ a)
    (L q p endR nFamily rho rounds bRef : ℕ)
    (Delta epsilon epsilonRef xi : ℝ)
    (G R : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (F : Fin nFamily → EuclideanSpace ℂ (interval L p endR → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p endR → Fin q))
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)))
    (hN : nFamily ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo epsilon G (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) G)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)),
      Submodule.IsViable delta S
        ((T x).map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (Delta / (1 - delta) ^ 2)
        (⨆ i, S.map (F i).toLinearMap)
        ((T x).map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap))
    (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (hepsilon : epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100)
    (hxi : 0 < xi) (hepsilonRef0 : 0 ≤ epsilonRef) (hepsilonRef : epsilonRef ≤ 1 / 100000)
    (hRawRef : Submodule.IsCloseTo epsilonRef G R)
    (hRefRaw : Submodule.IsCloseTo epsilonRef R G)
    (hRank : ∀ t ∈ R.map
        (Entropy.regionConfigurationSplit q (interval L p endR)).toLinearEquiv.toLinearMap,
      ∀ j < endR - p - 1,
      Matrix.schmidtRank (WithLp.ofLp
        (Entropy.cutEnvVector (n := fun _ : interval L p endR ↦ q)
          (intervalTrimCut L p endR j) t)) ≤ bRef)
    (hbudget : xi * Real.sqrt (((endR - p - 1 : ℕ) : ℝ) * (bRef : ℝ)) ≤ 1 / 1000)
    (hdim : Module.finrank ℂ G ≤ rho)
    (hrounds : Fintype.card (interval L p endR → Fin q) ≤ 2 ^ rounds)
    (hInitial : Submodule.IsViable 0.04 W
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)) :
    let d := Fintype.card (interval L p endR → Fin q)
    let e := (Fintype.equivFin (interval L p endR → Fin q)).symm
    let P := ((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ)).symm
      W.starProjection).reindex e.symm e.symm
    let threshold := K * (rho + 1) * (L + 2) ^ 2
    let good := canonicalHalfSampledIntervalHistory L q p endR D threshold rounds F xi W G
    let state := fun (U : Fin rounds → Matrix.rankUnitaryProduct d) j ↦
      Entropy.canonicalHalfSampleTrimIterate e (intervalTrimCut L p endR) xi
        (endR - p - 1) D threshold (Entropy.nativeFamilyMatrix e F) P
        (Entropy.halfSamplingSeedSequence U) j
    let image := fun U ↦ (Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ Entropy.nativeFamilyMatrix e F i * state U rounds))).range
    let parent := fun U ↦ canonicalHalfSampledIntervalParent
      L q p endR D threshold rounds F xi W U
    let law := Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d)
    MeasurableSet good ∧
    law goodᶜ ≤ (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a) ∧
    MeasurableSet {U | Submodule.IsViable (3 / 200) (parent U)
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)} ∧
    law {U | ¬Submodule.IsViable (3 / 200) (parent U)
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)} ≤
        (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a) ∧
    ∀ U ∈ good,
      (∀ x, Submodule.IsViable (Delta / (91 / 100 : ℝ) ^ 2) (image U)
        ((T x).map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)) ∧
      Submodule.IsViable (27 / 2500) (image U)
        (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) ∧
      Submodule.IsViable (3 / 200) (parent U)
        (G.map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) := by
  classical
  intro d e P threshold good state image parent law
  let split := Entropy.regionConfigurationSplit q (interval L p endR)
  let Graw := G.map split.toLinearEquiv.toLinearMap
  let Rraw := R.map split.toLinearEquiv.toLinearMap
  let Traw := fun x ↦ (T x).map split.toLinearEquiv.toLinearMap
  have hRange : (Matrix.toEuclideanLin P).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W := by
    change (Matrix.toEuclideanLin
      (((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ)).symm
        W.starProjection).submatrix e e)).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W
    rw [Matrix.map_range_toEuclideanLin_submatrix]
    change ((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ))
      ((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ)).symm
        W.starProjection)).toLinearMap.range = W
    rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection]
  have hInitialRaw : Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap)
          ({v // v ∉ interval L p endR} → Fin q)) Graw := by
    rw [hRange]
    exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR) W G).mpr hInitial
  have hdimRaw : Module.finrank ℂ Graw ≤ rho := by
    rw [split.toLinearEquiv.finrank_map_eq]
    exact hdim
  have hAraw : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)),
      Submodule.IsCloseTo delta
        (Submodule.prodExt S ({v // v ∉ interval L p endR} → Fin q)) (Traw x) →
      Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
        (Submodule.prodExt (⨆ i, S.map (F i).toLinearMap)
          ({v // v ∉ interval L p endR} → Fin q)) (Traw x) := by
    intro x delta hdelta S hS
    exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR)
      (⨆ i, S.map (F i).toLinearMap) (T x)).mpr
        (hA x delta hdelta S
          ((Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR) S (T x)).mp hS))
  obtain ⟨hGood, hFailure, hParentMeas, hParentFailure, hOnGood, _hRank, _hStop⟩ :=
    Entropy.canonicalHalfSamplingParent_joint_probability_of_threshold
      (n := fun _ : interval L p endR ↦ q)
      (β := {v // v ∉ interval L p endR} → Fin q) (ι := Fin nFamily)
      D a K hD eta hK hThreshold L rho d rounds e (endR - p - 1) bRef
      Delta epsilon epsilonRef xi Graw Rraw x0 Traw F P
      (by simpa only [Fintype.card_fin] using hN)
      (fun x ↦ (Submodule.isCloseTo_map_iff split).mpr (hRawSoft x))
      (fun x ↦ (Submodule.isCloseTo_map_iff split).mpr (hSoftRaw x))
      hAraw hDelta hepsilon (intervalTrimCut L p endR) (intervalTrimCut_mono L p endR)
      hxi hepsilonRef0 hepsilonRef
      ((Submodule.isCloseTo_map_iff split).mpr hRawRef)
      ((Submodule.isCloseTo_map_iff split).mpr hRefRaw)
      hRank hbudget hdimRaw hrounds hInitialRaw
  change MeasurableSet good at hGood
  change law goodᶜ ≤ (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a)
    at hFailure
  change MeasurableSet {U : Fin rounds → Matrix.rankUnitaryProduct d |
    Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt (parent U) ({v // v ∉ interval L p endR} → Fin q)) Graw} at hParentMeas
  change law {U : Fin rounds → Matrix.rankUnitaryProduct d |
    ¬Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt (parent U) ({v // v ∉ interval L p endR} → Fin q)) Graw} ≤
      (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a) at hParentFailure
  have hparentIff (U : Fin rounds → Matrix.rankUnitaryProduct d) :
      Submodule.IsCloseTo (3 / 200)
        (Submodule.prodExt (parent U) ({v // v ∉ interval L p endR} → Fin q)) Graw ↔
      Submodule.IsViable (3 / 200) (parent U)
        (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) :=
    Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR) (parent U) G
  refine ⟨hGood, hFailure, ?_, ?_, ?_⟩
  · simpa only [hparentIff] using hParentMeas
  · simpa only [hparentIff] using hParentFailure
  · intro U hU
    obtain ⟨hTargets, hRawImage, hRawParent⟩ := hOnGood U hU
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR)
        (image U) (T x)).mp (hTargets x)
    · exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR)
        (image U) G).mp hRawImage
    · exact (hparentIff U).mp hRawParent

end TNLean.MPS.AreaLaw

end CanonicalIntervalRawProbability

section CanonicalIntervalRawTreeProbability

/-!
## Joint original-target histories of the actual repeated-sampling tree

The fixed-candidate estimate for the literal stopped history yields one
joint bound for retained viability and every listed parent's same history.
The history is the existing original-target event, not an intersection of
all soft spectral targets. This conditional analytic composition supports
ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. The fixed-candidate
probability and history-to-parent implication remain explicit premises.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

namespace TNLean.MPS.AreaLaw

/-- True fixed-candidate estimates for the literal original-target history
control retained viability and the same history at every listed parent
with one merge count. All Borel and actual-coordinate section properties
are derived. Conditional auxiliary to ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem intervalResamplingMeasure_canonical_tree_joint_history_failure_le
    {L q width : ℕ} (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (beta : ℝ≥0∞)
    (hfixed : ∀ (J : LongIntervalIndex L width)
      (W : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))),
      Submodule.IsViable 0.04 W
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) →
      Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar
          (Fintype.card (interval L J.val.1 J.val.2 → Fin q)))
        (canonicalHalfSampledIntervalHistory L q J.val.1 J.val.2 D
          (threshold J) rounds (F J) xi W G)ᶜ ≤ beta ∧
      ∀ v ∈ canonicalHalfSampledIntervalHistory L q J.val.1 J.val.2 D
        (threshold J) rounds (F J) xi W G,
        Submodule.IsViable (3 / 200)
          (canonicalHalfSampledIntervalParent L q J.val.1 J.val.2 D
            (threshold J) rounds (F J) xi W v)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := fun (a b : ℕ) (U : IntervalResamplingChoices L q rounds) ↦
      balancedIntervalSpace (canonicalIntervalResamplingOperation
        D rounds threshold N F xi U) width hwidth a b
    let P := fun (a b : ℕ) (W : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable (3 / 200) W
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    intervalResamplingMeasure L q rounds
      {U | ¬(P p r (S p r U) ∧
        ∀ J : LongIntervalIndex L width,
          J.val ∈ balancedIntervalMergeList width hwidth p r →
          P J.val.1 J.val.2 (S J.val.1 J.val.2 U) ∧
            U ∈ canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J)} ≤
      ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  classical
  intro S P
  let H := fun J : ℕ × ℕ ↦ if h : J.1 ≤ J.2 ∧ J.2 ≤ L ∧ width < J.2 - J.1 then
    canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G ⟨J, h⟩ else ∅
  let operation := canonicalIntervalResamplingOperation D rounds threshold N F xi
  let μ := fun J : Fin (L + 1) × Fin (L + 1) ↦
    Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
  let E := fun J : ℕ × ℕ ↦
    {U : IntervalResamplingChoices L q rounds | let k := J.1 + (J.2 - J.1) / 2
      P J.1 k (S J.1 k U) ∧ P k J.2 (S k J.2 U) ∧ U ∉ H J}
  have hleaf (a b : ℕ) (_hab : a ≤ b) (_hbL : b ≤ L) (_hshort : b - a ≤ width) :
      P a b ⊤ := Submodule.isViable_top (3 / 200) (by norm_num) _
  have hnode (J : ℕ × ℕ) (hJ : J ∈ balancedIntervalMergeList width hwidth p r)
      (U : IntervalResamplingChoices L q rounds) :
      let k := J.1 + (J.2 - J.1) / 2
      P J.1 k (S J.1 k U) → P k J.2 (S k J.2 U) →
      U ∈ H J → P J.1 J.2 (S J.1 J.2 U) := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr hJ
    let I : LongIntervalIndex L width := ⟨J, hb.2.1, hb.2.2.1.trans hrL, hb.2.2.2⟩
    intro k hleft hright hhistory
    have hak : J.1 ≤ k := by dsimp only [k]; omega
    have hkb : k ≤ J.2 := by dsimp only [k]; omega
    let W := adjacentIntervalMerge L q J.1 k J.2 hak hkb (S J.1 k U) (S k J.2 U)
    have hW : Submodule.IsViable 0.04 W
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.1 J.2)).toLinearEquiv.toLinearMap) :=
      Submodule.IsCloseTo.of_le (isViable_adjacentIntervalMerge hak hkb G _ _ hleft hright)
        (by norm_num)
    have hvalid : J.1 ≤ J.2 ∧ J.2 ≤ L ∧ width < J.2 - J.1 := I.property
    have hhistory' : U ∈
        canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G I := by
      simpa only [H, dite_eq_left hvalid] using hhistory
    have hlocal := (hfixed I W hW).2 (U (LongIntervalIndex.coordinate I)) hhistory'
    have hvalue : S J.1 J.2 U = canonicalHalfSampledIntervalParent
        L q J.1 J.2 D (threshold I) rounds (F I) xi W
          (U (LongIntervalIndex.coordinate I)) := by
      change balancedIntervalSpace (operation U) width hwidth J.1 J.2 = _
      rw [balancedIntervalSpace, dite_eq_right (by omega : ¬J.2 - J.1 ≤ width)]
      simp only [operation, canonicalIntervalResamplingOperation,
        independentIntervalOperation, dite_eq_left (hb.2.2.1.trans hrL), dite_eq_left hb.2.2.2]
      rfl
    exact hvalue.symm ▸ hlocal
  have hE (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r}) :
      MeasurableSet (E J.val) := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    let I : LongIntervalIndex L width :=
      ⟨J.val, hb.2.1, hb.2.2.1.trans hrL, hb.2.2.2⟩
    let k := J.val.1 + (J.val.2 - J.val.1) / 2
    have hak : J.val.1 ≤ k := by dsimp only [k]; omega
    have hkb : k ≤ J.val.2 := by dsimp only [k]; omega
    have hleft := measurableSet_isViable_canonicalIntervalResamplingTree
      D rounds hwidth threshold N F xi G (3 / 200) J.val.1 k
      hak (hkb.trans I.property.2.1)
    have hright := measurableSet_isViable_canonicalIntervalResamplingTree
      D rounds hwidth threshold N F xi G (3 / 200) k J.val.2 hkb I.property.2.1
    have hhistory := measurableSet_canonicalIntervalResamplingHistory
      D rounds hwidth threshold N F xi G I
    have hvalid : J.val.1 ≤ J.val.2 ∧ J.val.2 ≤ L ∧ width < J.val.2 - J.val.1 := I.property
    have hH : H J.val =
        canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G I := by
      dsimp only [H]
      rw [dite_eq_left hvalid]
    change MeasurableSet {U | P J.val.1 k (S J.val.1 k U) ∧
      P k J.val.2 (S k J.val.2 U) ∧ U ∉ H J.val}
    rw [hH]
    exact hleft.inter (hright.inter hhistory.compl)
  have hsection (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r})
      (U : IntervalResamplingChoices L q rounds) :
      μ (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J)
        {v | Function.update U (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) v
          ∈ E J.val} ≤ beta := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    let I : LongIntervalIndex L width :=
      ⟨J.val, hb.2.1, hb.2.2.1.trans hrL, hb.2.2.2⟩
    let coord := LongIntervalIndex.coordinate I
    let k := J.val.1 + (J.val.2 - J.val.1) / 2
    have hak : J.val.1 ≤ k := by dsimp only [k]; omega
    have hkb : k ≤ J.val.2 := by dsimp only [k]; omega
    change μ coord {v | Function.update U coord v ∈ E J.val} ≤ beta
    have hshorter (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L)
        (hlen : b - a < J.val.2 - J.val.1)
        (v : Fin rounds → Matrix.rankUnitaryProduct
          (Fintype.card (interval L J.val.1 J.val.2 → Fin q))) :
        S a b (Function.update U coord v) = S a b U := by
      apply (measurable_projectionMatrix_and_dependsOn_canonicalIntervalResamplingTree
        D rounds hwidth threshold N F xi a b hab hbL).2
      intro B hB
      have hne : B ≠ coord := by
        intro heq
        subst B
        change J.val.2 - J.val.1 ≤ b - a at hB
        omega
      exact Function.update_of_ne hne v U
    have hleft (v) := hshorter J.val.1 k hak (hkb.trans I.property.2.1)
      (by dsimp only [k]; omega) v
    have hright (v) := hshorter k J.val.2 hkb I.property.2.1
      (by dsimp only [k]; omega) v
    by_cases hchildren : P J.val.1 k (S J.val.1 k U) ∧ P k J.val.2 (S k J.val.2 U)
    · let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hak hkb
        (S J.val.1 k U) (S k J.val.2 U)
      have hW : Submodule.IsViable 0.04 W
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) :=
        Submodule.IsCloseTo.of_le
          (isViable_adjacentIntervalMerge hak hkb G _ _ hchildren.1 hchildren.2) (by norm_num)
      have hvalid : J.val.1 ≤ J.val.2 ∧ J.val.2 ≤ L ∧ width < J.val.2 - J.val.1 := I.property
      have hH : H J.val =
          canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G I := by
        dsimp only [H]
        rw [dite_eq_left hvalid]
      apply (measure_mono ?_).trans (hfixed I W hW).1
      intro v hv
      change P J.val.1 k (S J.val.1 k (Function.update U coord v)) ∧
        P k J.val.2 (S k J.val.2 (Function.update U coord v)) ∧
        Function.update U coord v ∉ H J.val at hv
      intro hgood
      apply hv.2.2
      rw [hH]
      exact (canonicalIntervalResamplingHistory_update_parent
        D rounds hwidth threshold N F xi G I U v).2 hgood
    · have hempty : {v | Function.update U coord v ∈ E J.val} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro v hv
        apply hchildren
        change P J.val.1 k (S J.val.1 k (Function.update U coord v)) ∧
          P k J.val.2 (S k J.val.2 (Function.update U coord v)) ∧
          Function.update U coord v ∉ H J.val at hv
        exact ⟨(hleft v) ▸ hv.1, (hright v) ▸ hv.2.1⟩
      rw [hempty, measure_empty]
      exact bot_le
  have hbound := pi_balancedIntervalSpace_joint_history_failure_le μ operation
    width hwidth P H hleaf p r hpr hrL
    (balancedIntervalMergeCoordinate width hwidth p r hpr hrL) beta hnode hE hsection
  apply (measure_mono ?_).trans hbound
  intro U hfailure hgood
  apply hfailure
  refine ⟨hgood.1, ?_⟩
  intro J hJ
  have hlisted := hgood.2 J.val hJ
  refine ⟨hlisted.1, ?_⟩
  have hH : H J.val =
      canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J := by
    dsimp only [H]
    rw [dite_eq_left J.property]
  rw [← hH]
  exact hlisted.2

end TNLean.MPS.AreaLaw

end CanonicalIntervalRawTreeProbability
