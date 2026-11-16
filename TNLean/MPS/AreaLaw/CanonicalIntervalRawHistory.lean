/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalResampling
import QICLean.Analysis.StoppedHalfSamplingEvents

/-!
# The literal original-target history of an interval parent

The event is the existing native stopped-run event for the actual candidate
projection, fixed interval cuts and prescribed finite sequence. Its target
is the original whole-chain space in interval and full-exterior coordinates.
The event is jointly measurable when the actual candidate projection is
measurable; no sampling-success condition is assumed. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817.
-/

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
