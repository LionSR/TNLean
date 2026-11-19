/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalFamilyTrimmingMeasurable
import QICLean.Probability.RankUnitaryProductHaar
import QICLean.Analysis.RandomRangeSubspaceDimension
import QICLean.Analysis.ViableSubspaceTensorTransport

/-!
# The canonical sampled parent with `k` rounds and one trim

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, samples `s` vectors of a merged
space, applies `k` rounds of an improving family of operators and trims. This file realizes that
parent through one rank-independent Haar coordinate: the canonical range sample of the merged
space, the image under all words of length `k` in the family, and one collective trim of that
image. The coordinate is a product of unitary groups of every possible rank, fixed before the
merged space is known, so the parent is a jointly Borel function of the merged space and the
coordinate, as the independent-tree failure bound requires.

The fixed-input failure of the sample is Lemma `l:rs`, lines 530–558, with its rank-dependent
overlap `(1 - δ) min(s, Q) / (8 Q)`, transported from the canonical coordinates of the range to
the interval's own coordinates.

**Local fix (complex sphere net count):** the failure bound retains the corrected complex
sphere-net exponent of
https://sirui-lu.com/QICLean/paper-gaps/alvv16_random_sampling_net_count.pdf.
-/

open ManyBody (interval)

open MeasureTheory
open scoped TensorProduct Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The products of all words of length `power` in a finite family, indexed by one finite
type. Supporting ALVV, arXiv:1602.08828v2, `l:er`, lines 597–622. -/
noncomputable def wordFamily {N : ℕ} (F : Fin N → E →L[ℂ] E) (power : ℕ) :
    Fin (N ^ power) → E →L[ℂ] E :=
  fun i ↦ (List.ofFn (fun j ↦ F ((finFunctionFinEquiv.symm i) j))).prod

/-- The family of words spans the same image as the words themselves. -/
theorem iSup_map_wordFamily {N : ℕ} (F : Fin N → E →L[ℂ] E) (power : ℕ)
    (S : Submodule ℂ E) :
    ⨆ i, S.map (wordFamily F power i).toLinearMap =
      ⨆ w : Fin power → Fin N, S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap :=
  finFunctionFinEquiv.symm.iSup_comp
    (g := fun w : Fin power → Fin N ↦ S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap)

/-- The canonical range sample of an interval subspace: the orthogonal projection is written in
one fixed finite chart, its range is sampled through the coordinate of its rank, and the sample is
carried back to the interval's coordinates. Supporting ALVV, arXiv:1602.08828v2, Lemma `l:rs`,
lines 530–558. -/
noncomputable def canonicalIntervalRangeSample (L q p r s : ℕ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm W.starProjection
  (Matrix.randomRangeSubspace (P.reindex e.symm e.symm) s U).map
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap

/-- The canonical sampled parent: the canonical range sample, its image under all words of length
`power` in the family, and one collective trim of that image. Supporting ALVV,
arXiv:1602.08828v2, `l:rs`, lines 530–558, `l:er`, lines 597–622, `lem:trimming`,
lines 660–697, and `t:alg1`, lines 1777–1818. -/
noncomputable def canonicalSampledIntervalWordTrim (L q p r : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (power s : ℕ) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  intervalFamilyTrimStep L q p r (wordFamily F power) xi
    (canonicalIntervalRangeSample L q p r s W U)

/-- The canonical range sample has a jointly Borel orthogonal projection whenever the sampled
subspace does. -/
theorem measurable_projectionMatrix_canonicalIntervalRangeSample
    {X : Type*} [MeasurableSpace X] {L q p r : ℕ} (s : ℕ)
    (W : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection)) :
    Measurable (fun x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) ↦
      (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        (canonicalIntervalRangeSample L q p r s (W x.1) x.2).starProjection) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := fun x ↦ ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    (W x).starProjection).reindex e.symm e.symm
  have hP : Measurable P := by
    have hc : Continuous (fun M : Matrix (interval L p r → Fin q)
        (interval L p r → Fin q) ℂ ↦ M.reindex e.symm e.symm) := by
      change Continuous (fun M : Matrix (interval L p r → Fin q)
        (interval L p r → Fin q) ℂ ↦ fun i j ↦ M (e i) (e j))
      fun_prop
    exact hc.measurable.comp hW
  have hsample0 := (Matrix.measurable_randomRangeSubspace_projection s).comp
    ((hP.comp measurable_fst).prodMk measurable_snd)
  exact Submodule.measurable_projectionMatrix_map_piLpCongrLeft e
    (fun x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) ↦
      Matrix.randomRangeSubspace (P x.1) s x.2) hsample0

/-- The canonical sampled parent has a jointly Borel orthogonal projection whenever the merged
subspace does. -/
theorem measurable_projectionMatrix_canonicalSampledIntervalWordTrim
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (power s : ℕ) (xi : ℝ)
    (W : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection)) :
    Measurable (fun x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) ↦
      (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        (canonicalSampledIntervalWordTrim L q p r F power s xi (W x.1) x.2).starProjection) := by
  have hS := measurable_projectionMatrix_canonicalIntervalRangeSample (L := L) (q := q) (p := p)
    (r := r) s W hW
  have h := measurable_projectionMatrix_intervalFamilyTrimStep (wordFamily F power) xi
    (fun x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) ↦
      canonicalIntervalRangeSample L q p r s (W x.1) x.2) hS
  unfold canonicalSampledIntervalWordTrim
  exact h

/-- The canonical range sample has dimension at most the sample size `s`, for every coordinate. -/
theorem finrank_canonicalIntervalRangeSample (L q p r s : ℕ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
    Module.finrank ℂ (canonicalIntervalRangeSample L q p r s W U) ≤ s := by
  unfold canonicalIntervalRangeSample
  refine (Submodule.finrank_map_le _ _).trans ?_
  rw [Matrix.finrank_randomRangeSubspace]
  exact min_le_left _ _

/-- For every coordinate, the canonical parent has dimension at most the number of words times
the sample size. -/
theorem finrank_canonicalSampledIntervalWordTrim_le {L q p r N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (power s : ℕ) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
    Module.finrank ℂ (canonicalSampledIntervalWordTrim L q p r F power s xi W U) ≤
      N ^ power * s :=
  (finrank_intervalFamilyTrimStep_le (wordFamily F power) xi _).trans
    (Nat.mul_le_mul_left _ (finrank_canonicalIntervalRangeSample L q p r s W U))

private theorem range_reindex_projectionMatrix {σ : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}
    (e : Fin d ≃ σ) (W : Submodule ℂ (EuclideanSpace ℂ σ)) :
    LinearMap.range (Matrix.toEuclideanLin
      (((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm W.starProjection).reindex
        e.symm e.symm)) =
      W.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.toLinearMap := by
  have hprojection := Submodule.projectionMatrix_map_piLpCongrLeft e.symm W
  rw [← hprojection]
  let Wfin := W.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).toLinearMap
  let C := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  change LinearMap.range (C (C.symm Wfin.starProjection)).toLinearMap = _
  rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection,
    LinearIsometryEquiv.piLpCongrLeft_symm]

private theorem rank_reindex_projectionMatrix {σ : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}
    (e : Fin d ≃ σ) (W : Submodule ℂ (EuclideanSpace ℂ σ)) :
    (((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm W.starProjection).reindex
      e.symm e.symm).rank = Module.finrank ℂ W := by
  have hdim := Module.finrank_eq_card_basis (Matrix.rangeOrthonormalBasis
    ⟨((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm W.starProjection).reindex
      e.symm e.symm, rfl⟩).toBasis
  rw [range_reindex_projectionMatrix e W,
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.toLinearEquiv.finrank_map_eq] at hdim
  simpa only [Fintype.card_fin] using hdim.symm

/-- When the sampled subspace has dimension at most `s`, the canonical range sample is the whole
subspace, for every coordinate. -/
theorem canonicalIntervalRangeSample_eq_self_of_finrank_le {L q p r s : ℕ}
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Module.finrank ℂ W ≤ s)
    (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
    canonicalIntervalRangeSample L q p r s W U = W := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  dsimp only [canonicalIntervalRangeSample]
  rw [Matrix.randomRangeSubspace_eq_range_of_rank_le _ s
      ((rank_reindex_projectionMatrix e W).trans_le hW) U,
    range_reindex_projectionMatrix e W, ← Submodule.map_comp]
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).apply_symm_apply y
  · intro hx
    exact ⟨x, hx, (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).apply_symm_apply x⟩

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Lemma `l:rs` for the canonical range sample of an interval subspace `W` of dimension `Q`:
if `W` is `δ`-viable for `T`, the sample fails to be `(1 - c)`-viable, with
`c = (1 - δ) min(s, Q) / (8 Q)`, on a Haar set of measure at most
`(1 + 2 / √c)^{2 dim T} Q e^{-min(s, Q)/16}`. ALVV, arXiv:1602.08828v2, Lemma `l:rs`,
lines 530–558, under the local fix of this module. -/
theorem rankUnitaryHaar_not_isViable_canonicalIntervalRangeSample_le (L q p r s : ℕ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    {delta : ℝ} {T : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q) ⊗[ℂ] F)}
    (hT : Submodule.IsViable delta W T) :
    let Q := Module.finrank ℂ W
    Matrix.rankUnitaryHaar (Fintype.card (interval L p r → Fin q))
      {U | ¬Submodule.IsViable (1 - (1 - delta) * min s Q / (8 * (Q : ℝ)))
        (canonicalIntervalRangeSample L q p r s W U) T} ≤
      ENNReal.ofReal ((1 + 2 / Real.sqrt ((1 - delta) * min s Q / (8 * (Q : ℝ)))) ^
        (2 * Module.finrank ℂ T) * (Q : ℝ) * Real.exp (-(((min s Q : ℕ) : ℝ) / 16))) := by
  intro Q
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let I := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let J := TensorProduct.congrIsometry I.symm (LinearIsometryEquiv.refl ℂ F)
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  have hrange : LinearMap.range (Matrix.toEuclideanLin P) = W.map I.symm.toLinearMap :=
    range_reindex_projectionMatrix e W
  have hPrank : P.rank = Q := by
    have hdim := Module.finrank_eq_card_basis (Matrix.rangeOrthonormalBasis ⟨P, rfl⟩).toBasis
    rw [hrange, I.symm.toLinearEquiv.finrank_map_eq] at hdim
    simpa only [Fintype.card_fin] using hdim.symm
  have hTfin : Submodule.IsViable delta (LinearMap.range (Matrix.toEuclideanLin P))
      (T.map J.toLinearMap) := by
    rw [hrange]
    exact (Submodule.isViable_map_congrIsometry_iff I.symm (LinearIsometryEquiv.refl ℂ F)
      W T).mpr hT
  have hfailure := Matrix.rankUnitaryHaar_not_isViable_randomRangeSubspace_le P s hTfin
  rw [hPrank, J.toLinearEquiv.finrank_map_eq] at hfailure
  have hsample (c : ℝ) (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
      Submodule.IsViable c ((Matrix.randomRangeSubspace P s U).map I.toLinearMap) T ↔
        Submodule.IsViable c (Matrix.randomRangeSubspace P s U) (T.map J.toLinearMap) := by
    have h := Submodule.isViable_map_congrIsometry_iff I.symm (LinearIsometryEquiv.refl ℂ F)
      (delta := c) ((Matrix.randomRangeSubspace P s U).map I.toLinearMap) T
    simpa only [← Submodule.map_comp, LinearIsometryEquiv.toLinearEquiv_symm,
      LinearEquiv.symm_comp, Submodule.map_id] using h.symm
  refine (measure_mono ?_).trans hfailure
  intro U hbad hgood
  exact hbad ((hsample _ U).mpr hgood)

end TNLean.MPS.AreaLaw.ALVV
