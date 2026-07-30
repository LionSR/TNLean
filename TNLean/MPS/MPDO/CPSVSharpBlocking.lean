/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ActiveBNTRefinement
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum
import TNLean.MPS.MPDO.SourceBNTBlocking

/-!
# Sharp blocking bound for literal CPSV canonical form

A CPSV basis of normal tensors whose total representative bond dimension is at most `K`
has simultaneous product-algebra span at a positive length no greater than `3 * K ^ 5`.
Applying this estimate to the active representatives of literal CPSV canonical-form data
proves Proposition `propblockinj` of arXiv:1606.00608.

## Main results

* `IsCPSVBasisOfNormalTensors.exists_positive_wordTupleSpanTop_le_three_cap_pow_five`:
  the quantitative simultaneous spanning theorem for a source BNT.
* `IsCPSVCanonicalForm.exists_bnt_biCF_after_blocking_le_three_bondDim_pow_five`:
  literal CPSV canonical form becomes block-injective canonical form after blocking at most
  `3 * D ^ 5` sites.

## References

* arXiv:1606.00608, lines 317--345.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

private theorem wordTupleSpanTop_of_family_gaugeEquiv
    {g L : ℕ} {dim : Fin g → ℕ}
    {A B : (j : Fin g) → MPSTensor d (dim j)}
    (hSpan : WordTupleSpanTop A L)
    (hGauge : ∀ j, GaugeEquiv (A j) (B j)) :
    WordTupleSpanTop B L := by
  classical
  choose X hX using hGauge
  unfold WordTupleSpanTop at hSpan ⊢
  apply top_unique
  intro M _
  let M' : (j : Fin g) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ := fun j =>
    (↑((X j)⁻¹) : Matrix _ _ ℂ) * M j * (X j : Matrix _ _ ℂ)
  have hM' : M' ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
    rw [hSpan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM'
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).2
  refine ⟨c, ?_⟩
  funext j
  have hcj : (∑ w, c w • evalWord (A j) (List.ofFn w)) = M' j := by
    simpa [wordTuple, Fintype.linearCombination_apply] using congrFun hc j
  have hGoal : (∑ w, c w • evalWord (B j) (List.ofFn w)) = M j := by
    calc
      (∑ w, c w • evalWord (B j) (List.ofFn w)) =
          ∑ w, c w • ((X j : Matrix _ _ ℂ) *
            evalWord (A j) (List.ofFn w) *
            (↑((X j)⁻¹) : Matrix _ _ ℂ)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [evalWord_gauge (X j) (hX j)]
      _ = (X j : Matrix _ _ ℂ) *
          (∑ w, c w • evalWord (A j) (List.ofFn w)) *
          (↑((X j)⁻¹) : Matrix _ _ ℂ) := by
        rw [Matrix.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        simp
      _ = (X j : Matrix _ _ ℂ) * M' j *
          (↑((X j)⁻¹) : Matrix _ _ ℂ) := by rw [hcj]
      _ = M j := by simp [M', Matrix.mul_assoc]
  simpa [wordTuple] using hGoal

/-- A CPSV basis of normal tensors with total representative bond dimension at most `K`
has simultaneous product-algebra span at a positive length at most `3 * K ^ 5`.

The empty family is immediate. For one representative, the quantum Wielandt bound gives
length `K ^ 4`. For at least two representatives, the three-block separation argument gives
length `3 * (g - 1) * (K ^ 4 + 1)`, and positivity of every representative dimension implies
`g ≤ K`.

Source: arXiv:1606.00608, lines 317--345. -/
theorem IsCPSVBasisOfNormalTensors.exists_positive_wordTupleSpanTop_le_three_cap_pow_five
    {g K : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hK : 0 < K) (hDim : ∑ j, dim j ≤ K)
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 3 * K ^ 5 ∧ WordTupleSpanTop B L := by
  classical
  have hdimPos := hBNT.blocks_dim_pos
  have hdimLe : ∀ j, dim j ≤ K := by
    intro j
    exact (Finset.single_le_sum (fun k _ => Nat.zero_le (dim k))
      (Finset.mem_univ j)).trans hDim
  have hK4pos : 0 < K ^ 4 := Nat.pow_pos hK
  letI : ∀ j : Fin g, NeZero (dim j) := fun j => ⟨(hdimPos j).ne'⟩
  choose σ _hσ _hσfix hTP hGauge hPrim hIrr using
    fun j => (hBNT.blocks_normal j).exists_tpGauge
  let prepared : (j : Fin g) → MPSTensor d (dim j) :=
    fun j => tpGauge (B j) (σ j)
  have hPreparedDistinct : BlocksNotGaugePhaseEquiv (d := d) prepared := by
    intro j k hjk hdim hGPE
    apply hBNT.blocks_not_gaugePhaseEquiv j k hjk hdim
    exact gaugePhaseEquiv_of_gaugeEquiv_left_right_cast hdim
      (hGauge j) (by simpa [prepared] using hGPE) (hGauge k)
  have hPreparedNormal : ∀ j, IsNormal (prepared j) := by
    intro j
    exact isNormal_of_tp_primitive_irreducible
      (prepared j) (hTP j) (hPrim j) (hIrr j)
  have hBlk0 : ∀ j, IsNBlkInjective (prepared j) (K ^ 4) := by
    intro j
    have hOwn : IsNBlkInjective (prepared j) ((dim j) ^ 4) :=
      isNBlkInjective_pow_four_of_isNormal_leftCanonical
        (prepared j) (hTP j) (hPreparedNormal j)
    exact isNBlkInjective_of_le (Nat.pow_pos (hdimPos j)) hOwn
      (Nat.pow_le_pow_left (hdimLe j) 4)
  by_cases hCountZero : g = 0
  · subst g
    refine ⟨1, by omega, ?_, ?_⟩
    · have hK5pos : 0 < K ^ 5 := Nat.pow_pos hK
      omega
    · unfold WordTupleSpanTop
      apply top_unique
      intro X _
      have hX : X = 0 := by
        funext j
        exact Fin.elim0 j
      rw [hX]
      exact Submodule.zero_mem _
  by_cases hCountOne : g = 1
  · refine ⟨K ^ 4, hK4pos, ?_, ?_⟩
    · calc
        K ^ 4 = K ^ 4 * 1 := by simp
        _ ≤ K ^ 4 * (3 * K) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * K ^ 5 := by ring
    · have hPreparedSpan :=
        wordTupleSpanTop_of_card_eq_one_of_isNBlkInjective
          prepared hCountOne hBlk0
      exact wordTupleSpanTop_of_family_gaugeEquiv hPreparedSpan
        (fun j => (hGauge j).symm)
  · have hCountTwo : 2 ≤ g := by omega
    have hBlk1 : ∀ j, IsNBlkInjective (prepared j) (K ^ 4 + 1) := by
      intro j
      exact isNBlkInjective_of_le hK4pos (hBlk0 j) (by omega)
    have hBlk3 : ∀ j, IsNBlkInjective (prepared j)
        ((K ^ 4 + 1) + ((K ^ 4 + 1) + (K ^ 4 + 1))) := by
      intro j
      exact isNBlkInjective_of_le hK4pos (hBlk0 j) (by omega)
    have hIrrBlocks : HasIrreducibleBlocks (d := d) prepared :=
      HasIrreducibleBlocks.ofForall hIrr
    have hLeft : IsLeftCanonicalBlockFamily (d := d) prepared :=
      IsLeftCanonicalBlockFamily.ofForall hTP
    have hOverlap : HasNormalizedSelfOverlap (d := d) prepared :=
      HasNormalizedSelfOverlap.ofForall fun j =>
        overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
          (prepared j) (hIrr j) (hTP j) (hPrim j)
    have hPreparedSpan : WordTupleSpanTop prepared
        ((g - 1) * ((K ^ 4 + 1) + ((K ^ 4 + 1) + (K ^ 4 + 1)))) :=
      wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1
        prepared hIrrBlocks hLeft hOverlap hPreparedDistinct
        hBlk0 hBlk1 hBlk3 hK4pos hCountTwo
    have hSpan : WordTupleSpanTop B
        ((g - 1) * ((K ^ 4 + 1) + ((K ^ 4 + 1) + (K ^ 4 + 1)))) :=
      wordTupleSpanTop_of_family_gaugeEquiv hPreparedSpan
        (fun j => (hGauge j).symm)
    refine ⟨(g - 1) * ((K ^ 4 + 1) + ((K ^ 4 + 1) + (K ^ 4 + 1))),
      Nat.mul_pos (by omega) (by omega), ?_, hSpan⟩
    have hCountLeSum : g ≤ ∑ j, dim j := by
      calc
        g = ∑ _j : Fin g, 1 := by simp
        _ ≤ ∑ j : Fin g, dim j :=
          Finset.sum_le_sum fun j _ => hdimPos j
    have hCountLe : g ≤ K := hCountLeSum.trans hDim
    have hPredLe : g - 1 ≤ K - 1 := Nat.sub_le_sub_right hCountLe 1
    have hFirst :
        (g - 1) * ((K ^ 4 + 1) + ((K ^ 4 + 1) + (K ^ 4 + 1))) ≤
          (K - 1) * ((K ^ 4 + 1) + ((K ^ 4 + 1) + (K ^ 4 + 1))) :=
      Nat.mul_le_mul_right _ hPredLe
    refine hFirst.trans ?_
    calc
      (K - 1) * ((K ^ 4 + 1) + ((K ^ 4 + 1) + (K ^ 4 + 1))) =
          3 * ((K - 1) * (K ^ 4 + 1)) := by ring
      _ ≤ 3 * K ^ 5 :=
        three_mul_pred_mul_pow_four_add_one_le_three_mul_pow_five hK

/-- The active representative dimensions in literal CPSV canonical-form data sum to at most
the ambient bond dimension. -/
theorem CPSVCanonicalFormData.sum_activeRepresentative_dim_le
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) :
    ∑ j : Fin data.activePhaseClasses.g,
      data.dim (data.activeRepresentativeIndex j) ≤ D := by
  classical
  let firstCopyIndex : Fin data.activePhaseClasses.g → Fin data.r := fun j =>
    (data.activeClassCopyEquiv
      ⟨j, ⟨0, data.activePhaseClasses.copies_pos j⟩⟩ : data.Active).1
  have hFirstCopyIndex : ∀ j, firstCopyIndex j = data.activeRepresentativeIndex j := by
    intro j
    have hEnum : data.activePhaseClasses.enum j
        ⟨0, data.activePhaseClasses.copies_pos j⟩ =
        data.activePhaseClasses.repr j := by
      simp [CPSVCanonicalFormData.activePhaseClasses]
    change ((data.activeEquiv
      (data.activePhaseClasses.enum j
        ⟨0, data.activePhaseClasses.copies_pos j⟩) : data.Active) : Fin data.r) =
      ((data.activeEquiv (data.activePhaseClasses.repr j) : data.Active) : Fin data.r)
    rw [hEnum]
  have hInjective : Function.Injective firstCopyIndex := by
    intro j k hjk
    have hSubtype :
        data.activeClassCopyEquiv
            ⟨j, ⟨0, data.activePhaseClasses.copies_pos j⟩⟩ =
          data.activeClassCopyEquiv
            ⟨k, ⟨0, data.activePhaseClasses.copies_pos k⟩⟩ := by
      apply Subtype.ext
      exact hjk
    have hSigma := data.activeClassCopyEquiv.injective hSubtype
    exact congrArg Sigma.fst hSigma
  calc
    (∑ j : Fin data.activePhaseClasses.g,
        data.dim (data.activeRepresentativeIndex j)) =
        ∑ j : Fin data.activePhaseClasses.g, data.dim (firstCopyIndex j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hFirstCopyIndex j]
    _ = ∑ k ∈ Finset.image firstCopyIndex Finset.univ, data.dim k :=
      (Finset.sum_image hInjective.injOn).symm
    _ ≤ ∑ k ∈ Finset.univ, data.dim k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ k : Fin data.r, data.dim k := rfl
    _ ≤ D := data.total_dim_le

/-- **CPSV16 Proposition `propblockinj`.** A tensor in literal CPSV canonical form has an
active basis of normal tensors that becomes simultaneously block-injective after blocking a
positive number `L ≤ 3 * D ^ 5` of sites.

The conclusion is the one-letter span of the full product algebra of the chosen BNT. Inactive
zero-weight coordinates are not included among the representatives.

Source: arXiv:1606.00608, lines 317--345. -/
theorem IsCPSVCanonicalForm.exists_bnt_biCF_after_blocking_le_three_bondDim_pow_five
    {A : MPSTensor d D} [NeZero D] (hA : IsCPSVCanonicalForm A) :
    ∃ g : ℕ, ∃ dim : Fin g → ℕ,
      ∃ B : (j : Fin g) → MPSTensor d (dim j),
        IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩) ∧
        ∃ L : ℕ, 0 < L ∧ L ≤ 3 * D ^ 5 ∧
          WordTupleSpanTop (fun j => blockTensor (B j) L) 1 := by
  let data := Classical.choice hA
  let ref := data.activeBNTRefinement
  let dim : Fin data.activePhaseClasses.g → ℕ := fun j =>
    data.dim (data.activeRepresentativeIndex j)
  let B : (j : Fin data.activePhaseClasses.g) → MPSTensor d (dim j) := fun j =>
    data.blocks (data.activeRepresentativeIndex j)
  have hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩) := by
    simpa [dim, B] using ref.representativesBNT
  obtain ⟨L, hL, hLbound, hSpan⟩ :=
    hBNT.exists_positive_wordTupleSpanTop_le_three_cap_pow_five
      (NeZero.pos D) (by simpa [dim] using data.sum_activeRepresentative_dim_le)
  exact ⟨data.activePhaseClasses.g, dim, B, hBNT, L, hL, hLbound,
    wordTupleSpanTop_blockTensor_one B hSpan⟩

end MPSTensor
