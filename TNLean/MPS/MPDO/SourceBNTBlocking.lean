/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.BNT.Bridge
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPDO.PostBlockedRepresentativeSpan

/-!
# Simultaneous blocking of a basis of normal tensors

A basis of normal tensors admits one positive physical blocking for which the
blocked representatives span their full product matrix algebra in one letter.
This is the simultaneous block-injectivity statement of arXiv:1606.00608,
lines 317--345, applied to the basis of normal tensors defined at lines
271--274.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A simultaneous length-`L` word span becomes a simultaneous one-letter
span after blocking `L` physical sites. -/
theorem wordTupleSpanTop_blockTensor_one
    {g : ℕ} {dim : Fin g → ℕ}
    (B : (j : Fin g) → MPSTensor d (dim j)) {L : ℕ}
    (hSpan : WordTupleSpanTop B L) :
    WordTupleSpanTop (fun j => blockTensor (B j) L) 1 := by
  unfold WordTupleSpanTop at hSpan ⊢
  have hRange :
      Set.range (wordTuple (fun j => blockTensor (B j) L) 1) =
        Set.range (wordTuple B L) := by
    ext M
    constructor
    · rintro ⟨σ, rfl⟩
      let τ : Fin L → Fin d := fun i =>
        blockedConfigEquiv d 1 L σ (Fin.cast (Nat.one_mul L).symm i)
      refine ⟨τ, ?_⟩
      funext j
      change evalWord (B j) (List.ofFn τ) =
        evalWord (blockTensor (B j) L) (List.ofFn σ)
      rw [evalWord_blockTensor]
      have hτ : List.ofFn τ = flattenBlockedWord d L (List.ofFn σ) := by
        calc
          List.ofFn τ = List.ofFn (blockedConfigEquiv d 1 L σ) := by
            exact (List.ofFn_congr (Nat.one_mul L)
              (blockedConfigEquiv d 1 L σ)).symm
          _ = flattenBlockedWord d L (List.ofFn σ) :=
            ofFn_blockedConfigEquiv d 1 L σ
      rw [hτ]
    · rintro ⟨τ, rfl⟩
      let τ' : Fin (1 * L) → Fin d := fun i =>
        τ (Fin.cast (Nat.one_mul L) i)
      let σ : Fin 1 → Fin (blockPhysDim d L) :=
        (blockedConfigEquiv d 1 L).symm τ'
      refine ⟨σ, ?_⟩
      funext j
      change evalWord (blockTensor (B j) L) (List.ofFn σ) =
        evalWord (B j) (List.ofFn τ)
      rw [evalWord_blockTensor]
      have hcfg : blockedConfigEquiv d 1 L σ = τ' := by
        simp [σ]
      have hlist : List.ofFn τ' = List.ofFn τ := by
        simp [τ']
      rw [← ofFn_blockedConfigEquiv d 1 L σ, hcfg, hlist]
  rw [hRange, hSpan]

private theorem hasBlockSelectorWords_of_family_gaugeEquiv
    {g : ℕ} {dim : Fin g → ℕ}
    {A B : (j : Fin g) → MPSTensor d (dim j)} {S : ℕ}
    (hSel : HasBlockSelectorWords A S)
    (hGauge : ∀ j, GaugeEquiv (A j) (B j)) :
    HasBlockSelectorWords B S := by
  intro k
  obtain ⟨c, hself, hoff⟩ := hSel k
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨X, hX⟩ := hGauge k
    calc
      (∑ w, c w • evalWord (B k) (List.ofFn w)) =
          ∑ w, c w • ((X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
            evalWord (A k) (List.ofFn w) *
            ((X⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [evalWord_gauge X hX]
      _ = (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
          (∑ w, c w • evalWord (A k) (List.ofFn w)) *
          ((X⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
        rw [Matrix.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        simp
      _ = 1 := by
        rw [hself]
        simp
  · intro j hjk
    obtain ⟨X, hX⟩ := hGauge j
    calc
      (∑ w, c w • evalWord (B j) (List.ofFn w)) =
          ∑ w, c w • ((X : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) *
            evalWord (A j) (List.ofFn w) *
            ((X⁻¹ : GL (Fin (dim j)) ℂ) : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [evalWord_gauge X hX]
      _ = (X : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) *
          (∑ w, c w • evalWord (A j) (List.ofFn w)) *
          ((X⁻¹ : GL (Fin (dim j)) ℂ) : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) := by
        rw [Matrix.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        simp
      _ = 0 := by
        rw [hoff j hjk]
        simp

/-- A basis of normal tensors has one common positive word length at which the
labelled word evaluations span the full product matrix algebra.

The BNT hypothesis supplies positive bond dimensions and excludes
gauge-phase-equivalent duplicate representatives.  Perron gauges put all
representatives in left-canonical form, after which the block-injectivity
argument gives simultaneous selectors.  The gauges are then removed and the
resulting injectivity and selectors give the simultaneous product-algebra
span at one positive word length.

Source: arXiv:1606.00608, BNT definition at lines 271--274 and block
injectivity at lines 317--345. -/
theorem IsCPSVBasisOfNormalTensors.exists_positive_wordTupleSpanTop
    {g : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    ∃ L : ℕ, 0 < L ∧ WordTupleSpanTop B L := by
  classical
  have hdimPos := hBNT.blocks_dim_pos
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
  obtain ⟨p, hp, hAtP⟩ :=
    exists_common_isNBlkInjective_of_isNormal_leftCanonical
      prepared hTP (fun j => (hdimPos j).ne') hPreparedNormal
  have hAtLeastP : ∀ j n, p ≤ n → IsNBlkInjective (prepared j) n := by
    intro j n hpn
    exact isNBlkInjective_of_le hp (hAtP j) hpn
  have hPreparedIrr : HasIrreducibleBlocks (d := d) prepared :=
    HasIrreducibleBlocks.ofForall hIrr
  have hPreparedLeft : IsLeftCanonicalBlockFamily (d := d) prepared :=
    IsLeftCanonicalBlockFamily.ofForall hTP
  have hPreparedOverlap : HasNormalizedSelfOverlap (d := d) prepared :=
    HasNormalizedSelfOverlap.ofForall fun j =>
      overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
        (prepared j) (hIrr j) (hTP j) (hPrim j)
  have hPair : HasPairBlockSeparatingWords prepared
      ((p + 1) + ((p + 1) + (p + 1))) :=
    hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1
      prepared hPreparedIrr hPreparedLeft hPreparedOverlap hPreparedDistinct
      hAtP
      (fun j => hAtLeastP j (p + 1) (by omega))
      (fun j => hAtLeastP j ((p + 1) + ((p + 1) + (p + 1))) (by omega))
      hp
  let selectorLength :=
    (g - 1) * ((p + 1) + ((p + 1) + (p + 1)))
  have hPreparedSelectors : HasBlockSelectorWords prepared selectorLength := by
    simpa [selectorLength] using
      hasBlockSelectorWords_of_pairBlockSeparatingWords prepared hPair
  have hSelectors : HasBlockSelectorWords B selectorLength :=
    hasBlockSelectorWords_of_family_gaugeEquiv hPreparedSelectors
      (fun j => (hGauge j).symm)
  have hOriginalAtP : ∀ j, IsNBlkInjective (B j) p := by
    intro j
    exact isNBlkInjective_of_gaugeEquiv (hAtP j) (hGauge j).symm
  have hSpan : WordTupleSpanTop B (p + selectorLength) :=
    wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords
      B hOriginalAtP hSelectors
  exact ⟨p + selectorLength, Nat.add_pos_left hp selectorLength, hSpan⟩

/-- A simultaneous product-algebra word span makes each component block injective
at the same length. -/
theorem isNBlkInjective_of_wordTupleSpanTop
    {g : ℕ} {dim : Fin g → ℕ}
    (B : (j : Fin g) → MPSTensor d (dim j)) {L : ℕ}
    (hSpan : WordTupleSpanTop B L) (j : Fin g) :
    IsNBlkInjective (B j) L := by
  classical
  unfold IsNBlkInjective
  apply top_unique
  intro M _
  let target : (k : Fin g) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
    fun k => if h : k = j then cast (congrArg (fun n => Matrix (Fin n) (Fin n) ℂ)
      (congrArg dim h.symm)) M else 0
  have htarget : target ∈ Submodule.span ℂ (Set.range (wordTuple B L)) := by
    rw [hSpan]
    exact Submodule.mem_top
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp htarget with ⟨c, hc⟩
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).2
  refine ⟨c, ?_⟩
  have hj := congrArg (fun X => X j) hc
  simpa [target, wordTuple, Fintype.linearCombination_apply] using hj

/-- Representative word tuples of a CPSV basis of normal tensors span their product
matrix algebra at every sufficiently large length.

Starting from one positive simultaneous span, its component words remain injective at
all larger lengths.  The original span also supplies fixed block selectors; concatenating
an injective prefix with those selectors gives the simultaneous span at each large length.

Source: arXiv:1606.00608, lines 317--345, used in Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem IsCPSVBasisOfNormalTensors.eventually_wordTupleSpanTop
    {g : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, WordTupleSpanTop B L := by
  obtain ⟨p, hp, hSpan⟩ := hBNT.exists_positive_wordTupleSpanTop
  have hSelectors : HasBlockSelectorWords B p :=
    hasBlockSelectorWords_of_wordTupleSpanTop B hSpan
  have hAtP : ∀ j, IsNBlkInjective (B j) p :=
    fun j => isNBlkInjective_of_wordTupleSpanTop B hSpan j
  exact eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective
    B hSelectors hp hAtP

/-- A basis of normal tensors becomes simultaneously injective after one
common positive blocking.

The common positive word span is absorbed into one physical letter by
blocking the same number of sites.

Source: arXiv:1606.00608, BNT definition at lines 271--274 and block
injectivity at lines 317--345. -/
theorem IsCPSVBasisOfNormalTensors.exists_blocked_wordTupleSpanTop_one
    {g : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    ∃ L : ℕ, 0 < L ∧
      WordTupleSpanTop (fun j => blockTensor (B j) L) 1 := by
  obtain ⟨L, hL, hSpan⟩ := hBNT.exists_positive_wordTupleSpanTop
  exact ⟨L, hL, wordTupleSpanTop_blockTensor_one B hSpan⟩

end MPSTensor
