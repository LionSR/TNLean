/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.MutualInfoMonotone
import TNLean.MPS.MPDO.SectorTrace
import TNLean.Analysis.EntropyDecomposition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# A periodic MPDO without a thermodynamic limit

This file gives a classical translationally invariant MPDO whose normalized
periodic states alternate with the parity of the chain length.  It disproves
the unrestricted thermodynamic-limit assertion in Proposition 4.5 of
arXiv:1606.00608, lines 801--806.

The tensor has physical dimension two and bond dimension three.  Its only
nonzero physical slices are
\[
  M^{00}=\operatorname{diag}(1,0,0),\qquad
  M^{11}=\operatorname{diag}(0,1,-1).
\]
Consequently, the unnormalized operator on a chain of length~\(N\) is
\[
  \lvert 0^N\rangle\!\langle 0^N\rvert
  +\bigl(1+(-1)^N\bigr)\lvert 1^N\rangle\!\langle 1^N\rvert.
\]
It is positive semidefinite and has nonzero trace at every positive length.
For odd lengths its normalization is the first pure product state, whereas for
even lengths it is the mixture with weights \(1/3\) and \(2/3\).

## Main results

* `mpo_parityTensor_eq_diagonal`: the exact finite-chain operator.
* `parityTensor_isMPDO`: positivity at every positive chain length.
* `not_exists_tendsto_reducedBlockState_one_zero_zero`: the all-zero entry of
  the one-site reduced state has no thermodynamic limit.
* `mutualInfoChain_parityTensor_of_odd`: the mutual information is zero at odd
  chain lengths.
* `mutualInfoChain_parityTensor_of_even`: the mutual information is
  \(h_2(1/3)\) at positive even chain lengths.
* `not_exists_tendsto_parityMutualInfoAfterCut`: the mutual information has no
  thermodynamic limit at any fixed nonempty cut.

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.5, lines 801--806
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset Filter

namespace MPOTensor.ThermodynamicLimitCounterexample

private noncomputable def virtualWeight (a : Fin 3) (i j : Fin 2) : ℂ :=
  if i = j then
    ![if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 1 then -1 else 0] a
  else 0

/-- The diagonal classical tensor whose all-one sector cancels at odd lengths.

This is the counterexample to the unrestricted thermodynamic-limit clause of
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
noncomputable def parityTensor : MPOTensor 2 3 :=
  fun i j => Matrix.diagonal fun a => virtualWeight a i j

@[simp] private lemma parityTensor_apply (i j : Fin 2) :
    parityTensor i j = Matrix.diagonal fun a => virtualWeight a i j :=
  rfl

private lemma prod_parityTensor {N : ℕ} (σ τ : Fin N → Fin 2) :
    (List.ofFn fun k => parityTensor (σ k) (τ k)).prod =
      Matrix.diagonal fun a => ∏ k, virtualWeight a (σ k) (τ k) := by
  induction N with
  | zero =>
      simp only [List.ofFn_zero, List.prod_nil, Fin.prod_univ_zero]
      exact (Matrix.diagonal_one (n := Fin 3)).symm
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, parityTensor_apply, ih,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      rw [Fin.prod_univ_succ]

private lemma mpoMatrixEntry_eq_sum_prod {N : ℕ} (σ τ : Fin N → Fin 2) :
    mpoMatrixEntry parityTensor σ τ =
      ∑ a : Fin 3, ∏ k, virtualWeight a (σ k) (τ k) := by
  rw [mpoMatrixEntry, evalWord_ofFn, prod_parityTensor, Matrix.trace_diagonal]

private lemma mpo_off_diagonal {N : ℕ} {σ τ : Fin N → Fin 2} (hστ : σ ≠ τ) :
    mpo parityTensor N σ τ = 0 := by
  rw [mpo_apply, mpoMatrixEntry_eq_sum_prod]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hστ
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [virtualWeight, hk]

private lemma diagonalWeight_eq {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin 2) :
    (∑ a : Fin 3, ∏ k, virtualWeight a (σ k) (σ k)) =
      if (∀ k, σ k = 0) then 1 else if (∀ k, σ k = 1) then 1 + (-1 : ℂ) ^ N else 0 := by
  by_cases hzero : ∀ k, σ k = 0
  · simp [hzero, Fin.sum_univ_three, virtualWeight, hN.ne']
  · by_cases hone : ∀ k, σ k = 1
    · letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      simp [hone, Fin.sum_univ_three, virtualWeight, hN.ne']
    · push Not at hzero hone
      obtain ⟨kzero, hkzero⟩ := hzero
      obtain ⟨kone, hkone⟩ := hone
      have hσkzero : σ kzero = 1 := Fin.eq_one_of_ne_zero _ hkzero
      have hσkone : σ kone = 0 := by
        by_contra hne
        exact hkone (Fin.eq_one_of_ne_zero _ hne)
      have h0 : ∏ k, virtualWeight 0 (σ k) (σ k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ kzero)
        simp [virtualWeight, hσkzero]
      have h1 : ∏ k, virtualWeight 1 (σ k) (σ k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ kone)
        simp [virtualWeight, hσkone]
      have h2 : ∏ k, virtualWeight 2 (σ k) (σ k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ kone)
        simp [virtualWeight, hσkone]
      rw [if_neg (not_forall.mpr ⟨kzero, hkzero⟩),
        if_neg (not_forall.mpr ⟨kone, hkone⟩)]
      simp [Fin.sum_univ_three, h0, h1, h2]

/-- The finite-chain operator has support only on the two constant
configurations.  Its all-one weight is \(1+(-1)^N\).

This is the explicit finite-chain form of the counterexample to
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem mpo_parityTensor_eq_diagonal (N : ℕ) (hN : 0 < N) :
    mpo parityTensor N = Matrix.diagonal fun σ =>
      if (∀ k, σ k = 0) then 1 else if (∀ k, σ k = 1) then 1 + (-1 : ℂ) ^ N else 0 := by
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    rw [Matrix.diagonal_apply_eq, mpo_apply, mpoMatrixEntry_eq_sum_prod,
      diagonalWeight_eq hN]
  · rw [Matrix.diagonal_apply_ne _ hστ, mpo_off_diagonal hστ]

/-- The parity tensor generates positive semidefinite operators at every
positive chain length.

This gives a positive translationally invariant MPDO satisfying exactly the
hypotheses of arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem parityTensor_isMPDO : IsMPDO parityTensor := by
  intro N hN
  rw [mpo_parityTensor_eq_diagonal N hN]
  apply Matrix.PosSemidef.diagonal
  intro σ
  change 0 ≤ (if (∀ k, σ k = 0) then 1 else if (∀ k, σ k = 1) then
    1 + (-1 : ℂ) ^ N else 0)
  split_ifs with hzero hone
  · norm_num
  · rcases Nat.even_or_odd N with hEven | hOdd
    · simp [hEven.neg_one_pow, Complex.nonneg_iff]
    · simp [hOdd.neg_one_pow]
  · norm_num

private lemma verticalLoop_parityTensor :
    verticalLoop parityTensor = Matrix.diagonal ![(1 : ℂ), 1, -1] := by
  rw [verticalLoop_eq_physTraceTransfer]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [physTraceTransfer, parityTensor, virtualWeight, Fin.sum_univ_two]

/-- The trace of the finite-chain counterexample is \(2+(-1)^N\).

This is the normalization factor for the counterexample to arXiv:1606.00608,
Proposition 4.5, lines 801--806. -/
theorem trace_mpo_parityTensor (N : ℕ) :
    (mpo parityTensor N).trace = 2 + (-1 : ℂ) ^ N := by
  rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_parityTensor,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [Fin.sum_univ_three]
  ring

/-- The all-zero configuration has unnormalized weight one at every length. -/
private lemma mpo_zeroConfig (N : ℕ) (hN : 0 < N) :
    mpo parityTensor N (fun _ => 0) (fun _ => 0) = 1 := by
  rw [mpo_apply, mpoMatrixEntry_eq_sum_prod]
  simp [Fin.sum_univ_three, virtualWeight, hN.ne']

/-- At every odd length, the normalized all-zero diagonal entry is one.

This is the odd-length half of the counterexample to arXiv:1606.00608,
Proposition 4.5, lines 801--806. -/
theorem normalizedMPO_zeroConfig_of_odd {N : ℕ} (hN : Odd N) :
    normalizedMPO parityTensor N (fun _ => 0) (fun _ => 0) = 1 := by
  rw [normalizedMPO, Matrix.smul_apply, smul_eq_mul, trace_mpo_parityTensor,
    hN.neg_one_pow, mpo_zeroConfig N hN.pos]
  norm_num

/-- At every even length, the normalized all-zero diagonal entry is one third.

This is the even-length half of the counterexample to arXiv:1606.00608,
Proposition 4.5, lines 801--806. -/
theorem normalizedMPO_zeroConfig_of_even {N : ℕ} (hN : Even N) (hNpos : 0 < N) :
    normalizedMPO parityTensor N (fun _ => 0) (fun _ => 0) = 1 / 3 := by
  rw [normalizedMPO, Matrix.smul_apply, smul_eq_mul, trace_mpo_parityTensor,
    hN.neg_one_pow, mpo_zeroConfig N hNpos]
  norm_num

private def zeroSite : Fin 1 → Fin 2 := fun _ => 0

private theorem reducedBlockState_one_zero_zero (K : ℕ) :
    reducedBlockState parityTensor (K + 1) 1 (by omega) zeroSite zeroSite =
      normalizedMPO parityTensor (K + 1) (fun _ => 0) (fun _ => 0) := by
  classical
  let e := (blockReindexEquiv 2 (K + 1) 1 (by omega)).symm
  have e_const (j : Fin 2) : e (fun _ => j) = fun _ => j := by
    funext k
    simp only [e, blockReindexEquiv, Equiv.arrowCongr_symm, Equiv.refl_symm,
      Equiv.arrowCongr_apply, Equiv.coe_refl, id_eq, Function.comp_apply]
  have append_zero : Fin.append zeroSite (fun _ : Fin (K + 1 - 1) => (0 : Fin 2)) =
      (fun _ : Fin (1 + (K + 1 - 1)) => (0 : Fin 2)) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [zeroSite]
  have reindexed_zero :
      e (Fin.append zeroSite (fun _ : Fin (K + 1 - 1) => (0 : Fin 2))) = fun _ => 0 := by
    rw [append_zero, e_const]
  simp only [reducedBlockState, blockReducedState, Matrix.partialTraceRight_apply,
    Matrix.submatrix_apply, blockSplitEquiv_symm_apply]
  simp_rw [normalizedMPO, Matrix.smul_apply, smul_eq_mul,
    mpo_parityTensor_eq_diagonal (K + 1) (by omega), Matrix.diagonal_apply_eq]
  rw [Fintype.sum_eq_single (fun _ => 0)]
  · rw [show (blockReindexEquiv 2 (K + 1) 1 (by omega)).symm
        (Fin.append zeroSite (fun _ => 0)) = (fun _ => 0) from reindexed_zero]
    simp
  · intro x hx
    have append_ne_zero : Fin.append zeroSite x ≠ (fun _ => 0) := by
      intro h
      apply hx
      funext i
      have hi := congrFun h (Fin.natAdd 1 i)
      simpa using hi
    have append_ne_one : Fin.append zeroSite x ≠ (fun _ => 1) := by
      intro h
      have hi := congrFun h (Fin.castAdd (K + 1 - 1) (0 : Fin 1))
      norm_num [zeroSite] at hi
    have reindexed_ne_zero : e (Fin.append zeroSite x) ≠ (fun _ => 0) := by
      intro h
      apply append_ne_zero
      exact e.injective (h.trans (e_const 0).symm)
    have reindexed_ne_one : e (Fin.append zeroSite x) ≠ (fun _ => 1) := by
      intro h
      apply append_ne_one
      exact e.injective (h.trans (e_const 1).symm)
    have hnotzero : ¬∀ k, e (Fin.append zeroSite x) k = 0 := fun h =>
      reindexed_ne_zero (funext h)
    have hnotone : ¬∀ k, e (Fin.append zeroSite x) k = 1 := fun h =>
      reindexed_ne_one (funext h)
    rw [show (blockReindexEquiv 2 (K + 1) 1 (by omega)).symm
        (Fin.append zeroSite x) = e (Fin.append zeroSite x) from rfl]
    simp only [if_neg hnotzero, if_neg hnotone, mul_zero]

/-- The all-zero entry of the one-site reduced state is one at odd total
lengths.

This is the odd-length local marginal in the counterexample to
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem reducedBlockState_one_zero_zero_of_odd {N : ℕ} (hN : Odd N) :
    reducedBlockState parityTensor N 1 (by exact hN.pos) zeroSite zeroSite = 1 := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.pos.ne'
  rw [reducedBlockState_one_zero_zero, normalizedMPO_zeroConfig_of_odd hN]

/-- The all-zero entry of the one-site reduced state is one third at positive
even total lengths.

This is the even-length local marginal in the counterexample to
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem reducedBlockState_one_zero_zero_of_even {N : ℕ} (hN : Even N)
    (hNpos : 0 < N) :
    reducedBlockState parityTensor N 1 (by exact hNpos) zeroSite zeroSite = 1 / 3 := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  rw [reducedBlockState_one_zero_zero,
    normalizedMPO_zeroConfig_of_even hN hNpos]

/-- The one-site reduced states of the normalized periodic MPDO do not have a
thermodynamic limit: their all-zero diagonal entry alternates between one and
one third.

This is a formal obstruction to the inner limit asserted without further
hypotheses in arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem not_exists_tendsto_reducedBlockState_one_zero_zero :
    ¬∃ x : ℝ, Tendsto
      (fun K => (reducedBlockState parityTensor (K + 1) 1 (by omega)
        zeroSite zeroSite).re) atTop (nhds x) := by
  rintro ⟨x, hx⟩
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hx) (1 / 4) (by norm_num)
  have hOddLengthIndex := hK (2 * K) (by omega)
  have hEvenLengthIndex := hK (2 * K + 1) (by omega)
  rw [reducedBlockState_one_zero_zero_of_odd (show Odd (2 * K + 1) from ⟨K, by omega⟩)]
    at hOddLengthIndex
  rw [reducedBlockState_one_zero_zero_of_even
      (show Even (2 * K + 1 + 1) from ⟨K + 1, by omega⟩) (by omega)] at hEvenLengthIndex
  norm_num [Real.dist_eq] at hOddLengthIndex hEvenLengthIndex
  rw [abs_lt] at hOddLengthIndex hEvenLengthIndex
  linarith

/-! ## Mutual-information alternation -/

private def oddWeight {N : ℕ} (sigma : Fin N → Fin 2) : ℝ :=
  if ∀ k, sigma k = 0 then 1 else 0

private noncomputable def evenWeight {N : ℕ} (sigma : Fin N → Fin 2) : ℝ :=
  if ∀ k, sigma k = 0 then 1 / 3 else if ∀ k, sigma k = 1 then 2 / 3 else 0

private lemma forall_append_comp_cast_iff {L K N : ℕ} (u : Fin L → Fin 2)
    (w : Fin K → Fin 2) (h : N = L + K) (j : Fin 2) :
    (∀ k, (Fin.append u w ∘ Fin.cast h) k = j) ↔
      (∀ k, u k = j) ∧ (∀ k, w k = j) := by
  constructor
  · intro hall
    constructor
    · intro k
      simpa using hall (Fin.cast h.symm (Fin.castAdd K k))
    · intro k
      simpa using hall (Fin.cast h.symm (Fin.natAdd L k))
  · rintro ⟨hu, hw⟩ k
    change Fin.append u w (Fin.cast h k) = j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) (Fin.cast h k)
    · simp [hu]
    · simp [hw]

private lemma normalizedMPO_eq_diagonal_of_odd {N : ℕ} (hN : Odd N) :
    normalizedMPO parityTensor N =
      Matrix.diagonal fun sigma ↦ (oddWeight sigma : ℂ) := by
  rw [normalizedMPO, trace_mpo_parityTensor, hN.neg_one_pow,
    mpo_parityTensor_eq_diagonal N hN.pos]
  ext sigma tau
  by_cases hst : sigma = tau
  · subst tau
    rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    simp only [smul_eq_mul, oddWeight]
    split_ifs <;> norm_num [hN.neg_one_pow]
  · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hst,
      Matrix.diagonal_apply_ne _ hst, smul_zero]

private lemma normalizedMPO_eq_diagonal_of_even {N : ℕ} (hN : Even N)
    (hNpos : 0 < N) :
    normalizedMPO parityTensor N =
      Matrix.diagonal fun sigma ↦ (evenWeight sigma : ℂ) := by
  rw [normalizedMPO, trace_mpo_parityTensor, hN.neg_one_pow,
    mpo_parityTensor_eq_diagonal N hNpos]
  ext sigma tau
  by_cases hst : sigma = tau
  · subst tau
    rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    simp only [smul_eq_mul, evenWeight]
    split_ifs <;> norm_num [hN.neg_one_pow]
  · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hst,
      Matrix.diagonal_apply_ne _ hst, smul_zero]

private lemma reducedBlockState_eq_diagonal_of_odd {N L : ℕ} (hN : Odd N)
    (hLN : L ≤ N) :
    reducedBlockState parityTensor N L hLN =
      Matrix.diagonal fun sigma ↦ (oddWeight sigma : ℂ) := by
  ext u v
  rw [reducedBlockState_eq_sum]
  by_cases huv : u = v
  · subst v
    rw [Matrix.diagonal_apply_eq]
    simp_rw [normalizedMPO_eq_diagonal_of_odd hN,
      Matrix.diagonal_apply_eq, oddWeight, forall_append_comp_cast_iff]
    by_cases hu0 : ∀ k, u k = 0
    · have hu0eq : (∀ k, u k = 0) = True := propext (iff_true_intro hu0)
      rw [if_pos hu0]
      simp only [hu0eq, true_and]
      rw [Fintype.sum_eq_single (fun _ ↦ 0)]
      · simp
      · intro w hw
        have hnotzero : ¬∀ k, w k = 0 := fun h ↦ hw (funext h)
        simp [hnotzero]
    · have hu0eq : (∀ k, u k = 0) = False := propext (iff_false_intro hu0)
      rw [if_neg hu0]
      apply Finset.sum_eq_zero
      intro w _
      simp [hu0eq]
  · rw [Matrix.diagonal_apply_ne _ huv]
    apply Finset.sum_eq_zero
    intro w _
    rw [normalizedMPO_eq_diagonal_of_odd hN]
    apply Matrix.diagonal_apply_ne
    intro hfull
    apply huv
    funext k
    have hk := congrFun hfull
      (Fin.cast (show N = L + (N - L) by omega).symm (Fin.castAdd (N - L) k))
    simpa using hk

private lemma reducedBlockState_eq_diagonal_of_even {N L : ℕ} (hN : Even N)
    (hNpos : 0 < N) (hLpos : 0 < L) (hLN : L ≤ N) :
    reducedBlockState parityTensor N L hLN =
      Matrix.diagonal fun sigma ↦ (evenWeight sigma : ℂ) := by
  ext u v
  rw [reducedBlockState_eq_sum]
  by_cases huv : u = v
  · subst v
    rw [Matrix.diagonal_apply_eq]
    simp_rw [normalizedMPO_eq_diagonal_of_even hN hNpos,
      Matrix.diagonal_apply_eq, evenWeight, forall_append_comp_cast_iff]
    by_cases hu0 : ∀ k, u k = 0
    · have hu1 : ¬∀ k, u k = 1 := by
        intro h
        have h01 := (hu0 ⟨0, hLpos⟩).symm.trans (h ⟨0, hLpos⟩)
        norm_num at h01
      have hu0eq : (∀ k, u k = 0) = True := propext (iff_true_intro hu0)
      have hu1eq : (∀ k, u k = 1) = False := propext (iff_false_intro hu1)
      rw [if_pos hu0]
      simp only [hu0eq, hu1eq, true_and, false_and, if_false]
      rw [Fintype.sum_eq_single (fun _ ↦ 0)]
      · simp
      · intro w hw
        have hnotzero : ¬∀ k, w k = 0 := fun h ↦ hw (funext h)
        simp [hnotzero]
    · by_cases hu1 : ∀ k, u k = 1
      · have hu0eq : (∀ k, u k = 0) = False := propext (iff_false_intro hu0)
        have hu1eq : (∀ k, u k = 1) = True := propext (iff_true_intro hu1)
        rw [if_neg hu0, if_pos hu1]
        simp only [hu0eq, hu1eq, false_and, true_and, if_false]
        rw [Fintype.sum_eq_single (fun _ ↦ 1)]
        · simp
        · intro w hw
          have hnotone : ¬∀ k, w k = 1 := fun h ↦ hw (funext h)
          simp [hnotone]
      · have hu0eq : (∀ k, u k = 0) = False := propext (iff_false_intro hu0)
        have hu1eq : (∀ k, u k = 1) = False := propext (iff_false_intro hu1)
        rw [if_neg hu0, if_neg hu1]
        apply Finset.sum_eq_zero
        intro w _
        simp [hu0eq, hu1eq]
  · rw [Matrix.diagonal_apply_ne _ huv]
    apply Finset.sum_eq_zero
    intro w _
    rw [normalizedMPO_eq_diagonal_of_even hN hNpos]
    apply Matrix.diagonal_apply_ne
    intro hfull
    apply huv
    funext k
    have hk := congrFun hfull
      (Fin.cast (show N = L + (N - L) by omega).symm (Fin.castAdd (N - L) k))
    simpa using hk

/-- At odd length the normalized chain is the pure all-zero state.

This is the odd-length state used to test the inner limit in
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem normalizedMPO_parityTensor_of_odd {N : ℕ} (hN : Odd N) :
    normalizedMPO parityTensor N = Matrix.diagonal fun sigma ↦
      ((if ∀ k, sigma k = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  simpa [oddWeight] using normalizedMPO_eq_diagonal_of_odd hN

/-- At positive even length the normalized chain has precisely the two
constant configurations, with weights one third and two thirds.

This is the even-length state used to test the inner limit in
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem normalizedMPO_parityTensor_of_even {N : ℕ} (hN : Even N)
    (hNpos : 0 < N) :
    normalizedMPO parityTensor N = Matrix.diagonal fun sigma ↦
      ((if ∀ k, sigma k = 0 then (1 / 3 : ℝ)
        else if ∀ k, sigma k = 1 then 2 / 3 else 0 : ℝ) : ℂ) := by
  simpa [evenWeight] using normalizedMPO_eq_diagonal_of_even hN hNpos

/-- Every reduced block of an odd-length chain is the pure all-zero state.

This is the odd-length marginal in the counterexample to the inner limit of
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem reducedBlockState_parityTensor_of_odd {N L : ℕ} (hN : Odd N)
    (hLN : L ≤ N) :
    reducedBlockState parityTensor N L hLN = Matrix.diagonal fun sigma ↦
      ((if ∀ k, sigma k = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  simpa [oddWeight] using reducedBlockState_eq_diagonal_of_odd hN hLN

/-- Every nonempty reduced block of a positive even-length chain has the same
two nonzero eigenvalues, one third and two thirds, as the full state.

This is the even-length marginal in the counterexample to the inner limit of
arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem reducedBlockState_parityTensor_of_even {N L : ℕ} (hN : Even N)
    (hNpos : 0 < N) (hLpos : 0 < L) (hLN : L ≤ N) :
    reducedBlockState parityTensor N L hLN = Matrix.diagonal fun sigma ↦
      ((if ∀ k, sigma k = 0 then (1 / 3 : ℝ)
        else if ∀ k, sigma k = 1 then 2 / 3 else 0 : ℝ) : ℂ) := by
  simpa [evenWeight] using
    reducedBlockState_eq_diagonal_of_even hN hNpos hLpos hLN

private lemma vonNeumannEntropy_oddWeight {N : ℕ}
    (hd : (Matrix.diagonal fun sigma : Fin N → Fin 2 =>
      (oddWeight sigma : ℂ)).IsHermitian) :
    vonNeumannEntropy (Matrix.diagonal fun sigma : Fin N → Fin 2 =>
      (oddWeight sigma : ℂ)) hd = 0 := by
  rw [Matrix.vonNeumannEntropy_diagonal]
  apply Finset.sum_eq_zero
  intro sigma _
  by_cases hzero : ∀ k, sigma k = 0
  · simp [oddWeight, hzero, Real.negMulLog_one]
  · simp [oddWeight, hzero, Real.negMulLog_zero]

private lemma vonNeumannEntropy_evenWeight {N : ℕ} (hNpos : 0 < N)
    (hd : (Matrix.diagonal fun sigma : Fin N → Fin 2 =>
      (evenWeight sigma : ℂ)).IsHermitian) :
    vonNeumannEntropy (Matrix.diagonal fun sigma : Fin N → Fin 2 =>
      (evenWeight sigma : ℂ)) hd = Real.binEntropy (1 / 3) := by
  rw [Matrix.vonNeumannEntropy_diagonal]
  let zeroConfig : Fin N → Fin 2 := fun _ ↦ 0
  let oneConfig : Fin N → Fin 2 := fun _ ↦ 1
  have hzero_one : zeroConfig ≠ oneConfig := by
    intro h
    have := congrFun h ⟨0, hNpos⟩
    norm_num [zeroConfig, oneConfig] at this
  let f : (Fin N → Fin 2) → ℝ := fun sigma ↦ Real.negMulLog (evenWeight sigma)
  rw [show (∑ sigma, Real.negMulLog (evenWeight sigma)) = ∑ sigma, f sigma from rfl]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ zeroConfig)]
  rw [← Finset.add_sum_erase _ _
    (Finset.mem_erase.mpr ⟨hzero_one.symm, Finset.mem_univ oneConfig⟩)]
  have hremaining :
      ∑ sigma ∈ (Finset.univ.erase zeroConfig).erase oneConfig, f sigma = 0 := by
    apply Finset.sum_eq_zero
    intro sigma hsigma
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hsigma
    have hnotzero : ¬∀ k, sigma k = 0 := fun h ↦ hsigma.2 (funext h)
    have hnotone : ¬∀ k, sigma k = 1 := fun h ↦ hsigma.1 (funext h)
    simp [f, evenWeight, hnotzero, hnotone, Real.negMulLog_zero]
  rw [hremaining, add_zero]
  have hfzero : f zeroConfig = Real.negMulLog (1 / 3) := by
    norm_num [f, evenWeight, zeroConfig]
  have hfone : f oneConfig = Real.negMulLog (2 / 3) := by
    simp only [f, evenWeight, oneConfig]
    rw [if_neg]
    · norm_num
    · intro h
      have := h ⟨0, hNpos⟩
      norm_num at this
  rw [hfzero, hfone, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num

/-- Every reduced block of an odd-length chain has zero von Neumann entropy.

This is the entropy calculation underlying the odd-length mutual information
in the counterexample to arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem blockEntropy_parityTensor_of_odd {N L : ℕ} (hN : Odd N)
    (hLN : L ≤ N) :
    blockEntropy parityTensor N L hLN (parityTensor_isMPDO N hN.pos) = 0 := by
  let hd : (Matrix.diagonal fun sigma : Fin L → Fin 2 =>
      (oddWeight sigma : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      rw [isSelfAdjoint_iff]
      ext sigma
      simp [Complex.conj_ofReal])
  calc
    blockEntropy parityTensor N L hLN (parityTensor_isMPDO N hN.pos) =
        vonNeumannEntropy (Matrix.diagonal fun sigma : Fin L → Fin 2 =>
          (oddWeight sigma : ℂ)) hd :=
      vonNeumannEntropy_congr (reducedBlockState_eq_diagonal_of_odd hN hLN) _ _
    _ = 0 := vonNeumannEntropy_oddWeight hd

/-- Every nonempty reduced block of a positive even-length chain has von
Neumann entropy \(h_2(1/3)\).

This is the entropy calculation underlying the even-length mutual information
in the counterexample to arXiv:1606.00608, Proposition 4.5, lines 801--806. -/
theorem blockEntropy_parityTensor_of_even {N L : ℕ} (hN : Even N)
    (hNpos : 0 < N) (hLpos : 0 < L) (hLN : L ≤ N) :
    blockEntropy parityTensor N L hLN (parityTensor_isMPDO N hNpos) =
      Real.binEntropy (1 / 3) := by
  let hd : (Matrix.diagonal fun sigma : Fin L → Fin 2 =>
      (evenWeight sigma : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      rw [isSelfAdjoint_iff]
      ext sigma
      simp [Complex.conj_ofReal])
  calc
    blockEntropy parityTensor N L hLN (parityTensor_isMPDO N hNpos) =
        vonNeumannEntropy (Matrix.diagonal fun sigma : Fin L → Fin 2 =>
          (evenWeight sigma : ℂ)) hd :=
      vonNeumannEntropy_congr
        (reducedBlockState_eq_diagonal_of_even hN hNpos hLpos hLN) _ _
    _ = Real.binEntropy (1 / 3) := vonNeumannEntropy_evenWeight hLpos hd

/-- At odd total length, the mutual information across every proper cut is
zero.

This is the odd-length value of the quantity in arXiv:1606.00608,
Proposition 4.5, lines 795--806. -/
theorem mutualInfoChain_parityTensor_of_odd {N L : ℕ} (hN : Odd N)
    (hLN : L < N) :
    mutualInfoChain parityTensor N L (Nat.le_of_lt hLN)
      (parityTensor_isMPDO N hN.pos) = 0 := by
  rw [mutualInfoChain_eq,
    blockEntropy_parityTensor_of_odd hN (Nat.le_of_lt hLN),
    blockEntropy_parityTensor_of_odd hN (Nat.sub_le N L),
    blockEntropy_parityTensor_of_odd hN (le_refl N)]
  ring

/-- At positive even total length, the mutual information across every
nonempty proper cut is \(h_2(1/3)\).

This is the even-length value of the quantity in arXiv:1606.00608,
Proposition 4.5, lines 795--806. -/
theorem mutualInfoChain_parityTensor_of_even {N L : ℕ} (hN : Even N)
    (hLpos : 0 < L) (hLN : L < N) :
    mutualInfoChain parityTensor N L (Nat.le_of_lt hLN)
      (parityTensor_isMPDO N (by omega)) = Real.binEntropy (1 / 3) := by
  rw [mutualInfoChain_eq,
    blockEntropy_parityTensor_of_even hN (by omega) hLpos (Nat.le_of_lt hLN),
    blockEntropy_parityTensor_of_even hN (by omega) (by omega) (Nat.sub_le N L),
    blockEntropy_parityTensor_of_even hN (by omega) (by omega) (le_refl N)]
  ring

/-- For fixed block length \(L\), the mutual-information tail whose chain
length is \(N=L+K+1\).

This is exactly the inner sequence \(I_L^{(N)}\) from arXiv:1606.00608,
Proposition 4.5, lines 801--806, restricted to its natural range \(N>L\). -/
noncomputable def parityMutualInfoAfterCut (L K : ℕ) : ℝ :=
  mutualInfoChain parityTensor (L + K + 1) L (by omega)
    (parityTensor_isMPDO (L + K + 1) (by omega))

private lemma parityMutualInfoAfterCut_of_odd {L K : ℕ} (hN : Odd (L + K + 1)) :
    parityMutualInfoAfterCut L K = 0 := by
  rw [parityMutualInfoAfterCut, mutualInfoChain_parityTensor_of_odd hN (by omega)]

private lemma parityMutualInfoAfterCut_of_even {L K : ℕ} (hN : Even (L + K + 1))
    (hLpos : 0 < L) :
    parityMutualInfoAfterCut L K = Real.binEntropy (1 / 3) := by
  rw [parityMutualInfoAfterCut,
    mutualInfoChain_parityTensor_of_even hN hLpos (by omega)]

/-- The binary entropy \(h_2(1/3)\) appearing in the counterexample of
arXiv:1606.00608, lines 801--806, is strictly positive. -/
theorem binEntropy_one_div_three_pos : 0 < Real.binEntropy (1 / 3) :=
  Real.binEntropy_pos (by norm_num) (by norm_num)

/-- At every fixed nonempty cut, the mutual information has no thermodynamic
limit: its odd-length subsequence is zero, while its even-length subsequence is
the strictly positive value \(h_2(1/3)\).

This disproves the unrestricted inner-limit assertion in arXiv:1606.00608,
Proposition 4.5, lines 801--806. -/
theorem not_exists_tendsto_parityMutualInfoAfterCut (L : ℕ) (hLpos : 0 < L) :
    ¬∃ x : ℝ, Tendsto (parityMutualInfoAfterCut L) atTop (nhds x) := by
  rintro ⟨x, hx⟩
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hx)
    (Real.binEntropy (1 / 3) / 3) (by positivity [binEntropy_one_div_three_pos])
  let J := 2 * (K + L) + 1 - L - 1
  have hKJ : K ≤ J := by
    dsimp [J]
    omega
  have hOddLength : Odd (L + J + 1) := by
    refine ⟨K + L, ?_⟩
    dsimp [J]
    omega
  have hEvenLength : Even (L + (J + 1) + 1) := by
    refine ⟨K + L + 1, ?_⟩
    dsimp [J]
    omega
  have hOddIndex := hK J hKJ
  have hEvenIndex := hK (J + 1) (by omega)
  rw [parityMutualInfoAfterCut_of_odd hOddLength] at hOddIndex
  rw [parityMutualInfoAfterCut_of_even hEvenLength hLpos] at hEvenIndex
  rw [Real.dist_eq, abs_lt] at hOddIndex hEvenIndex
  linarith [binEntropy_one_div_three_pos]

end MPOTensor.ThermodynamicLimitCounterexample
