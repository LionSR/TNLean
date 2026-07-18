/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.MutualInfoMonotone
import TNLean.MPS.MPDO.SectorTrace
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

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.5, lines 801--806
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset

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

private lemma diagonalWeight_nonneg {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin 2) :
    0 ≤ ∑ a : Fin 3, ∏ k, virtualWeight a (σ k) (σ k) := by
  by_cases hzero : ∀ k, σ k = 0
  · simp [Fin.sum_univ_three, virtualWeight, hzero, hN.ne']
  · by_cases hone : ∀ k, σ k = 1
    · rcases Nat.even_or_odd N with hEven | hOdd
      · simp [Fin.sum_univ_three, virtualWeight, hone, hN.ne', hEven.neg_one_pow,
          Complex.nonneg_iff]
      · simp [Fin.sum_univ_three, virtualWeight, hone, hN.ne', hOdd.neg_one_pow]
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
      rw [Fin.sum_univ_three, h0, h1, h2]
      simp

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
  rw [show mpo parityTensor N = Matrix.diagonal fun σ => mpo parityTensor N σ σ by
    ext σ τ
    by_cases hστ : σ = τ
    · subst τ
      simp
    · rw [Matrix.diagonal_apply_ne _ hστ, mpo_off_diagonal hστ]]
  apply Matrix.PosSemidef.diagonal
  exact fun σ => by
    change 0 ≤ (mpo parityTensor N) σ σ
    rw [mpo_apply, mpoMatrixEntry_eq_sum_prod]
    exact diagonalWeight_nonneg hN σ

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
  simp only [reducedBlockState, blockReducedState, Matrix.partialTraceRight_apply,
    Matrix.submatrix_apply, blockSplitEquiv_symm_apply, blockReindexEquiv,
    Equiv.arrowCongr_symm, Equiv.refl_symm, finCongr_symm]
  simp_rw [normalizedMPO, Matrix.smul_apply, smul_eq_mul,
    mpo_parityTensor_eq_diagonal (K + 1) (by omega), Matrix.diagonal_apply_eq]
  simp [zeroSite]

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
  have hEvenIndex := hK (2 * K) (by omega)
  have hOddIndex := hK (2 * K + 1) (by omega)
  rw [reducedBlockState_one_zero_zero_of_odd (show Odd (2 * K + 1) from ⟨K, by omega⟩)]
    at hEvenIndex
  rw [reducedBlockState_one_zero_zero_of_even
      (show Even (2 * K + 1 + 1) from ⟨K + 1, by omega⟩) (by omega)] at hOddIndex
  norm_num [Real.dist_eq] at hEvenIndex hOddIndex
  linarith

end MPOTensor.ThermodynamicLimitCounterexample
