/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap

/-!
# Singleton fixed-block cancellation for proportional BNT families

This module contains the no-tail base cases for the fixed-block cancellation
step in the proof of the proportional-MPV fundamental theorem.

The source passage is arXiv:1606.00608, Theorem `thm1`, lines 1181--1185:
after fixing one block on either side, the proof rules out the alternative
that all overlaps with blocks on the other side tend to zero, using
Lemma `Lem1`. The two results here prove that cancellation step in the
base cases where the fixed side has no other summands.

The general fixed-block cancellation obligations remain in
`TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap`; the remaining
coefficient-isolation argument is documented in
`docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section HeteroEqualCase

/-- **No-tail fixed-right all-overlaps-decay contradiction.**

Source: arXiv:1606.00608, Theorem `thm1`, line 1182. This is the base case of
the fixed-block cancellation step when the `B`-side has only the selected
block. Then the proportional weighted-state identity has no other `B`-summands
which could cancel the selected block, so Lemma `Lem1` coefficient extraction
directly contradicts the nonzero selected weight and nonzero proportionality
scalar. -/
lemma fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_finOne
    {d rA : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin 1 → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin 1 → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin 1) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (hAllDecay : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (B 0) N) atTop (nhds 0)) :
    False := by
  classical
  have hLI :=
    eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT
      A B hA hB 0 hAllDecay
  obtain ⟨c, hc, hState⟩ :=
    exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp
  let lhs : (N : ℕ) → Sum (Fin rA) (Fin 1) → ℂ := fun N =>
    Sum.elim (fun j : Fin rA => (μA j) ^ N) (fun _ : Fin 1 => 0)
  let rhs : (N : ℕ) → Sum (Fin rA) (Fin 1) → ℂ := fun N =>
    Sum.elim (fun _ : Fin rA => 0) (fun _ : Fin 1 => c N * (μB 0) ^ N)
  have hEqSum :
      ∀ᶠ N in atTop,
        ∑ x : Sum (Fin rA) (Fin 1),
            lhs N x • Sum.elim
              (fun j : Fin rA => mpvState (d := d) (A j) N)
              (fun _ : Fin 1 => mpvState (d := d) (B 0) N) x =
          ∑ x : Sum (Fin rA) (Fin 1),
            rhs N x • Sum.elim
              (fun j : Fin rA => mpvState (d := d) (A j) N)
              (fun _ : Fin 1 => mpvState (d := d) (B 0) N) x := by
    refine hState.mono ?_
    intro N hN
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [lhs, rhs, Sum.elim_inl, Sum.elim_inr, zero_smul, Finset.sum_const_zero,
      add_zero, zero_add]
    have hMain :
        (∑ x : Fin rA, (μA x) ^ N • mpvState (d := d) (A x) N) =
          (c N * (μB 0) ^ N) • mpvState (d := d) (B 0) N := by
      calc
        (∑ x : Fin rA, (μA x) ^ N • mpvState (d := d) (A x) N) =
          c N • (∑ k : Fin 1, (μB k) ^ N • mpvState (d := d) (B k) N) := hN
        _ = c N • ((μB 0) ^ N • mpvState (d := d) (B 0) N) := by
          congr 1
          exact Fintype.sum_eq_single 0 (fun k hk => (hk (Subsingleton.elim k 0)).elim)
        _ = (c N * (μB 0) ^ N) • mpvState (d := d) (B 0) N := by
          rw [smul_smul]
    simpa using hMain
  have hCoeff :=
    coefficient_eventually_eq_of_eventually_linearIndependent
      (fun N => Sum.elim
        (fun j : Fin rA => mpvState (d := d) (A j) N)
        (fun _ : Fin 1 => mpvState (d := d) (B 0) N))
      lhs rhs hLI hEqSum
  have hContradiction : ∀ᶠ N in (atTop : Filter ℕ), False := by
    refine (hCoeff.and hc).mono ?_
    intro N hN
    rcases hN with ⟨hCoeffN, hcN⟩
    have hCoeff0 : (0 : ℂ) = c N * (μB 0) ^ N := by
      simpa [lhs, rhs] using hCoeffN (Sum.inr (0 : Fin 1))
    exact (mul_ne_zero hcN (pow_ne_zero N
      (hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero 0))) hCoeff0.symm
  rcases (inferInstance : NeBot (atTop : Filter ℕ)).nonempty_of_mem hContradiction with
    ⟨N, hN⟩
  exact hN

/-- **No-tail fixed-left all-overlaps-decay contradiction.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1182--1185. This is the
symmetric base case of the fixed-block cancellation step when the `A`-side has
only the selected block. Then the proportional weighted-state identity has no
other `A`-summands which could cancel the selected block, so Lemma `Lem1`
coefficient extraction directly contradicts the nonzero selected weight and
nonzero proportionality scalar. -/
lemma fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_finOne
    {d rB : ℕ}
    {dimA : Fin 1 → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin 1 → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin 1) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (hAllDecay : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (A 0) (B k) N) atTop (nhds 0)) :
    False := by
  classical
  have hLI :=
    eventually_linearIndependent_all_right_single_left_of_all_overlaps_decay_CFBNT
      A B hA hB 0 hAllDecay
  obtain ⟨c, _hc, hState⟩ :=
    exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂
      A B hProp
  let lhs : (N : ℕ) → Sum (Fin rB) (Fin 1) → ℂ := fun N =>
    Sum.elim (fun k : Fin rB => c N * (μB k) ^ N) (fun _ : Fin 1 => 0)
  let rhs : (N : ℕ) → Sum (Fin rB) (Fin 1) → ℂ := fun N =>
    Sum.elim (fun _ : Fin rB => 0) (fun _ : Fin 1 => (μA 0) ^ N)
  have hEqSum :
      ∀ᶠ N in atTop,
        ∑ x : Sum (Fin rB) (Fin 1),
            lhs N x • Sum.elim
              (fun k : Fin rB => mpvState (d := d) (B k) N)
              (fun _ : Fin 1 => mpvState (d := d) (A 0) N) x =
          ∑ x : Sum (Fin rB) (Fin 1),
            rhs N x • Sum.elim
              (fun k : Fin rB => mpvState (d := d) (B k) N)
              (fun _ : Fin 1 => mpvState (d := d) (A 0) N) x := by
    refine hState.mono ?_
    intro N hN
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [lhs, rhs, Sum.elim_inl, Sum.elim_inr, zero_smul, Finset.sum_const_zero,
      add_zero, zero_add]
    have hMain :
        (∑ k : Fin rB, (c N * (μB k) ^ N) • mpvState (d := d) (B k) N) =
          (μA 0) ^ N • mpvState (d := d) (A 0) N := by
      calc
        (∑ k : Fin rB, (c N * (μB k) ^ N) • mpvState (d := d) (B k) N) =
            c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) := by
          rw [Finset.smul_sum]
          simp [smul_smul]
        _ = ∑ j : Fin 1, (μA j) ^ N • mpvState (d := d) (A j) N := hN.symm
        _ = (μA 0) ^ N • mpvState (d := d) (A 0) N := by
          exact Fintype.sum_eq_single 0 (fun j hj => (hj (Subsingleton.elim j 0)).elim)
    simpa using hMain
  have hCoeff :=
    coefficient_eventually_eq_of_eventually_linearIndependent
      (fun N => Sum.elim
        (fun k : Fin rB => mpvState (d := d) (B k) N)
        (fun _ : Fin 1 => mpvState (d := d) (A 0) N))
      lhs rhs hLI hEqSum
  have hContradiction : ∀ᶠ N in (atTop : Filter ℕ), False := by
    refine hCoeff.mono ?_
    intro N hCoeffN
    have hCoeff0 : (0 : ℂ) = (μA 0) ^ N := by
      simpa [lhs, rhs] using hCoeffN (Sum.inr (0 : Fin 1))
    exact (pow_ne_zero N (hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero 0)) hCoeff0.symm
  rcases (inferInstance : NeBot (atTop : Filter ℕ)).nonempty_of_mem hContradiction with
    ⟨N, hN⟩
  exact hN

end HeteroEqualCase

end MPSTensor
