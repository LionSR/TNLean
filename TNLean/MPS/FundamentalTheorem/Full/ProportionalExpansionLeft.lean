/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalExpansion

/-!
# Left phase-substituted tail proportionality

This module records the symmetric formulation of the tail-peeling step when the
selected phase relation is substituted on the left side of the weighted BNT block
sum.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem `thm1`, lines 1181--1185.
-/

open scoped BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section ProportionalExpansionLeft

/-- **Tail proportionality from the left phase-substituted family.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182 invokes Lemma
`Lem1`. This is the symmetric bookkeeping form of
`eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li`: the
eventual linear-independence input is taken for the family consisting of all
`B`-blocks together with the remaining `A`-blocks. The phase is assumed
nonzero so that the selected `A`-summand can be rewritten in terms of the
selected `B`-summand before coefficient extraction.

The assumption is that the displayed combined MPV family is linearly independent
for all sufficiently large lengths. In the proof of Theorem `thm1` this
assumption is supplied by the fixed-block application of Lemma `Lem1` at the
current peeling step. -/
lemma eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li_left
    {d nA nB : ℕ}
    {dimA : Fin (nA + 1) → ℕ} {dimB : Fin (nB + 1) → ℕ}
    {μA : Fin (nA + 1) → ℂ} {μB : Fin (nB + 1) → ℂ}
    {ζ : ℂ}
    (A : (j : Fin (nA + 1)) → MPSTensor d (dimA j))
    (B : (k : Fin (nB + 1)) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (a0 : Fin (nA + 1)) (b0 : Fin (nB + 1))
    (hc : ∀ᶠ N in atTop, c N ≠ 0)
    (hζ : ζ ≠ 0)
    (hPhase : ∀ N : ℕ,
      mpvState (d := d) (B b0) N = ζ ^ N • mpvState (d := d) (A a0) N)
    (hLI : ∀ᶠ N in atTop,
      LinearIndependent ℂ
        (Sum.elim
          (fun k : Fin (nB + 1) => mpvState (d := d) (B k) N)
          (fun j : Fin nA => mpvState (d := d) (A (a0.succAbove j)) N)))
    (hState : ∀ᶠ N in atTop,
      (∑ j : Fin (nA + 1), (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N •
          (∑ k : Fin (nB + 1), (μB k) ^ N • mpvState (d := d) (B k) N)) :
    EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks
        (fun j : Fin nA => μA (a0.succAbove j))
        (fun j : Fin nA => A (a0.succAbove j)))
      (toTensorFromBlocks
        (fun k : Fin nB => μB (b0.succAbove k))
        (fun k : Fin nB => B (b0.succAbove k))) := by
  classical
  have hA0_phase_inv : ∀ N : ℕ,
      mpvState (d := d) (A a0) N =
        (ζ ^ N)⁻¹ • mpvState (d := d) (B b0) N := by
    intro N
    rw [hPhase N, smul_smul]
    rw [inv_mul_cancel₀ (pow_ne_zero N hζ), one_smul]
  have hCoeff :
      ∀ᶠ N in atTop,
        c N * (μB b0) ^ N = (μA a0) ^ N * (ζ ^ N)⁻¹ := by
    refine eventually_selected_coefficient_eq_of_eventually_linearIndependent_sum
      (fun N k => mpvState (d := d) (B k) N)
      (fun N j => mpvState (d := d) (A (a0.succAbove j)) N)
      (fun N k => c N * (μB k) ^ N)
      (fun N => (μA a0) ^ N * (ζ ^ N)⁻¹)
      (fun N j => (μA (a0.succAbove j)) ^ N)
      b0 hLI ?_
    refine hState.mono ?_
    intro N hN
    have hAsplit :
        (∑ j : Fin (nA + 1), (μA j) ^ N • mpvState (d := d) (A j) N) =
          ((μA a0) ^ N • mpvState (d := d) (A a0) N) +
            ∑ j : Fin nA,
              (μA (a0.succAbove j)) ^ N •
                mpvState (d := d) (A (a0.succAbove j)) N := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
      congr 1
      exact weighted_mpvState_sum_erase_eq_sum_succAbove A a0 N
    calc
      (∑ k : Fin (nB + 1),
          (c N * (μB k) ^ N) • mpvState (d := d) (B k) N) =
          c N •
            (∑ k : Fin (nB + 1),
              (μB k) ^ N • mpvState (d := d) (B k) N) := by
        rw [Finset.smul_sum]
        simp [smul_smul]
      _ = ∑ j : Fin (nA + 1), (μA j) ^ N • mpvState (d := d) (A j) N := hN.symm
      _ =
          ((μA a0) ^ N • mpvState (d := d) (A a0) N) +
            ∑ j : Fin nA,
              (μA (a0.succAbove j)) ^ N •
                mpvState (d := d) (A (a0.succAbove j)) N := hAsplit
      _ =
          ((μA a0) ^ N * (ζ ^ N)⁻¹) • mpvState (d := d) (B b0) N +
            ∑ j : Fin nA,
              (μA (a0.succAbove j)) ^ N •
                mpvState (d := d) (A (a0.succAbove j)) N := by
        rw [hA0_phase_inv N, smul_smul]
  have hSelected :
      ∀ᶠ N in atTop,
        (μA a0) ^ N • mpvState (d := d) (A a0) N =
          c N • ((μB b0) ^ N • mpvState (d := d) (B b0) N) := by
    refine hCoeff.mono ?_
    intro N hN
    calc
      (μA a0) ^ N • mpvState (d := d) (A a0) N =
          ((μA a0) ^ N * (ζ ^ N)⁻¹) • mpvState (d := d) (B b0) N := by
        rw [hA0_phase_inv N, smul_smul]
      _ = (c N * (μB b0) ^ N) • mpvState (d := d) (B b0) N := by
        rw [← hN]
      _ = c N • ((μB b0) ^ N • mpvState (d := d) (B b0) N) := by
        rw [smul_smul]
  exact eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_total_and_selected
    A B c a0 b0 hc hState hSelected

end ProportionalExpansionLeft

end MPSTensor
