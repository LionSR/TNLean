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
eventual linear-independence input is taken explicitly for the family
consisting of all `B`-blocks together with the remaining `A`-blocks. The phase
is assumed nonzero so that the selected `A`-summand can be rewritten in terms
of the selected `B`-summand before coefficient extraction.

**Scope restriction (explicit residual-family independence):** CPSV16 Lemma
`Lem1` gives this kind of independence only for the family in which all
off-diagonal overlaps tend to zero. In the fixed-block step of Theorem `thm1`,
lines 1181--1185, the local application gives independence for all blocks on
one side together with one fixed block on the other side, not for the whole
remaining tail appearing in this lemma. This auxiliary lemma must therefore
not be used as the source-faithful discharge of fixed-block cancellation unless
that residual-family independence has first been proved in the current
argument. See `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`. -/
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

/-- **Tail proportionality from the left phase-substituted residual span.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182 invokes Lemma
`Lem1`. This is the symmetric residual-span form of
`eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_notMem_residual_span`:
the selected `B`-state is assumed to be outside the span of the remaining
`B`-states together with the remaining `A`-states, after using the nonzero
phase to substitute the selected `A`-state.

**Scope restriction (residual-span exclusion):** The displayed span-exclusion
hypothesis must be derived from the fixed-block BNT separation argument before
this lemma is used as a source-faithful step. See
`docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`. -/
lemma eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_notMem_residual_span_left
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
    (hnot : ∀ᶠ N in atTop,
      mpvState (d := d) (B b0) N ∉
        Submodule.span ℂ
          (Set.range
            (Sum.elim
              (fun k : {k : Fin (nB + 1) // k ≠ b0} =>
                mpvState (d := d) (B k.1) N)
              (fun j : Fin nA => mpvState (d := d) (A (a0.succAbove j)) N))))
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
    refine eventually_selected_coefficient_eq_of_eventually_notMem_residual_span_sum
      (fun N k => mpvState (d := d) (B k) N)
      (fun N j => mpvState (d := d) (A (a0.succAbove j)) N)
      (fun N k => c N * (μB k) ^ N)
      (fun N => (μA a0) ^ N * (ζ ^ N)⁻¹)
      (fun N j => (μA (a0.succAbove j)) ^ N)
      b0 hnot ?_
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

/-- **Tail proportionality from the left residual independence input.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182 invokes Lemma
`Lem1`. This is the symmetric selected-plus-residual independence form of the
tail-peeling step: the selected `B`-state together with the residual `B`- and
`A`-states is assumed eventually linearly independent.

**Scope restriction (derived separation input):** The displayed eventual
linear-independence hypothesis must be derived from the CPSV16 fixed-block BNT
separation argument. See
`docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`. -/
lemma eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li_residual_left
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
        (fun o : Option (Sum {k : Fin (nB + 1) // k ≠ b0} (Fin nA)) =>
          match o with
          | none => mpvState (d := d) (B b0) N
          | some x =>
              Sum.elim
                (fun k : {k : Fin (nB + 1) // k ≠ b0} =>
                  mpvState (d := d) (B k.1) N)
                (fun j : Fin nA => mpvState (d := d) (A (a0.succAbove j)) N) x))
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
  have hnot :
      ∀ᶠ N in atTop,
        mpvState (d := d) (B b0) N ∉
          Submodule.span ℂ
            (Set.range
              (Sum.elim
                (fun k : {k : Fin (nB + 1) // k ≠ b0} =>
                  mpvState (d := d) (B k.1) N)
                (fun j : Fin nA => mpvState (d := d) (A (a0.succAbove j)) N))) := by
    filter_upwards [hLI] with N hLIN
    have hnone_not_mem :
        (none : Option (Sum {k : Fin (nB + 1) // k ≠ b0} (Fin nA))) ∉ Set.range some := by
      rintro ⟨x, hx⟩
      cases hx
    have himage :
        ((fun o : Option (Sum {k : Fin (nB + 1) // k ≠ b0} (Fin nA)) =>
            match o with
            | none => mpvState (d := d) (B b0) N
            | some x =>
                Sum.elim
                  (fun k : {k : Fin (nB + 1) // k ≠ b0} =>
                    mpvState (d := d) (B k.1) N)
                  (fun j : Fin nA => mpvState (d := d) (A (a0.succAbove j)) N) x) ''
          Set.range some) =
          Set.range
            (Sum.elim
              (fun k : {k : Fin (nB + 1) // k ≠ b0} =>
                mpvState (d := d) (B k.1) N)
              (fun j : Fin nA => mpvState (d := d) (A (a0.succAbove j)) N)) := by
      ext x
      constructor
      · rintro ⟨o, ⟨y, rfl⟩, rfl⟩
        exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨some y, ⟨y, rfl⟩, rfl⟩
    simpa [himage] using
      hLIN.notMem_span_image (s := Set.range some) (x := none) hnone_not_mem
  exact eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_notMem_residual_span_left
    A B c a0 b0 hc hζ hPhase hnot hState

end ProportionalExpansionLeft

end MPSTensor
