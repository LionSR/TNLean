/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalDominant

/-!
# Asymptotic tail subtraction for proportional BNT families

This module records the asymptotic erased-tail cancellation obtained after the
dominant selected summands have been phase matched.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem thm1, lines 1170--1192.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section ProportionalTail

/-- **Leading-erased tail difference vanishes asymptotically.**

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. After a
leading `B`-block is phase-matched to the leading `A`-block, the selected
summand cancellation implies an asymptotic cancellation of the erased tails,
after normalization by the leading `A`-weight.

This is an asymptotic tail-subtraction statement. It does not assert exact
tail proportionality and does not use residual-family linear independence.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma exists_dominant_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ} {ζ : ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hζ : ‖ζ‖ = 1)
    (hPhase : ∀ N : ℕ,
      mpvState (d := d) (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N =
        ζ ^ N • mpvState (d := d) (A ⟨0, Nat.pos_of_ne_zero hrA⟩) N)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ c : ℕ → ℂ,
      (∀ᶠ N in atTop, c N ≠ 0) ∧
      (∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) ∧
      Tendsto
        (fun N : ℕ =>
          ‖(μA ⟨0, Nat.pos_of_ne_zero hrA⟩ ^ N)⁻¹ •
            ((∑ j ∈ Finset.univ.erase ⟨0, Nat.pos_of_ne_zero hrA⟩,
                (μA j) ^ N • mpvState (d := d) (A j) N) -
              c N •
                (∑ k ∈ Finset.univ.erase ⟨0, Nat.pos_of_ne_zero hrB⟩,
                  (μB k) ^ N • mpvState (d := d) (B k) N))‖)
        atTop (nhds (0 : ℝ)) := by
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  obtain ⟨c, hc, hState, hSelectedDiff⟩ :=
    exists_dominant_selected_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hζ hPhase hProp
  have hTailDiff :
      Tendsto
        (fun N : ℕ =>
          ‖(μA a0 ^ N)⁻¹ •
            ((∑ j ∈ Finset.univ.erase a0,
                (μA j) ^ N • mpvState (d := d) (A j) N) -
              c N •
                (∑ k ∈ Finset.univ.erase b0,
                  (μB k) ^ N • mpvState (d := d) (B k) N))‖)
        atTop (nhds (0 : ℝ)) := by
    refine Tendsto.congr' ?_ hSelectedDiff
    filter_upwards [hState] with N hStateN
    let selectedA :=
      (μA a0) ^ N • mpvState (d := d) (A a0) N
    let tailA :=
      ∑ j ∈ Finset.univ.erase a0,
        (μA j) ^ N • mpvState (d := d) (A j) N
    let selectedB :=
      (μB b0) ^ N • mpvState (d := d) (B b0) N
    let tailB :=
      ∑ k ∈ Finset.univ.erase b0,
        (μB k) ^ N • mpvState (d := d) (B k) N
    have hStateSplit : selectedA + tailA = c N • selectedB + c N • tailB := by
      have hA_sum :
          (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
            selectedA + tailA := by
        dsimp [selectedA, tailA]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
      have hB_sum :
          (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) =
            selectedB + tailB := by
        dsimp [selectedB, tailB]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b0)]
      calc
        selectedA + tailA =
            (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) := hA_sum.symm
        _ = c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N) := hStateN
        _ = c N • (selectedB + tailB) := by rw [hB_sum]
        _ = c N • selectedB + c N • tailB := by rw [smul_add]
    have hTail :
        tailA - c N • tailB = -(selectedA - c N • selectedB) := by
      calc
        tailA - c N • tailB = (selectedA + tailA) - selectedA - c N • tailB := by
          abel
        _ = (c N • selectedB + c N • tailB) - selectedA - c N • tailB := by
          rw [hStateSplit]
        _ = -(selectedA - c N • selectedB) := by
          abel
    have hNorm :
        ‖(μA a0 ^ N)⁻¹ • (tailA - c N • tailB)‖ =
          ‖(μA a0 ^ N)⁻¹ • (selectedA - c N • selectedB)‖ := by
      calc
        ‖(μA a0 ^ N)⁻¹ • (tailA - c N • tailB)‖ =
            ‖(μA a0 ^ N)⁻¹ • (-(selectedA - c N • selectedB))‖ := by
              rw [hTail]
        _ = ‖(μA a0 ^ N)⁻¹ • (selectedA - c N • selectedB)‖ := by
              rw [smul_neg, norm_neg]
    exact hNorm.symm
  exact ⟨c, hc, hState, by simpa [a0, b0] using hTailDiff⟩

end ProportionalTail

end MPSTensor
