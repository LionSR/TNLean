/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Basic

/-!
# Diagonal restriction need not preserve injectivity

This file gives a two-dimensional counterexample to the assertion that the diagonal
restriction of a doubled-index horizontal canonical-form block must be injective.

The tensor consists of the four matrix units, with nonzero row-dependent coefficients.
Thus its four physical matrices span the full matrix algebra, while its diagonal
restriction contains only the two diagonal matrix units. The coefficients are chosen so
that the tensor is left-canonical. Since there is only one block, its injectivity also
supplies the finite-length block-separation property in `HorizontalCFData`.

This obstruction does not contradict Proposition 4.13 (source label `Prop:IV.12`) of
arXiv:1606.00608. In the proof at lines 1873--1921, positivity is first used to obtain
a new canonical form in the
vertical direction; the vertical basis of normal tensors is obtained from that canonical
form, not by restricting each horizontal basis tensor to physical pairs `(i, i)`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 (source label `Prop:IV.12`), lines 1863--1921
-/

open scoped Matrix BigOperators

namespace MPSTensor

section DiagonalRestrictionCounterexample

/-- A doubled-index tensor consisting of the four matrix units. The first row has
coefficient `3/5` and the second row has coefficient `4/5`. -/
private noncomputable def diagonalRestrictionUnits : MPSTensor (2 * 2) 2
  | 0 => (3 / 5 : ℂ) • Matrix.single 0 0 1
  | 1 => (3 / 5 : ℂ) • Matrix.single 0 1 1
  | 2 => (4 / 5 : ℂ) • Matrix.single 1 0 1
  | 3 => (4 / 5 : ℂ) • Matrix.single 1 1 1

/-- Evaluation at the physical pair `(a,b)` gives the corresponding matrix unit with
the row-dependent coefficient. -/
private theorem diagonalRestrictionUnits_finProd (a b : Fin 2) :
    diagonalRestrictionUnits (finProdFinEquiv (a, b)) =
      (if a = 0 then (3 / 5 : ℂ) else 4 / 5) • Matrix.single a b 1 := by
  fin_cases a <;> fin_cases b <;> norm_num [finProdFinEquiv, diagonalRestrictionUnits]

/-- Every matrix unit lies in the span of the four physical matrices. -/
private theorem single_mem_span_diagonalRestrictionUnits (a b : Fin 2) :
    Matrix.single a b (1 : ℂ) ∈
      Submodule.span ℂ (Set.range diagonalRestrictionUnits) := by
  have hmem : diagonalRestrictionUnits (finProdFinEquiv (a, b)) ∈
      Submodule.span ℂ (Set.range diagonalRestrictionUnits) :=
    Submodule.subset_span ⟨finProdFinEquiv (a, b), rfl⟩
  fin_cases a
  case «0» =>
    convert Submodule.smul_mem _ (5 / 3 : ℂ) hmem using 1
    rw [diagonalRestrictionUnits_finProd]
    ext i j
    simp [Matrix.single]
  case «1» =>
    convert Submodule.smul_mem _ (5 / 4 : ℂ) hmem using 1
    rw [diagonalRestrictionUnits_finProd]
    ext i j
    simp [Matrix.single]

/-- The doubled-index tensor is injective. -/
private theorem diagonalRestrictionUnits_isInjective : IsInjective diagonalRestrictionUnits := by
  rw [IsInjective, eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ => ?_))
  rw [show Matrix.single a b (M a b) = M a b • Matrix.single a b (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (single_mem_span_diagonalRestrictionUnits a b)

/-- The doubled-index tensor is left-canonical. -/
private theorem diagonalRestrictionUnits_leftCanonical :
    ∑ i : Fin (2 * 2), (diagonalRestrictionUnits i)ᴴ * diagonalRestrictionUnits i = 1 := by
  rw [Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [diagonalRestrictionUnits, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single]
  all_goals
    rw [map_ofNat (starRingEnd ℂ) 3, map_ofNat (starRingEnd ℂ) 4,
      map_ofNat (starRingEnd ℂ) 5]
    norm_num

/-- The diagonal restriction contains only the two diagonal matrix units. -/
private theorem diagBlock_diagonalRestrictionUnits_apply (i : Fin 2) :
    diagBlock diagonalRestrictionUnits i =
      (if i = 0 then (3 / 5 : ℂ) • Matrix.single 0 0 1
        else (4 / 5 : ℂ) • Matrix.single 1 1 1) := by
  fin_cases i <;> norm_num [diagBlock, finProdFinEquiv, diagonalRestrictionUnits]

/-- The diagonal restriction of the doubled-index tensor is not injective. -/
private theorem diagBlock_diagonalRestrictionUnits_not_isInjective :
    ¬ IsInjective (diagBlock diagonalRestrictionUnits) := by
  intro h
  suffices hzero : ∀ M ∈ Submodule.span ℂ (Set.range (diagBlock diagonalRestrictionUnits)),
      M 0 1 = 0 by
    have hmem : Matrix.single 0 1 (1 : ℂ) ∈
        Submodule.span ℂ (Set.range (diagBlock diagonalRestrictionUnits)) :=
      h ▸ Submodule.mem_top
    exact absurd (hzero _ hmem) one_ne_zero
  intro M hM
  induction hM using Submodule.span_induction with
  | mem M hM =>
      obtain ⟨i, rfl⟩ := hM
      fin_cases i <;> simp [diagBlock_diagonalRestrictionUnits_apply, Matrix.single]
  | zero => simp
  | add M N _ _ hM hN => simp [hM, hN]
  | smul c M _ hM => simp [hM]

/-- Every word in the diagonal restriction has vanishing `(0,1)` entry. -/
private theorem evalWord_diagBlock_diagonalRestrictionUnits_zero_one (w : List (Fin 2)) :
    evalWord (diagBlock diagonalRestrictionUnits) w 0 1 = 0 := by
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
      fin_cases i <;>
        simp [evalWord, diagBlock_diagonalRestrictionUnits_apply, Matrix.mul_apply,
          Matrix.single, ih]

/-- The diagonal restriction is not normal: blocking preserves its diagonal matrix
algebra and therefore never produces the missing off-diagonal matrix units. -/
private theorem diagBlock_diagonalRestrictionUnits_not_isNormal :
    ¬ IsNormal (diagBlock diagonalRestrictionUnits) := by
  rintro ⟨N, hN⟩
  have hmem : Matrix.single 0 1 (1 : ℂ) ∈
      Submodule.span ℂ (Set.range fun σ : Fin N → Fin 2 =>
        evalWord (diagBlock diagonalRestrictionUnits) (List.ofFn σ)) :=
    hN ▸ Submodule.mem_top
  suffices hzero : ∀ M ∈
      Submodule.span ℂ (Set.range fun σ : Fin N → Fin 2 =>
        evalWord (diagBlock diagonalRestrictionUnits) (List.ofFn σ)), M 0 1 = 0 by
    exact absurd (hzero _ hmem) one_ne_zero
  intro M hM
  induction hM using Submodule.span_induction with
  | mem M hM =>
      obtain ⟨σ, rfl⟩ := hM
      exact evalWord_diagBlock_diagonalRestrictionUnits_zero_one (List.ofFn σ)
  | zero => simp
  | add M K _ _ hM hK => simp [hM, hK]
  | smul c M _ hM => simp [hM]

/-- The single-block bond-dimension family used in the horizontal canonical form. -/
private abbrev diagonalRestrictionDim : Fin 1 → ℕ := fun _ => 2

/-- The nonzero weight of the single horizontal block. -/
private def diagonalRestrictionWeight : Fin 1 → ℂ := fun _ => 1

/-- The single horizontal block formed by the doubled-index matrix-unit tensor. -/
private noncomputable def diagonalRestrictionBlock :
    (k : Fin 1) → MPSTensor (2 * 2) (diagonalRestrictionDim k) :=
  fun _ => diagonalRestrictionUnits

/-- The doubled-index matrix-unit block satisfies all assumptions in
`HorizontalCFData`, including finite-length block separation. -/
private theorem diagonalRestrictionBlock_horizontalCFData :
    MPOTensor.HorizontalCFData diagonalRestrictionWeight diagonalRestrictionBlock := by
  refine {
    block_injective := ?_
    left_canonical := ?_
    weight_ne_zero := ?_
    biCF := ?_
  }
  · intro k
    fin_cases k
    exact diagonalRestrictionUnits_isInjective
  · intro k
    fin_cases k
    exact diagonalRestrictionUnits_leftCanonical
  · intro k
    simp [diagonalRestrictionWeight]
  · refine ⟨1, ?_⟩
    intro Δ hΔ k
    fin_cases k
    have hA : ∀ i : Fin (2 * 2),
        Matrix.trace (Δ 0 * diagonalRestrictionUnits i) = 0 := by
      intro i
      let w : Fin 1 → Fin (2 * 2) := fun _ => i
      have h := hΔ w
      simpa [w, diagonalRestrictionBlock, List.ofFn_succ, List.ofFn_zero, evalWord] using h
    have hzero : Δ 0 = 0 := (Matrix.trace_mul_right_eq_zero_iff (Δ 0)).mp (by
      intro N
      have hN : N ∈ Submodule.span ℂ (Set.range diagonalRestrictionUnits) := by
        rw [diagonalRestrictionUnits_isInjective]
        exact Submodule.mem_top
      induction hN using Submodule.span_induction with
      | mem N hN =>
          obtain ⟨i, rfl⟩ := hN
          exact hA i
      | zero => simp
      | add M N _ _ hM hN => simp [Matrix.mul_add, Matrix.trace_add, hM, hN]
      | smul c M _ hM => simp [Matrix.trace_smul, hM])
    simpa using hzero

/-- Horizontal canonical-form hypotheses do not imply injectivity after restriction
from physical pairs `(i,j)` to diagonal pairs `(i,i)`.

**Local obstruction (Proposition 4.13):** The proposition in arXiv:1606.00608,
source label `Prop:IV.12`, lines 1873--1921, obtains a new vertical canonical form from
positivity; it does not assert that the diagonal restrictions of the horizontal blocks
are normal. The source comparison is documented in
`docs/paper-gaps/cpgsv17_vertical_diagonal_restriction.tex`. -/
private theorem horizontalCFData_diagBlock_not_isInjective :
    MPOTensor.HorizontalCFData diagonalRestrictionWeight diagonalRestrictionBlock ∧
      ¬ (∀ k, IsInjective (diagBlock (diagonalRestrictionBlock k))) := by
  refine ⟨diagonalRestrictionBlock_horizontalCFData, ?_⟩
  intro h
  exact diagBlock_diagonalRestrictionUnits_not_isInjective (by
    simpa [diagonalRestrictionBlock] using h 0)

/-- Horizontal canonical-form hypotheses also do not imply normality of the
diagonally restricted blocks, even after arbitrary blocking. -/
theorem horizontalCFData_diagBlock_not_isNormal :
    MPOTensor.HorizontalCFData diagonalRestrictionWeight diagonalRestrictionBlock ∧
      ¬ (∀ k, IsNormal (diagBlock (diagonalRestrictionBlock k))) := by
  refine ⟨diagonalRestrictionBlock_horizontalCFData, ?_⟩
  intro h
  exact diagBlock_diagonalRestrictionUnits_not_isNormal (by
    simpa [diagonalRestrictionBlock] using h 0)

end DiagonalRestrictionCounterexample

end MPSTensor
