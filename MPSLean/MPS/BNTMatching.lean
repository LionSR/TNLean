import MPSLean.MPS.BasisNormalTensors

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# BNT matching infrastructure

This module provides the **permutation-matching** linear-algebra scaffolding for the proof of
Theorem 4.4 of arXiv:2011.12127 (Cirac–Pérez-García–Schuch–Verstraete, RMP 2021).

## Main results

### Pure linear algebra

* `exists_invertible_changeBasis`: If two finite families of vectors `v, w : Fin g → V` in a
  complex vector space are both linearly independent and span the same subspace, then there is an
  invertible `g × g` coefficient matrix `U` expressing each `w j` as a linear combination
  `w j = ∑ i, U i j • v i`.

### MPS application

* `MPSTensor.bntFamilies_eventually_linearIndependent`: Re-exports the BNT Gram-matrix criterion
  in a form suited to families with per-block bond dimension.

* `MPSTensor.eventually_exists_invertible_changeBasis`: If two BNT-like families produce MPV
  states that are eventually linearly independent and always span the same subspace, then for all
  sufficiently large system sizes there is an invertible coefficient matrix `U_N` expressing one
  family in terms of the other.

## Intended use (Thm 4.4 roadmap)

1. **Block separation** produces two BNT families `A_bnt` and `B_bnt` from tensors `A_total` and
   `B_total` that generate the same MPV family.
2. This module supplies the invertible `U_N` relating the two BNT families at each large `N`.
3. A **subsequent step** (not in this file) will show that `U_N` converges to a
   permutation-times-phase matrix, using the overlap orthonormality conditions.
-/

open scoped BigOperators Matrix
open Filter Finset

/-! ## Pure linear algebra: invertible change of basis -/

section LinearAlgebra

variable {g : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Auxiliary: express `w j` in the span of `v` and extract its coefficients.
Given LI `v` and `w j ∈ Submodule.span ℂ (Set.range v)`, define the coefficients. -/
private noncomputable def changeBasisCoeffs
    (v w : Fin g → V)
    (hw_mem : ∀ j, w j ∈ Submodule.span ℂ (Set.range v)) :
    Fin g → Fin g → ℂ :=
  fun j => Classical.choose ((Submodule.mem_span_range_iff_exists_fun ℂ).mp (hw_mem j))

private lemma changeBasisCoeffs_spec
    (v w : Fin g → V)
    (hw_mem : ∀ j, w j ∈ Submodule.span ℂ (Set.range v)) :
    ∀ j, ∑ i : Fin g, changeBasisCoeffs v w hw_mem j i • v i = w j :=
  fun j => Classical.choose_spec ((Submodule.mem_span_range_iff_exists_fun ℂ).mp (hw_mem j))

/--
**Invertible change-of-basis lemma.**

If two finite families of vectors `v, w : Fin g → V` in a complex vector space are both
linearly independent and span the same subspace, then there exists an invertible
`g × g` matrix `U` such that `w j = ∑ i, U i j • v i` for all `j`.

This is the key algebraic step in the BNT permutation-matching argument: it converts the
subspace-level agreement of two BNT families into a *matrix* equation whose asymptotics
(as the system size grows) can then be analysed.
-/
theorem exists_invertible_changeBasis
    (v w : Fin g → V)
    (_hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w)
    (hspan : Submodule.span ℂ (Set.range v) = Submodule.span ℂ (Set.range w)) :
    ∃ U : Matrix (Fin g) (Fin g) ℂ,
      U.det ≠ 0 ∧
      ∀ j : Fin g, w j = ∑ i : Fin g, U i j • v i := by
  classical
  -- Each `w j` lies in the span of `v`.
  have hw_mem : ∀ j, w j ∈ Submodule.span ℂ (Set.range v) := by
    intro j
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  -- Extract coefficients: for each `j`, ∃ `c j : Fin g → ℂ` with `∑ i, c j i • v i = w j`.
  let c := changeBasisCoeffs v w hw_mem
  have hc := changeBasisCoeffs_spec v w hw_mem
  -- Define the matrix `U i j := c j i` (transpose of the natural coefficient ordering).
  let U : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => c j i
  -- The expansion holds by construction.
  have hU : ∀ j, w j = ∑ i : Fin g, U i j • v i := by
    intro j
    exact (hc j).symm
  -- It remains to show `U.det ≠ 0`.
  -- Strategy: show `U.mulVec` is injective, hence `U` is a unit, hence `det U ≠ 0`.
  have hmulVec_zero : ∀ a : Fin g → ℂ, U.mulVec a = 0 → a = 0 := by
    intro a ha
    -- It suffices to show ∑ j, a j • w j = 0 (then LI of w gives a = 0).
    suffices h : ∑ j : Fin g, a j • w j = 0 by
      exact funext (Fintype.linearIndependent_iff.mp hw a h)
    -- Compute: ∑ j, a j • w j = ∑ i, (U.mulVec a) i • v i = 0.
    calc ∑ j : Fin g, a j • w j
        = ∑ j, a j • (∑ i, U i j • v i) := by simp_rw [hU]
      _ = ∑ j, ∑ i, (a j * U i j) • v i := by simp_rw [Finset.smul_sum, smul_smul]
      _ = ∑ i, ∑ j, (a j * U i j) • v i := Finset.sum_comm
      _ = ∑ i, (∑ j, a j * U i j) • v i := by simp_rw [← Finset.sum_smul]
      _ = ∑ i, (U.mulVec a) i • v i := by
            congr 1; ext i; congr 1
            simp only [Matrix.mulVec, dotProduct]
            exact Finset.sum_congr rfl fun j _ => mul_comm (a j) (U i j)
      _ = 0 := by simp [ha]
  -- Deduce injectivity of U.mulVec.
  have hinj : Function.Injective U.mulVec := by
    intro a b hab
    have h0 : U.mulVec (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    exact eq_of_sub_eq_zero (hmulVec_zero _ h0)
  -- Injectivity of mulVec implies U is a unit.
  have hunit : IsUnit U := Matrix.mulVec_injective_iff_isUnit.mp hinj
  -- A unit matrix has nonzero determinant.
  have hdet : U.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det U).mp hunit).ne_zero
  exact ⟨U, hdet, hU⟩

end LinearAlgebra

/-! ## MPS application -/

namespace MPSTensor

open MPSTensor

/--
**BNT families are eventually linearly independent.**

Given a finite family of MPS tensors `A j` (with possibly different bond dimensions `dim j`)
whose pairwise overlaps converge to the Kronecker delta, the MPV states `mpvState (A j) N` are
linearly independent for all sufficiently large `N`.

This is a direct repackaging of
`MPSTensor.eventually_linearIndependent_of_overlap_tendsto_orthonormal`
in the exact form used by the BNT permutation-matching argument.
-/
theorem bntFamilies_eventually_linearIndependent
    {d g : ℕ} {dim : Fin g → ℕ}
    (A : (j : Fin g) → MPSTensor d (dim j))
    (h_diag : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (h_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds (0 : ℂ))) :
    ∀ᶠ N in atTop,
      LinearIndependent ℂ (fun j : Fin g => mpvState (d := d) (A j) N) :=
  eventually_linearIndependent_of_overlap_tendsto_orthonormal A h_diag h_off

/--
**Eventually invertible change-of-basis matrix from equal spans.**

Given two BNT-like families of MPS tensors whose pairwise overlaps converge to orthonormality
(so both are eventually linearly independent), and whose MPV state spans agree for every system
size `N`, there is—for all large enough `N`—an invertible `g × g` coefficient matrix `U_N`
satisfying

`mpvState (B j) N = ∑ i, U_N i j • mpvState (A i) N`.

This is the algebraic bridge between "same MPV subspace" and "matrix equation" that is needed
for the permutation-matching step in Thm 4.4.
-/
theorem eventually_exists_invertible_changeBasis
    {d g : ℕ} {dimA dimB : Fin g → ℕ}
    (A : (j : Fin g) → MPSTensor d (dimA j))
    (B : (j : Fin g) → MPSTensor d (dimB j))
    (hA_diag : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds (0 : ℂ)))
    (hB_diag : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (B j) (B j) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (B i) (B j) N) atTop (nhds (0 : ℂ)))
    (hspan : ∀ N : ℕ,
      Submodule.span ℂ (Set.range (fun j : Fin g => mpvState (d := d) (A j) N)) =
      Submodule.span ℂ (Set.range (fun j : Fin g => mpvState (d := d) (B j) N))) :
    ∀ᶠ N in atTop, ∃ U : Matrix (Fin g) (Fin g) ℂ,
      U.det ≠ 0 ∧
      ∀ j : Fin g,
        mpvState (d := d) (B j) N =
          ∑ i : Fin g, U i j • mpvState (d := d) (A i) N := by
  -- Both families are eventually LI.
  have hA_li := bntFamilies_eventually_linearIndependent A hA_diag hA_off
  have hB_li := bntFamilies_eventually_linearIndependent B hB_diag hB_off
  -- Combine the two "eventually" filters.
  filter_upwards [hA_li, hB_li] with N hA_N hB_N
  -- Apply the pure linear-algebra change-of-basis lemma.
  exact exists_invertible_changeBasis
    (fun j => mpvState (d := d) (A j) N)
    (fun j => mpvState (d := d) (B j) N)
    hA_N hB_N (hspan N)

end MPSTensor
