/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Complex.BigOperators

/-!
# Projection-geometry lemmas for martingale estimates

This file collects small finite-dimensional Hilbert-space lemmas used by the
parent-Hamiltonian martingale method.  The main theorem is a purely algebraic
quadratic-form reduction for a finite sum of symmetric projections: if the
ordered off-diagonal terms satisfy a row-summable anti-commutator bound, then
`H = ∑ i, P i` satisfies `H² ≥ γ H` as a quadratic form.

The statements deliberately keep the MPS/Friedrichs-angle estimates as explicit
hypotheses.  They provide the reusable projection-geometry layer into which the
model-specific overlap and row-sum bounds can later be plugged.
-/

open scoped BigOperators InnerProductSpace

namespace ProjectionGeometry

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The quadratic form of a positive-order comparison is monotone. -/
theorem re_inner_le_of_le {S T : E →ₗ[ℂ] E} (h : S ≤ T) (v : E) :
    (⟪S v, v⟫_ℂ).re ≤ (⟪T v, v⟫_ℂ).re := by
  have hpos : (T - S).IsPositive := h
  have hnonneg := hpos.re_inner_nonneg_left v
  simpa [LinearMap.sub_apply, inner_sub_left, map_sub, sub_nonneg] using hnonneg

/-- The real quadratic form of the anti-commutator of two symmetric operators is
twice the ordered cross term. This is the algebraic form behind the usual
martingale estimate `P Q + Q P ≥ -ε (P + Q)`. -/
theorem IsSymmetric.re_inner_anticommutator
    {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hQ : Q.IsSymmetric) (v : E) :
    (⟪(P * Q + Q * P) v, v⟫_ℂ).re = 2 * (⟪P v, Q v⟫_ℂ).re := by
  have hPQ : ⟪(P * Q) v, v⟫_ℂ = ⟪Q v, P v⟫_ℂ := by
    change ⟪P (Q v), v⟫_ℂ = ⟪Q v, P v⟫_ℂ
    exact hP (Q v) v
  have hQP : ⟪(Q * P) v, v⟫_ℂ = ⟪P v, Q v⟫_ℂ := by
    change ⟪Q (P v), v⟫_ℂ = ⟪P v, Q v⟫_ℂ
    exact hQ (P v) v
  have hRe : (⟪Q v, P v⟫_ℂ).re = (⟪P v, Q v⟫_ℂ).re := by
    exact inner_re_symm (𝕜 := ℂ) (Q v) (P v)
  calc
    (⟪(P * Q + Q * P) v, v⟫_ℂ).re
        = (⟪(P * Q) v, v⟫_ℂ + ⟪(Q * P) v, v⟫_ℂ).re := by
            simp [LinearMap.add_apply, inner_add_left]
    _ = (⟪Q v, P v⟫_ℂ + ⟪P v, Q v⟫_ℂ).re := by rw [hPQ, hQP]
    _ = 2 * (⟪P v, Q v⟫_ℂ).re := by
      rw [Complex.add_re, hRe]
      ring

/-- For a symmetric projection `P`, the diagonal term in `‖P v‖²` is its
quadratic form. -/
theorem IsSymmetricProjection.re_inner_apply_apply_self
    {P : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) (v : E) :
    (⟪P v, P v⟫_ℂ).re = (⟪P v, v⟫_ℂ).re := by
  have hidem : P (P v) = P v := by
    simpa [Module.End.mul_apply] using congrArg (fun T : E →ₗ[ℂ] E => T v) hP.isIdempotentElem.eq
  calc
    (⟪P v, P v⟫_ℂ).re = (⟪P (P v), v⟫_ℂ).re := by
      exact congrArg Complex.re ((hP.isSymmetric (P v) v).symm)
    _ = (⟪P v, v⟫_ℂ).re := by
      rw [hidem]

/-- A symmetric projection has nonnegative quadratic form. -/
theorem IsSymmetricProjection.re_inner_nonneg
    {P : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) (v : E) :
    0 ≤ (⟪P v, v⟫_ℂ).re :=
  hP.isPositive.re_inner_nonneg_left v

/-- The quadratic form of a finite sum expands into the finite sum of quadratic
forms. -/
theorem re_inner_sum_apply_left (P : ι → E →ₗ[ℂ] E) (v : E) :
    (⟪(∑ i, P i) v, v⟫_ℂ).re = ∑ i, (⟪P i v, v⟫_ℂ).re := by
  simp only [LinearMap.sum_apply, sum_inner]
  rw [Complex.re_sum]

/-- The norm-square quadratic form of a finite sum expands into all ordered
cross terms. -/
theorem re_inner_sum_apply_apply (P : ι → E →ₗ[ℂ] E) (v : E) :
    (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re =
      ∑ i, ∑ j, (⟪P i v, P j v⟫_ℂ).re := by
  simp only [LinearMap.sum_apply, sum_inner, inner_sum]
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]

section OffDiagonal

variable [DecidableEq ι]

/-- Split an ordered double sum into diagonal and off-diagonal parts. -/
theorem sum_sum_eq_diag_add_offdiag (f : ι → ι → ℝ) :
    (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) := by
  calc
    (∑ i, ∑ j, f i j) =
        ∑ i, (f i i + ∑ j ∈ Finset.univ.erase i, f i j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact (Finset.add_sum_erase Finset.univ (fun j => f i j) (Finset.mem_univ i)).symm
    _ = (∑ i, f i i) + (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) := by
      rw [Finset.sum_add_distrib]

/-- Row-summable ordered off-diagonal bounds imply the aggregate cross-term
bound used in the martingale method.

Here `q i` is the nonnegative diagonal quadratic form of the `i`-th projection,
`cross i j` is the ordered real cross term, and `c i j` is a row-summable
coefficient matrix. -/
theorem crossTerm_sum_bound_of_ordered_rowSum {γ : ℝ} (hγle : γ ≤ 1)
    (q : ι → ℝ) (cross c : ι → ι → ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i)
    (hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCross : ∀ i j, j ∈ Finset.univ.erase i →
      -(1 - γ) * c i j * q i ≤ cross i j) :
    -(1 - γ) * (∑ i, q i) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j := by
  have hrowmul : ∀ i,
      -(1 - γ) * q i ≤
        ∑ j ∈ Finset.univ.erase i, -(1 - γ) * c i j * q i := by
    intro i
    have hnonneg : 0 ≤ 1 - γ := sub_nonneg.mpr hγle
    have hq : 0 ≤ q i := hq_nonneg i
    have hmul : (∑ j ∈ Finset.univ.erase i, c i j) * q i ≤ 1 * q i :=
      mul_le_mul_of_nonneg_right (hRow i) hq
    have hmul' : (1 - γ) * ((∑ j ∈ Finset.univ.erase i, c i j) * q i) ≤
        (1 - γ) * q i := by
      simpa [one_mul] using mul_le_mul_of_nonneg_left hmul hnonneg
    have hneg := neg_le_neg hmul'
    calc
      -(1 - γ) * q i = - ((1 - γ) * q i) := by ring
      _ ≤ - ((1 - γ) * ((∑ j ∈ Finset.univ.erase i, c i j) * q i)) := hneg
      _ = ∑ j ∈ Finset.univ.erase i, -(1 - γ) * c i j * q i := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
  calc
    -(1 - γ) * (∑ i, q i)
        = ∑ i, -(1 - γ) * q i := by
            simp [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, -(1 - γ) * c i j * q i := by
            exact Finset.sum_le_sum (fun i _ => hrowmul i)
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j := by
            refine Finset.sum_le_sum ?_
            intro i _
            refine Finset.sum_le_sum ?_
            intro j hj
            exact hCross i j hj

/-- If the ordered off-diagonal terms of a finite family of symmetric
projections satisfy a row-summable anti-commutator bound, then the sum satisfies
`H² ≥ γ H` as a quadratic form.

The hypothesis `hCross` is the ordered form of the martingale anti-commutator
estimate after taking real quadratic forms:
`Re ⟪P_i v, P_j v⟫ ≥ -(1 - γ) c_{ij} Re ⟪P_i v, v⟫` for `i ≠ j`.
The row bound `∑_{j ≠ i} c_{ij} ≤ 1` then gives the aggregate estimate. -/
theorem quadraticForm_sum_projections_of_ordered_rowSum {γ : ℝ} (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (c : ι → ι → ℝ)
    (hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCross : ∀ i j, j ∈ Finset.univ.erase i → ∀ v : E,
      -(1 - γ) * c i j * (⟪P i v, v⟫_ℂ).re ≤
        (⟪P i v, P j v⟫_ℂ).re) :
    ∀ v : E,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤
        (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := by
  intro v
  let q : ι → ℝ := fun i => (⟪P i v, v⟫_ℂ).re
  let cross : ι → ι → ℝ := fun i j => (⟪P i v, P j v⟫_ℂ).re
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i =>
    IsSymmetricProjection.re_inner_nonneg (hP i) v
  have hCrossSum : -(1 - γ) * (∑ i, q i) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j :=
    crossTerm_sum_bound_of_ordered_rowSum hγle q cross c hq_nonneg hRow
      (fun i j hj => hCross i j hj v)
  have hDiag : (∑ i, cross i i) = ∑ i, q i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact IsSymmetricProjection.re_inner_apply_apply_self (hP i) v
  have hSplit := sum_sum_eq_diag_add_offdiag (fun i j => cross i j)
  have hHq : (⟪(∑ i, P i) v, v⟫_ℂ).re = ∑ i, q i := by
    simpa [q] using re_inner_sum_apply_left P v
  have hHH : (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re =
      ∑ i, q i + ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j := by
    rw [re_inner_sum_apply_apply P v, hSplit, hDiag]
  calc
    γ * (⟪(∑ i, P i) v, v⟫_ℂ).re
        = γ * (∑ i, q i) := by rw [hHq]
    _ = (∑ i, q i) + (-(1 - γ) * (∑ i, q i)) := by ring
    _ ≤ (∑ i, q i) + ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j :=
        add_le_add le_rfl hCrossSum
    _ = (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := hHH.symm

end OffDiagonal

end ProjectionGeometry
