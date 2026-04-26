/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Projection-geometry lemmas for martingale estimates

This file collects small finite-dimensional Hilbert-space lemmas used by the
parent-Hamiltonian martingale method.  The main theorem is a purely algebraic
quadratic-form reduction for a finite sum of symmetric projections: if the
ordered off-diagonal terms satisfy a row-summable cross-term bound, then
`H = ∑ i, P i` satisfies `H² ≥ γ H` as a quadratic form.

The statements deliberately keep the MPS/Friedrichs-angle estimates as explicit
hypotheses.  They provide the reusable projection-geometry layer into which the
model-specific overlap and row-sum bounds can later be plugged.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a symmetric projection `P`, the diagonal term in `‖P v‖²` is its
quadratic form. -/
theorem re_inner_apply_apply_self {P : E →ₗ[𝕜] E} (hP : P.IsSymmetricProjection)
    (v : E) :
    RCLike.re (⟪P v, P v⟫_𝕜) = RCLike.re (⟪P v, v⟫_𝕜) := by
  have hidem : P (P v) = P v := by
    simpa [Module.End.mul_apply] using congrArg (fun T : E →ₗ[𝕜] E => T v)
      hP.isIdempotentElem.eq
  calc
    RCLike.re (⟪P v, P v⟫_𝕜) = RCLike.re (⟪P (P v), v⟫_𝕜) := by
      exact congrArg RCLike.re ((hP.isSymmetric (P v) v).symm)
    _ = RCLike.re (⟪P v, v⟫_𝕜) := by
      rw [hidem]

/-- A symmetric projection has nonnegative quadratic form. -/
theorem re_inner_nonneg {P : E →ₗ[𝕜] E} (hP : P.IsSymmetricProjection) (v : E) :
    0 ≤ RCLike.re (⟪P v, v⟫_𝕜) :=
  hP.isPositive.re_inner_nonneg_left v

end LinearMap.IsSymmetricProjection

namespace ProjectionGeometry

section InnerSums

variable {ι 𝕜 E : Type*} [Fintype ι]
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The quadratic form of a finite sum expands into the finite sum of quadratic
forms. -/
theorem re_inner_sum_apply_left (P : ι → E →ₗ[𝕜] E) (v : E) :
    RCLike.re (⟪(∑ i, P i) v, v⟫_𝕜) =
      ∑ i, RCLike.re (⟪P i v, v⟫_𝕜) := by
  simp only [LinearMap.sum_apply, sum_inner]
  exact map_sum (RCLike.re : 𝕜 →+ ℝ) (fun i => ⟪P i v, v⟫_𝕜) Finset.univ

/-- The norm-square quadratic form of a finite sum expands into all ordered
cross terms. -/
theorem re_inner_sum_apply_apply (P : ι → E →ₗ[𝕜] E) (v : E) :
    RCLike.re (⟪(∑ i, P i) v, (∑ i, P i) v⟫_𝕜) =
      ∑ i, ∑ j, RCLike.re (⟪P i v, P j v⟫_𝕜) := by
  simp only [LinearMap.sum_apply, sum_inner, inner_sum]
  rw [map_sum (RCLike.re : 𝕜 →+ ℝ)]
  simp_rw [map_sum (RCLike.re : 𝕜 →+ ℝ)]
  rw [Finset.sum_comm]

end InnerSums

section OffDiagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Split an ordered double sum into diagonal and off-diagonal parts. -/
theorem sum_sum_eq_diag_add_offdiag {M : Type*} [AddCommMonoid M] (f : ι → ι → M) :
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

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

private theorem indicator_row_sum_le_one_of_card_le (overlaps : ι → ι → Prop)
    [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i, ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (i : ι) :
    (∑ j ∈ Finset.univ.erase i,
      if overlaps i j then ((m : ℝ)⁻¹) else 0) ≤ 1 := by
  have hsum : (∑ j ∈ Finset.univ.erase i,
      if overlaps i j then ((m : ℝ)⁻¹) else 0) =
      (((Finset.univ.erase i).filter (fun j => overlaps i j)).card : ℝ) *
        ((m : ℝ)⁻¹) := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcard_le :
      (((Finset.univ.erase i).filter (fun j => overlaps i j)).card : ℝ) ≤
        (m : ℝ) := by
    exact_mod_cast hCard i
  have hinv_nonneg : 0 ≤ ((m : ℝ)⁻¹) := inv_nonneg.mpr hmpos.le
  have hmul := mul_le_mul_of_nonneg_right hcard_le hinv_nonneg
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  simpa [hmne] using hmul

/-- If the ordered off-diagonal terms of a finite family of symmetric
projections satisfy a row-summable cross-term bound, then the sum satisfies
`H² ≥ γ H` as a quadratic form.

The hypothesis `hCross` is the ordered form of the martingale overlap estimate
after taking real quadratic forms:
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
  let q : ι → ℝ := fun i => RCLike.re (⟪P i v, v⟫_ℂ)
  let cross : ι → ι → ℝ := fun i j => RCLike.re (⟪P i v, P j v⟫_ℂ)
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i => (hP i).re_inner_nonneg v
  have hCrossSum : -(1 - γ) * (∑ i, q i) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j :=
    crossTerm_sum_bound_of_ordered_rowSum hγle q cross c hq_nonneg hRow
      (fun i j hj => by simpa [q, cross] using hCross i j hj v)
  have hDiag : (∑ i, cross i i) = ∑ i, q i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (hP i).re_inner_apply_apply_self v
  have hSplit := sum_sum_eq_diag_add_offdiag (fun i j => cross i j)
  have hHq : (⟪(∑ i, P i) v, v⟫_ℂ).re = ∑ i, q i := by
    change RCLike.re (⟪(∑ i, P i) v, v⟫_ℂ) = ∑ i, q i
    simpa [q] using re_inner_sum_apply_left P v
  have hHH : (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re =
      ∑ i, q i + ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j := by
    change RCLike.re (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ) =
      ∑ i, q i + ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j
    rw [re_inner_sum_apply_apply P v, hSplit, hDiag]
  calc
    γ * (⟪(∑ i, P i) v, v⟫_ℂ).re
        = γ * (∑ i, q i) := by rw [hHq]
    _ = (∑ i, q i) + (-(1 - γ) * (∑ i, q i)) := by ring
    _ ≤ (∑ i, q i) + ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j :=
        add_le_add le_rfl hCrossSum
    _ = (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := hHH.symm

/-- Finite-overlap Friedrichs conditions for a family of symmetric projections.

Assume that each row has at most `m` interacting off-diagonal entries.  On an
interacting pair, a Friedrichs-angle estimate supplies the ordered bound with
coefficient `1 / m`; on a noninteracting pair, the ordered cross term is
nonnegative.  Then choosing coefficient `1 / m` on interacting pairs and `0`
on noninteracting pairs gives row sums at most one, so the abstract row-sum
reduction gives `H² ≥ γ H` as a quadratic form.

This is the abstract finite-range step: locality provides the cardinal bound
(for parent Hamiltonians, `m = 2 * (L - 1)`), while the analytic Friedrichs-angle
argument provides the interacting-pair estimate. -/
theorem quadraticForm_sum_projections_of_finite_overlap {γ : ℝ} (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (overlaps : ι → ι → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i, ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : E, 0 ≤ (⟪P i v, P j v⟫_ℂ).re)
    (hFriedrichs : ∀ i j, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : E,
        - (1 - γ) * ((m : ℝ)⁻¹) * (⟪P i v, v⟫_ℂ).re ≤
          (⟪P i v, P j v⟫_ℂ).re) :
    ∀ v : E,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤
        (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := by
  classical
  let c : ι → ι → ℝ := fun i j => if overlaps i j then ((m : ℝ)⁻¹) else 0
  have hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1 := by
    intro i
    simpa [c] using indicator_row_sum_le_one_of_card_le overlaps hm hCard i
  have hCross : ∀ i j, j ∈ Finset.univ.erase i → ∀ v : E,
      -(1 - γ) * c i j * (⟪P i v, v⟫_ℂ).re ≤
        (⟪P i v, P j v⟫_ℂ).re := by
    intro i j hij v
    by_cases hoverlap : overlaps i j
    · simpa [c, hoverlap] using hFriedrichs i j hij hoverlap v
    · simpa [c, hoverlap] using hDisjoint i j hij hoverlap v
  exact quadraticForm_sum_projections_of_ordered_rowSum hγle P hP c hRow hCross

end OffDiagonal

end ProjectionGeometry
