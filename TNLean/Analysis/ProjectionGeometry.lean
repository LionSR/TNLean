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
`H = ∑ i, P i` satisfies `H² ≥ γ H` as a quadratic form.  The file also records
that commuting symmetric projections have nonnegative ordered cross terms, and
converts norm-compression estimates for products of projections into the ordered
cross-term bounds used by the row-sum reduction.

The statements deliberately keep the MPS-specific overlap estimates as explicit
hypotheses.  They provide the reusable projection-geometry layer into which the
model-specific overlap and row-sum bounds are inserted.
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
  rw [show ⟪P v, P v⟫_𝕜 = ⟪P (P v), v⟫_𝕜 from (hP.isSymmetric (P v) v).symm, hidem]

/-- A norm bound on the compressed product of two projections gives the ordered
cross-term lower bound.

For a symmetric projection `P`, the ordered cross term satisfies
`Re ⟪P v, Q v⟫ = Re ⟪P v, P (Q v)⟫`. Hence Cauchy--Schwarz shows that a
bound `‖P (Q v)‖ ≤ c ‖P v‖` implies
`Re ⟪P v, Q v⟫ ≥ -c Re ⟪P v, v⟫`. This is the
projection-geometry conversion from a principal-angle norm estimate to the
ordered quadratic-form estimate used by the martingale row-sum argument.

The norm-compression hypothesis is directional. If it holds for every `v`, then
`P v = 0` forces `P (Q v) = 0`; equivalently, `Q` maps `ker P` into `ker P`.
Thus a principal-angle estimate used here must supply this compressed-product
bound, not only a qualitative lower bound on a non-zero angle between the two
projected subspaces. -/
theorem re_inner_apply_apply_ge_neg_of_norm_apply_le {P Q : E →ₗ[𝕜] E}
    (hP : P.IsSymmetricProjection) {c : ℝ}
    (hNorm : ∀ v : E, ‖P (Q v)‖ ≤ c * ‖P v‖) (v : E) :
    -c * RCLike.re (⟪P v, v⟫_𝕜) ≤ RCLike.re (⟪P v, Q v⟫_𝕜) := by
  have hPidem : P (P v) = P v := by
    simpa [Module.End.mul_apply] using congrArg (fun T : E →ₗ[𝕜] E => T v)
      hP.isIdempotentElem.eq
  have hcompress : ⟪P v, Q v⟫_𝕜 = ⟪P v, P (Q v)⟫_𝕜 := by
    calc
      ⟪P v, Q v⟫_𝕜 = ⟪P (P v), Q v⟫_𝕜 := by rw [hPidem]
      _ = ⟪P v, P (Q v)⟫_𝕜 := hP.isSymmetric (P v) (Q v)
  have hdiag : RCLike.re (⟪P v, v⟫_𝕜) = ‖P v‖ ^ 2 := by
    rw [← hP.re_inner_apply_apply_self v, inner_self_eq_norm_sq]
  have hre_lower : -‖⟪P v, P (Q v)⟫_𝕜‖ ≤ RCLike.re (⟪P v, P (Q v)⟫_𝕜) := by
    have h := RCLike.re_le_norm (-(⟪P v, P (Q v)⟫_𝕜))
    have h' : -RCLike.re (⟪P v, P (Q v)⟫_𝕜) ≤ ‖⟪P v, P (Q v)⟫_𝕜‖ := by
      simpa using h
    exact neg_le.mp h'
  have hnorm_inner : ‖⟪P v, P (Q v)⟫_𝕜‖ ≤ c * ‖P v‖ ^ 2 := by
    calc
      ‖⟪P v, P (Q v)⟫_𝕜‖ ≤ ‖P v‖ * ‖P (Q v)‖ := norm_inner_le_norm (P v) (P (Q v))
      _ ≤ ‖P v‖ * (c * ‖P v‖) :=
          mul_le_mul_of_nonneg_left (hNorm v) (norm_nonneg (P v))
      _ = c * ‖P v‖ ^ 2 := by ring
  calc
    -c * RCLike.re (⟪P v, v⟫_𝕜) = -(c * ‖P v‖ ^ 2) := by rw [hdiag]; ring
    _ ≤ -‖⟪P v, P (Q v)⟫_𝕜‖ := neg_le_neg hnorm_inner
    _ ≤ RCLike.re (⟪P v, P (Q v)⟫_𝕜) := hre_lower
    _ = RCLike.re (⟪P v, Q v⟫_𝕜) := by rw [← hcompress]

/-- Commuting symmetric projections have nonnegative ordered cross terms.

If `P` and `Q` are symmetric projections that commute pointwise, then
`0 ≤ Re ⟪P v, Q v⟫` for every vector `v`. -/
theorem re_inner_apply_apply_nonneg_of_commute {P Q : E →ₗ[𝕜] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (hcomm : ∀ v : E, P (Q v) = Q (P v)) (v : E) :
    0 ≤ RCLike.re (⟪P v, Q v⟫_𝕜) := by
  have hQidem : Q (Q (P v)) = Q (P v) := by
    simpa [Module.End.mul_apply] using congrArg (fun T : E →ₗ[𝕜] E => T (P v))
      hQ.isIdempotentElem.eq
  have hsym₁ : ⟪P v, Q v⟫_𝕜 = ⟪Q (P v), v⟫_𝕜 := (hQ.isSymmetric (P v) v).symm
  have hsym₂ : ⟪Q (P v), v⟫_𝕜 = ⟪Q (P v), Q v⟫_𝕜 := by
    calc
      ⟪Q (P v), v⟫_𝕜 = ⟪Q (Q (P v)), v⟫_𝕜 := by rw [hQidem]
      _ = ⟪Q (P v), Q v⟫_𝕜 := hQ.isSymmetric (Q (P v)) v
  calc
    0 ≤ RCLike.re (⟪P (Q v), Q v⟫_𝕜) :=
      hP.isPositive.re_inner_nonneg_left (Q v)
    _ = RCLike.re (⟪P v, Q v⟫_𝕜) := by
      rw [hsym₁, hsym₂, hcomm v]

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

/-- If a finite sum of symmetric projections annihilates a vector, then each
projection in the sum annihilates that vector. -/
theorem apply_eq_zero_of_sum_apply_eq_zero
    (P : ι → E →ₗ[𝕜] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    {v : E} (hsum : (∑ i, P i) v = 0) (i : ι) :
    P i v = 0 := by
  have hsum_re :
      (∑ i, RCLike.re (⟪P i v, v⟫_𝕜)) = 0 := by
    rw [← re_inner_sum_apply_left P v, hsum]
    simp
  have hterm_zero :
      (fun i => RCLike.re (⟪P i v, v⟫_𝕜)) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun i => (hP i).isPositive.re_inner_nonneg_left v)).mp hsum_re
  have hterm : RCLike.re (⟪P i v, v⟫_𝕜) = 0 := by
    simpa using congrFun hterm_zero i
  have hdiag : RCLike.re (⟪P i v, v⟫_𝕜) = ‖P i v‖ ^ 2 := by
    rw [← (hP i).re_inner_apply_apply_self v, inner_self_eq_norm_sq]
  have hnorm_sq : ‖P i v‖ ^ 2 = 0 := by
    rwa [← hdiag]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq)

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

/-- Anticommutator bounds imply the aggregate off-diagonal bound used in the
martingale method, once the corresponding coefficient-weighted diagonal sum is
controlled.

Here `q i` is the nonnegative diagonal quadratic form of the `i`-th projection,
`cross i j` is the ordered real cross term, and `c i j` is a coefficient matrix
whose weighted diagonal contribution is at most twice the total diagonal form.
The hypothesis `hAnti` is the real-valued form of the source martingale condition
`P_i P_j + P_j P_i ≥ -(1 - γ)c_{ij}(P_i + P_j)`, after evaluating on a vector. -/
theorem crossTerm_sum_bound_of_anticommutator_coeffSum {γ : ℝ} (hγle : γ ≤ 1)
    (q : ι → ℝ) (cross c : ι → ι → ℝ)
    (hCoeff : (∑ i, ∑ j ∈ Finset.univ.erase i, c i j * (q i + q j)) ≤
      2 * ∑ i, q i)
    (hCrossSymm : ∀ i j, cross j i = cross i j)
    (hAnti : ∀ i j, j ∈ Finset.univ.erase i →
      -(1 - γ) * c i j * (q i + q j) ≤ cross i j + cross j i) :
    -(1 - γ) * (∑ i, q i) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j := by
  let coeffSum : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, c i j * (q i + q j)
  let crossSum : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j
  have hnonneg : 0 ≤ 1 - γ := sub_nonneg.mpr hγle
  have hCoeffNeg :
      -(1 - γ) * (2 * ∑ i, q i) ≤ -(1 - γ) * coeffSum := by
    have hmul : (1 - γ) * coeffSum ≤ (1 - γ) * (2 * ∑ i, q i) :=
      mul_le_mul_of_nonneg_left hCoeff hnonneg
    calc
      -(1 - γ) * (2 * ∑ i, q i) = -((1 - γ) * (2 * ∑ i, q i)) := by ring
      _ ≤ -((1 - γ) * coeffSum) := neg_le_neg hmul
      _ = -(1 - γ) * coeffSum := by ring
  have hAntiSum : -(1 - γ) * coeffSum ≤ 2 * crossSum := by
    calc
      -(1 - γ) * coeffSum =
          ∑ i, ∑ j ∈ Finset.univ.erase i, -(1 - γ) * c i j * (q i + q j) := by
            change -(1 - γ) *
                (∑ i, ∑ j ∈ Finset.univ.erase i, c i j * (q i + q j)) =
              ∑ i, ∑ j ∈ Finset.univ.erase i, -(1 - γ) * c i j * (q i + q j)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (cross i j + cross j i) := by
            refine Finset.sum_le_sum ?_
            intro i _
            refine Finset.sum_le_sum ?_
            intro j hj
            exact hAnti i j hj
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, (cross i j + cross i j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [hCrossSymm i j]
      _ = 2 * crossSum := by
            simp [crossSum, two_mul, Finset.sum_add_distrib]
  have htwice :
      2 * (-(1 - γ) * (∑ i, q i)) ≤ 2 * crossSum := by
    calc
      2 * (-(1 - γ) * (∑ i, q i)) = -(1 - γ) * (2 * ∑ i, q i) := by ring
      _ ≤ -(1 - γ) * coeffSum := hCoeffNeg
      _ ≤ 2 * crossSum := hAntiSum
  nlinarith [htwice]

/-- Row- and column-summable anticommutator bounds imply the aggregate
off-diagonal bound used in the martingale method.

This is the row-sum form of the source martingale estimate. The column condition
is automatic in the usual symmetric-coefficient case, but it is stated separately
so the lemma does not require a symmetry assumption on `c`. -/
theorem crossTerm_sum_bound_of_anticommutator_rowCol {γ : ℝ} (hγle : γ ≤ 1)
    (q : ι → ℝ) (cross c : ι → ι → ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i)
    (hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCol : ∀ j, (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1)
    (hCrossSymm : ∀ i j, cross j i = cross i j)
    (hAnti : ∀ i j, j ∈ Finset.univ.erase i →
      -(1 - γ) * c i j * (q i + q j) ≤ cross i j + cross j i) :
    -(1 - γ) * (∑ i, q i) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j := by
  refine crossTerm_sum_bound_of_anticommutator_coeffSum hγle q cross c ?_
    hCrossSymm hAnti
  let rowPart : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, c i j * q i
  let colPart : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, c i j * q j
  have hRowWeighted : rowPart ≤ ∑ i, q i := by
    refine Finset.sum_le_sum ?_
    intro i _
    calc
      (∑ j ∈ Finset.univ.erase i, c i j * q i) =
          (∑ j ∈ Finset.univ.erase i, c i j) * q i := by
            rw [← Finset.sum_mul]
      _ ≤ 1 * q i := mul_le_mul_of_nonneg_right (hRow i) (hq_nonneg i)
      _ = q i := by ring
  have hColWeighted : (∑ j, ∑ i ∈ Finset.univ.erase j, c i j * q j) ≤ ∑ j, q j := by
    refine Finset.sum_le_sum ?_
    intro j _
    calc
      (∑ i ∈ Finset.univ.erase j, c i j * q j) =
          (∑ i ∈ Finset.univ.erase j, c i j) * q j := by
            rw [← Finset.sum_mul]
      _ ≤ 1 * q j := mul_le_mul_of_nonneg_right (hCol j) (hq_nonneg j)
      _ = q j := by ring
  have hColSwap : colPart = ∑ j, ∑ i ∈ Finset.univ.erase j, c i j * q j := by
    let f : ι → ι → ℝ := fun i j => c i j * q j
    have hsplit₁ := sum_sum_eq_diag_add_offdiag (fun i j => f i j)
    have hsplit₂ := sum_sum_eq_diag_add_offdiag (fun j i => f i j)
    have htotal : (∑ i, ∑ j, f i j) = ∑ j, ∑ i, f i j := by
      rw [Finset.sum_comm]
    have hadd :
        (∑ i, f i i) + (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
          (∑ i, f i i) + (∑ j, ∑ i ∈ Finset.univ.erase j, f i j) := by
      calc
        (∑ i, f i i) + (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
            ∑ i, ∑ j, f i j := hsplit₁.symm
        _ = ∑ j, ∑ i, f i j := htotal
        _ = (∑ j, f j j) + (∑ j, ∑ i ∈ Finset.univ.erase j, f i j) := hsplit₂
        _ = (∑ i, f i i) + (∑ j, ∑ i ∈ Finset.univ.erase j, f i j) := rfl
    change (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
      ∑ j, ∑ i ∈ Finset.univ.erase j, f i j
    exact add_left_cancel hadd
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i, c i j * (q i + q j)) =
        rowPart + colPart := by
          simp [rowPart, colPart, mul_add, Finset.sum_add_distrib]
    _ ≤ (∑ i, q i) + ∑ j, q j := add_le_add hRowWeighted (by
          rw [hColSwap]
          exact hColWeighted)
    _ = 2 * ∑ i, q i := by ring

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
  have hq_nonneg : ∀ i, 0 ≤ q i :=
    fun i => (hP i).isPositive.re_inner_nonneg_left v
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

/-- If the anticommutator forms of a finite family of symmetric projections
satisfy row- and column-summable bounds, then the sum satisfies
`H² ≥ γ H` as a quadratic form.

This is the source martingale condition in quadratic-form language:
`P_i P_j + P_j P_i ≥ -(1 - γ)c_{ij}(P_i + P_j)` on off-diagonal pairs, together
with row and column sums bounded by one. -/
theorem quadraticForm_sum_projections_of_anticommutator_rowCol {γ : ℝ} (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (c : ι → ι → ℝ)
    (hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCol : ∀ j, (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1)
    (hAnti : ∀ i j, j ∈ Finset.univ.erase i → ∀ v : E,
      -(1 - γ) * c i j *
          ((⟪P i v, v⟫_ℂ).re + (⟪P j v, v⟫_ℂ).re) ≤
        (⟪P i v, P j v⟫_ℂ).re + (⟪P j v, P i v⟫_ℂ).re) :
    ∀ v : E,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤
        (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := by
  intro v
  let q : ι → ℝ := fun i => RCLike.re (⟪P i v, v⟫_ℂ)
  let cross : ι → ι → ℝ := fun i j => RCLike.re (⟪P i v, P j v⟫_ℂ)
  have hq_nonneg : ∀ i, 0 ≤ q i :=
    fun i => (hP i).isPositive.re_inner_nonneg_left v
  have hCrossSymm : ∀ i j, cross j i = cross i j := by
    intro i j
    simpa [cross] using (inner_re_symm (𝕜 := ℂ) (P i v) (P j v)).symm
  have hCrossSum : -(1 - γ) * (∑ i, q i) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, cross i j :=
    crossTerm_sum_bound_of_anticommutator_rowCol hγle q cross c hq_nonneg
      hRow hCol hCrossSymm (fun i j hj => by
        simpa [q, cross] using hAnti i j hj v)
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

/-- Finite-overlap anticommutator reduction for symmetric projections.

Choose the coefficient \(c_{ij}=1/m\) on interacting off-diagonal pairs and
\(c_{ij}=0\) otherwise. Row and column cardinality bounds by \(m\) make these
coefficients summable. If noninteracting pairs have non-negative
anticommutator quadratic form, and interacting pairs satisfy the source
anticommutator estimate with coefficient \(1/m\), then the sum satisfies
\(H² ≥ γH\) as a quadratic form. -/
theorem quadraticForm_sum_projections_of_finite_overlap_anticommutator
    {γ : ℝ} (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (overlaps : ι → ι → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hRowCard : ∀ i,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hColCard : ∀ j,
      ((Finset.univ.erase j).filter (fun i => overlaps i j)).card ≤ m)
    (hDisjointAnti : ∀ i j, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : E, 0 ≤
        (⟪P i v, P j v⟫_ℂ).re + (⟪P j v, P i v⟫_ℂ).re)
    (hAnti : ∀ i j, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : E,
        - (1 - γ) * ((m : ℝ)⁻¹) *
            ((⟪P i v, v⟫_ℂ).re + (⟪P j v, v⟫_ℂ).re) ≤
          (⟪P i v, P j v⟫_ℂ).re + (⟪P j v, P i v⟫_ℂ).re) :
    ∀ v : E,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤
        (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := by
  classical
  let c : ι → ι → ℝ := fun i j => if overlaps i j then ((m : ℝ)⁻¹) else 0
  have hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1 := by
    intro i
    simpa [c] using indicator_row_sum_le_one_of_card_le overlaps hm hRowCard i
  have hCol : ∀ j, (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1 := by
    intro j
    simpa [c] using
      indicator_row_sum_le_one_of_card_le (fun j i => overlaps i j) hm hColCard j
  have hAntiAll : ∀ i j, j ∈ Finset.univ.erase i → ∀ v : E,
      -(1 - γ) * c i j *
          ((⟪P i v, v⟫_ℂ).re + (⟪P j v, v⟫_ℂ).re) ≤
        (⟪P i v, P j v⟫_ℂ).re + (⟪P j v, P i v⟫_ℂ).re := by
    intro i j hij v
    by_cases hoverlap : overlaps i j
    · simpa [c, hoverlap] using hAnti i j hij hoverlap v
    · simpa [c, hoverlap] using hDisjointAnti i j hij hoverlap v
  exact quadraticForm_sum_projections_of_anticommutator_rowCol hγle P hP c
    hRow hCol hAntiAll

/-- Finite-overlap ordered cross-term conditions for a family of symmetric
projections.

Assume that each row has at most `m` interacting off-diagonal entries.  On an
interacting pair, an ordered cross-term estimate supplies the bound with
coefficient `1 / m`; on a noninteracting pair, the ordered cross term is
nonnegative.  Then choosing coefficient `1 / m` on interacting pairs and `0`
on noninteracting pairs gives row sums at most one, so the abstract row-sum
reduction gives `H² ≥ γ H` as a quadratic form.

This is the abstract finite-range step: locality provides the cardinal bound
(for parent Hamiltonians, `m = 2 * (L - 1)`), while the analytic part provides
the interacting-pair estimate. -/
theorem quadraticForm_sum_projections_of_finite_overlap {γ : ℝ} (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (overlaps : ι → ι → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i, ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : E, 0 ≤ (⟪P i v, P j v⟫_ℂ).re)
    (hCrossTerm : ∀ i j, j ∈ Finset.univ.erase i → overlaps i j →
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
    · simpa [c, hoverlap] using hCrossTerm i j hij hoverlap v
    · simpa [c, hoverlap] using hDisjoint i j hij hoverlap v
  exact quadraticForm_sum_projections_of_ordered_rowSum hγle P hP c hRow hCross

/-- Finite-overlap row-sum reduction from a norm-compression bound.

For symmetric projections, a principal-angle style estimate
`‖P_i (P_j v)‖ ≤ (1 - γ) m⁻¹ ‖P_i v‖` on every interacting pair implies the
ordered cross-term estimate used by
`quadraticForm_sum_projections_of_finite_overlap`.  Thus the same finite-overlap
quadratic-form conclusion follows from this norm formulation, together with the
usual row-cardinality and noninteraction nonnegativity hypotheses. -/
theorem quadraticForm_sum_projections_of_finite_overlap_norm_bound {γ : ℝ} (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (overlaps : ι → ι → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i, ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : E, 0 ≤ (⟪P i v, P j v⟫_ℂ).re)
    (hOverlapNorm : ∀ i j, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : E,
        ‖P i (P j v)‖ ≤ ((1 - γ) * ((m : ℝ)⁻¹)) * ‖P i v‖) :
    ∀ v : E,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤
        (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := by
  refine quadraticForm_sum_projections_of_finite_overlap hγle P hP overlaps hm hCard
    hDisjoint ?_
  intro i j hij hoverlap v
  have hraw :
      -((1 - γ) * ((m : ℝ)⁻¹)) * (⟪P i v, v⟫_ℂ).re ≤
        (⟪P i v, P j v⟫_ℂ).re :=
    (hP i).re_inner_apply_apply_ge_neg_of_norm_apply_le
      (hOverlapNorm i j hij hoverlap) v
  convert hraw using 1
  ring

/-- Finite-overlap row-sum reduction from an explicit overlap-compression
coefficient.

If interacting pairs satisfy `‖P_i (P_j v)‖ ≤ η ‖P_i v‖`, and the coefficient
`η` is no larger than `(1 - γ) / m`, then the usual finite-overlap
norm-compression theorem applies.  This form separates the analytic principal-angle
constant from the gap parameter: it suffices to choose a positive `γ` satisfying
`η ≤ (1 - γ) / m` whenever a later bound gives `η < 1 / m`. -/
theorem quadraticForm_sum_projections_of_finite_overlap_norm_bound_of_le
    {γ η : ℝ} (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (overlaps : ι → ι → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i, ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : E, 0 ≤ (⟪P i v, P j v⟫_ℂ).re)
    (hηle : η ≤ (1 - γ) * ((m : ℝ)⁻¹))
    (hOverlapNorm : ∀ i j, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : E, ‖P i (P j v)‖ ≤ η * ‖P i v‖) :
    ∀ v : E,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤
        (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := by
  refine quadraticForm_sum_projections_of_finite_overlap_norm_bound hγle P hP
    overlaps hm hCard hDisjoint ?_
  intro i j hij hoverlap v
  calc
    ‖P i (P j v)‖ ≤ η * ‖P i v‖ := hOverlapNorm i j hij hoverlap v
    _ ≤ ((1 - γ) * ((m : ℝ)⁻¹)) * ‖P i v‖ :=
      mul_le_mul_of_nonneg_right hηle (norm_nonneg (P i v))

/-- Finite-overlap row-sum reduction from a strict norm-compression coefficient.

If interacting pairs satisfy `‖P_i (P_j v)‖ ≤ η ‖P_i v‖`, with
`0 ≤ η` and `η * m < 1`, then the finite sum of symmetric projections satisfies
`H² ≥ (1 - η * m)H` as a quadratic form.  Thus a compression coefficient
strictly below the reciprocal of the overlap degree gives a positive
martingale constant. -/
theorem quadraticForm_sum_projections_of_finite_overlap_norm_bound_of_lt
    {η : ℝ} (hηnonneg : 0 ≤ η)
    (P : ι → E →ₗ[ℂ] E) (hP : ∀ i, (P i).IsSymmetricProjection)
    (overlaps : ι → ι → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hηlt : η * (m : ℝ) < 1)
    (hCard : ∀ i, ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : E, 0 ≤ (⟪P i v, P j v⟫_ℂ).re)
    (hOverlapNorm : ∀ i j, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : E, ‖P i (P j v)‖ ≤ η * ‖P i v‖) :
    0 < 1 - η * (m : ℝ) ∧
    ∀ v : E,
      (1 - η * (m : ℝ)) * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤
        (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re := by
  have hmRpos : 0 < (m : ℝ) := by
    exact_mod_cast hm
  have hγpos : 0 < 1 - η * (m : ℝ) := by
    linarith
  refine ⟨hγpos, ?_⟩
  have hγle : 1 - η * (m : ℝ) ≤ 1 := by
    have hmul_nonneg : 0 ≤ η * (m : ℝ) :=
      mul_nonneg hηnonneg hmRpos.le
    linarith
  have hηle : η ≤ (1 - (1 - η * (m : ℝ))) * ((m : ℝ)⁻¹) := by
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hηeq : η = (1 - (1 - η * (m : ℝ))) * ((m : ℝ)⁻¹) := by
      calc
        η = η * ((m : ℝ) * ((m : ℝ)⁻¹)) := by
          rw [mul_inv_cancel₀ hmne, mul_one]
        _ = (1 - (1 - η * (m : ℝ))) * ((m : ℝ)⁻¹) := by ring
    exact le_of_eq hηeq
  exact quadraticForm_sum_projections_of_finite_overlap_norm_bound_of_le hγle
    P hP overlaps hm hCard hDisjoint hηle hOverlapNorm

end OffDiagonal

end ProjectionGeometry
