/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import QICLean.Channel.Basic
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import Mathlib.Topology.Algebra.AffineSubspace
import QICLean.Analysis.FunctionalCalculus.SqrtHolder
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import QICLean.Analysis.Optimization.HermitianMatrixCone

/-!
# Dual positive metrics for MPU interval isometries

For a positive definite matrix on an `r`-dimensional bond space, the dual
metric is its inverse divided by `r`. This is the algebraic normalization
following determinant stationarity in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The existence of the determinant maximizer and the circuit construction
are separate assertions; neither is assumed to have been formalized here.

It also contains the following results.

* `MPUCircuit.exists_posDef_dualGramMetric_on_affineSubspace`: determinant balancing of affine cap
  Grams.
-/

open Matrix
open scoped ComplexOrder

namespace MPUCircuit

section BalancedGramMetrics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Real affine combinations of Hermitian cap Grams remain Hermitian.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isHermitian_of_mem_real_affineSpan {S : Set (Matrix ι ι ℂ)}
    (hS : ∀ X ∈ S, X.IsHermitian) {X : Matrix ι ι ℂ}
    (hX : X ∈ affineSpan ℝ S) : X.IsHermitian := by
  refine affineSpan_induction hX hS ?_
  intro c u v w hu hv hw
  change (c • (u - v) + w).IsHermitian
  exact ((hu.sub hv).smul (by simp [IsSelfAdjoint])).add hw

omit [DecidableEq ι] in
/-- A trace normalization on physical cap Grams extends to their full real
affine hull, including combinations with negative coefficients.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem trace_mul_eq_of_mem_real_affineSpan {S : Set (Matrix ι ι ℂ)}
    (Q : Matrix ι ι ℂ) (z : ℂ) (hS : ∀ X ∈ S, (X * Q).trace = z)
    {X : Matrix ι ι ℂ} (hX : X ∈ affineSpan ℝ S) : (X * Q).trace = z := by
  refine affineSpan_induction hX hS ?_
  intro c u v w hu hv hw
  change ((c • (u - v) + w) * Q).trace = z
  simp [Matrix.add_mul, Matrix.sub_mul, hu, hv, hw]

/-- The positive dual metric is the inverse divided by the bond dimension.
Source: the determinant normalization in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def dualGramMetric (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Fintype.card ι : ℝ)⁻¹ • P⁻¹

/-- The dual metric of a positive definite matrix is positive definite
on a nonempty bond space. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem dualGramMetric_posDef [Nonempty ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    (dualGramMetric P).PosDef := by
  exact hP.inv.smul (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))

/-- Determinant stationarity makes the dual metric normalized on every
affine displacement from the maximizing matrix. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem trace_mul_dualGramMetric_eq_one [Nonempty ι]
    {P X : Matrix ι ι ℂ} (hP : P.PosDef)
    (hstationary : (P⁻¹ * (X - P)).trace = 0) :
    (X * dualGramMetric P).trace = 1 := by
  have hdet : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hP.isUnit
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul _ hdet,
    Matrix.trace_one, sub_eq_zero] at hstationary
  rw [dualGramMetric, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_comm,
    hstationary]
  simp

/-- The two balanced metrics multiply to the inverse dimension times the
identity. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem dualGramMetric_mul {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    dualGramMetric P * P = (Fintype.card ι : ℝ)⁻¹ • (1 : Matrix ι ι ℂ) := by
  rw [dualGramMetric, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ (P.isUnit_iff_isUnit_det.mp hP.isUnit)]

/-- Reversing the order gives the same balanced product. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem mul_dualGramMetric {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    P * dualGramMetric P = (Fintype.card ι : ℝ)⁻¹ • (1 : Matrix ι ι ℂ) := by
  rw [dualGramMetric, Matrix.mul_smul,
    Matrix.mul_nonsing_inv _ (P.isUnit_iff_isUnit_det.mp hP.isUnit)]

/-- Inverting the dual metric removes its reciprocal dimension factor.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem dualGramMetric_inv [Nonempty ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    (dualGramMetric P)⁻¹ = (Fintype.card ι : ℝ) • P := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, mul_dualGramMetric hP, smul_smul]
  simp

/-- The inverse-metric trace is the square of the bond dimension. Its
square root is the norm of the contraction used in the interval merger.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem trace_dualGramMetric_inv_mul_inv [Nonempty ι]
    {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ((dualGramMetric P)⁻¹ * P⁻¹).trace = (Fintype.card ι : ℂ) ^ 2 := by
  rw [dualGramMetric_inv hP, Matrix.smul_mul,
    Matrix.mul_nonsing_inv _ (P.isUnit_iff_isUnit_det.mp hP.isUnit),
    Matrix.trace_smul, Matrix.trace_one]
  simp [pow_two, Complex.real_smul]

end BalancedGramMetrics

section AffineGramBalancing

/-!
## Determinant balancing of affine cap Grams

A trace-normalized real affine space of Hermitian matrices containing a
positive-definite matrix admits a positive-definite determinant maximizer.
Its inverse divided by the dimension normalizes every matrix in that affine
space. The associated inverse-metric trace is the square of the dimension.

This is the determinant-balancing lemma of Section 5 in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The formal statement below
concerns a single affine Gram space. Realizing the compatible interval maps
as a complete quantum circuit is a further statement.
-/

/-- Determinant maximization produces positive balanced metrics on a real
affine space of Hermitian cap Grams. The metric normalizes the entire affine
space, rather than only its positive-semidefinite part.

Source: Section 5, "The determinant maximizer and its dual metric", in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_posDef_dualGramMetric_on_affineSubspace
    {D : ℕ} [Nonempty (Fin D)]
    (C : AffineSubspace ℝ (Matrix (Fin D) (Fin D) ℂ))
    (hHerm : ∀ X ∈ C, X.IsHermitian)
    {Q₀ : Matrix (Fin D) (Fin D) ℂ} (hQ₀ : Q₀.PosDef)
    (hnorm : ∀ X ∈ C, (X * Q₀).trace = 1)
    (hPD : ∃ X ∈ C, X.PosDef) :
    ∃ P ∈ C, P.PosDef ∧ (dualGramMetric P).PosDef ∧
      (∀ X ∈ C, (X * dualGramMetric P).trace = 1) ∧
      ((dualGramMetric P)⁻¹ * P⁻¹).trace = (D : ℂ) ^ 2 := by
  obtain ⟨P, hPC, hP, hmax⟩ :=
    Matrix.exists_posDef_det_re_max_of_trace_mul_eq_one C hQ₀ hnorm hPD
  refine ⟨P, hPC, hP, dualGramMetric_posDef hP, ?_, ?_⟩
  · intro X hXC
    apply trace_mul_dualGramMetric_eq_one hP
    exact hP.trace_nonsing_inv_mul_sub_eq_zero_of_isMaxOn_det C hPC hHerm
      (isMaxOn_iff.mpr (fun Y hY ↦ hmax Y hY.1 hY.2)) X hXC
  · simpa using trace_dualGramMetric_inv_mul_inv hP

end AffineGramBalancing

end MPUCircuit
