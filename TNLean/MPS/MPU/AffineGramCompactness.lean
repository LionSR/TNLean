/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Basic
import QICLean.Analysis.MatrixSqrt
import Mathlib.Topology.Algebra.AffineSubspace

/-!
# Compact affine Gram slices

The determinant normalization of finite matrix-product unitaries uses a real
affine space of cap Grams with a positive-definite trace normalizer. Its
positive-semidefinite part is compact, and any determinant maximum is positive
definite when that part contains a positive-definite point.

This module formalizes those two steps from Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. It reuses QICLean's density-matrix
compactness theorem through an invertible square-root congruence. The Hermitian
condition on the surrounding affine space is unnecessary for these steps,
since the matrices being maximized over are positive semidefinite.

The determinant stationarity identity and the resulting MPU circuit theorem
are not established in this module.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {D : ℕ}

private theorem sqrt_congruence_mem_densityMatrices_iff
    {Q P : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosDef) :
    CFC.sqrt Q * P * CFC.sqrt Q ∈ densityMatrices D ↔
      P.PosSemidef ∧ (P * Q).trace = 1 := by
  have hSstar : star (CFC.sqrt Q) = CFC.sqrt Q :=
    Matrix.conjTranspose_cfc_sqrt Q
  have hSunit : IsUnit (CFC.sqrt Q) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hQ.isUnit_det_cfc_sqrt
  have hPSD := Matrix.IsUnit.posSemidef_star_left_conjugate_iff (x := P) hSunit
  rw [hSstar] at hPSD
  have htrace : (CFC.sqrt Q * P * CFC.sqrt Q).trace = (P * Q).trace := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg,
      Matrix.trace_mul_comm]
  simp only [mem_densityMatrices, hPSD, htrace]


/-- Positive-semidefinite matrices normalized by a fixed positive-definite
trace pairing form a compact set. The proof transports QICLean's compact
set of density matrices by the inverse square-root congruence.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"The determinant maximizer and its dual metric". -/
theorem isCompact_setOf_posSemidef_trace_mul_eq_one
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosDef) :
    IsCompact {P : Matrix (Fin D) (Fin D) ℂ |
      P.PosSemidef ∧ (P * Q).trace = 1} := by
  let S := CFC.sqrt Q
  have hSdet : IsUnit S.det := hQ.isUnit_det_cfc_sqrt
  have hset : {P : Matrix (Fin D) (Fin D) ℂ |
      P.PosSemidef ∧ (P * Q).trace = 1} =
      (fun X ↦ S⁻¹ * X * S⁻¹) '' densityMatrices D := by
    ext P
    constructor
    · intro hP
      refine ⟨S * P * S, sqrt_congruence_mem_densityMatrices_iff hQ |>.2 hP, ?_⟩
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSdet,
        Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right S P hSdet]
    · rintro ⟨X, hX, rfl⟩
      apply (sqrt_congruence_mem_densityMatrices_iff hQ).1
      change S * (S⁻¹ * X * S⁻¹) * S ∈ densityMatrices D
      simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet,
        Matrix.one_mul, Matrix.nonsing_inv_mul_cancel_right S X hSdet] using hX
  rw [hset]
  exact densityMatrices_isCompact.image
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

/-- The positive-semidefinite part of a real affine matrix subspace is compact
when a fixed positive-definite matrix normalizes its trace pairing.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"The determinant maximizer and its dual metric". -/
theorem isCompact_affineSubspace_inter_posSemidef
    (C : AffineSubspace ℝ (Matrix (Fin D) (Fin D) ℂ))
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosDef)
    (hnorm : ∀ P ∈ C, (P * Q).trace = 1) :
    IsCompact ((C : Set (Matrix (Fin D) (Fin D) ℂ)) ∩ {P | P.PosSemidef}) := by
  have hC : IsClosed (C : Set (Matrix (Fin D) (Fin D) ℂ)) :=
    C.isClosed_direction_iff.mp C.direction.closed_of_finiteDimensional
  exact (isCompact_setOf_posSemidef_trace_mul_eq_one hQ).of_isClosed_subset
    (hC.inter Matrix.posSemidef_is_closed) fun P hP ↦ ⟨hP.2, hnorm P hP.1⟩

/-- A positive-semidefinite maximizer of the real determinant is positive
definite if its comparison set contains a positive-definite matrix.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"The determinant maximizer and its dual metric". -/
theorem PosSemidef.posDef_of_isMaxOn_det_re
    {S : Set (Matrix (Fin D) (Fin D) ℂ)}
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef)
    (hPmax : IsMaxOn (fun X ↦ X.det.re) S P)
    (hPD : ∃ X ∈ S, X.PosDef) : P.PosDef := by
  obtain ⟨P₀, hP₀mem, hP₀⟩ := hPD
  have hdetpos : 0 < P.det.re :=
    lt_of_lt_of_le (Complex.pos_iff.mp hP₀.det_pos).1 (hPmax hP₀mem)
  have hdet : P.det ≠ 0 := by
    intro heq
    simp only [heq, Complex.zero_re, lt_self_iff_false] at hdetpos
  exact hP.posDef_iff_det_ne_zero.mpr hdet

/-- A compact set of positive-semidefinite matrices containing a positive-definite
matrix has a positive-definite determinant maximizer. Positive-semidefinite
determinants are real, so maximizing the real part maximizes the determinant.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"The determinant maximizer and its dual metric". -/
theorem exists_posDef_isMaxOn_det_re_of_isCompact
    {S : Set (Matrix (Fin D) (Fin D) ℂ)} (hS : IsCompact S)
    (hPSD : ∀ P ∈ S, P.PosSemidef)
    (hPD : ∃ P ∈ S, P.PosDef) :
    ∃ P ∈ S, P.PosDef ∧ IsMaxOn (fun X ↦ X.det.re) S P := by
  have hnonempty : S.Nonempty := by
    obtain ⟨P, hP, _⟩ := hPD
    exact ⟨P, hP⟩
  obtain ⟨P, hPmem, hPmax⟩ := hS.exists_isMaxOn hnonempty
    (Complex.continuous_re.comp continuous_id.matrix_det).continuousOn
  exact ⟨P, hPmem, (hPSD P hPmem).posDef_of_isMaxOn_det_re hPmax hPD, hPmax⟩

/-- A trace-normalized real affine matrix subspace containing a positive-definite
matrix admits a positive-definite determinant maximizer over its entire
positive-semidefinite part.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"The determinant maximizer and its dual metric". This is the compactness and
existence step; the derivative identity and circuit construction are separate. -/
theorem exists_posDef_det_re_max_of_trace_mul_eq_one
    (C : AffineSubspace ℝ (Matrix (Fin D) (Fin D) ℂ))
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosDef)
    (hnorm : ∀ P ∈ C, (P * Q).trace = 1)
    (hPD : ∃ P ∈ C, P.PosDef) :
    ∃ P ∈ C, P.PosDef ∧
      ∀ X ∈ C, X.PosSemidef → X.det.re ≤ P.det.re := by
  obtain ⟨P₀, hP₀mem, hP₀⟩ := hPD
  obtain ⟨P, hPmem, hPpd, hPmax⟩ := exists_posDef_isMaxOn_det_re_of_isCompact
    (isCompact_affineSubspace_inter_posSemidef C hQ hnorm)
    (fun _ h ↦ h.2) ⟨P₀, ⟨hP₀mem, hP₀.posSemidef⟩, hP₀⟩
  exact ⟨P, hPmem.1, hPpd, fun X hXC hX ↦ hPmax ⟨hXC, hX⟩⟩

end Matrix
