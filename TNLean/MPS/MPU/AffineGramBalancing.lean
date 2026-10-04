/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineGramCompactness
import TNLean.MPS.MPU.BalancedGramMetrics
import TNLean.MPS.MPU.DeterminantStationarity

/-!
# Determinant balancing of affine cap Grams

A trace-normalized real affine space of Hermitian matrices containing a
positive-definite matrix admits a positive-definite determinant maximizer.
Its inverse divided by the dimension normalizes every matrix in that affine
space. The associated inverse-metric trace is the square of the dimension.

This is the determinant-balancing lemma of Section 5 in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The formal statement below
concerns a single affine Gram space. Realizing the compatible interval maps
as a complete quantum circuit is a further statement.
-/

open Matrix
open scoped ComplexOrder

namespace MPUCircuit

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

end MPUCircuit
