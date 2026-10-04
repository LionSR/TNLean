/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineGramHull
import TNLean.MPS.MPU.AffineGramBalancing
import QICLean.Analysis.MatrixSqrt

/-!
# Interval isometries from affine Gram normalization

An interval transfer maps the real affine hull of earlier prefix Grams into
the real affine hull of the longer prefix. A positive right metric normalized
on that longer hull therefore makes every density-weighted interval Gram have
trace one. Density separation then gives the complete isometry identity for
the interval weighted by the positive square roots of its two metrics.

This is the interval-isometry argument in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The interval isometry is
derived from affine normalization rather than supplied as a hypothesis.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPUCircuit

variable {o i o' i' m n : Type*}
  [Fintype o] [Fintype i] [Fintype o'] [Fintype i'] [Fintype m] [Fintype n]

/-- Affine normalization of the longer prefix determines the entire interval
input Gram, including off-diagonal entries. Input density matrices may be
entangled throughout the interval. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem intervalInputGram_eq_one_of_prefixGramAffineHull [DecidableEq i']
    (F : o → i → Matrix Unit m ℂ) (A : o' → i' → Matrix m n ℂ)
    {P : Matrix m m ℂ} (hP : P ∈ prefixGramAffineHull F)
    (Q : Matrix n n ℂ)
    (hQ : ∀ X ∈ prefixGramAffineHull
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2),
        trace (X * Q) = 1) :
    intervalInputGram A P Q = 1 := by
  apply intervalInputGram_eq_one_of_density_tests
  intro ρ hρ hρtrace
  rw [trace_mul_comm]
  exact hQ _ (intervalGramTransfer_mem_prefixGramAffineHull_concat F A hρ hρtrace hP)

open scoped Classical in
/-- Positive square roots of affine-normalized boundary Grams produce an
explicit interval isometry. No interval-isometry hypothesis or restriction
to product inputs is imposed. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem vectorizedWeightedInterval_isometry_of_prefixGramAffineHull
    (F : o → i → Matrix Unit m ℂ) (A : o' → i' → Matrix m n ℂ)
    {P : Matrix m m ℂ} (hP : P ∈ prefixGramAffineHull F) (hPpos : P.PosSemidef)
    {Q : Matrix n n ℂ} (hQpos : Q.PosSemidef)
    (hQ : ∀ X ∈ prefixGramAffineHull
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2),
        trace (X * Q) = 1) :
    (vectorizedWeightedInterval A (CFC.sqrt P) (CFC.sqrt Q))ᴴ *
      vectorizedWeightedInterval A (CFC.sqrt P) (CFC.sqrt Q) = 1 := by
  rw [vectorizedWeightedInterval_gram]
  simp only [conjTranspose_cfc_sqrt, CFC.sqrt_mul_sqrt_self P hPpos.nonneg,
    CFC.sqrt_mul_sqrt_self Q hQpos.nonneg]
  exact intervalInputGram_eq_one_of_prefixGramAffineHull F A hP Q hQ

open scoped Classical in
/-- Determinant balancing at both bounding cuts produces compatible positive
metrics and the derived interval isometry. The only boundary premises are
positive-definite normalization witnesses and positive-definite points of
the physical-prefix affine hulls. Both inverse-metric traces depend only on
the corresponding bond dimension. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_balanced_prefix_metrics_interval_isometry
    {D E : ℕ} [Nonempty (Fin D)] [Nonempty (Fin E)]
    (F : o → i → Matrix Unit (Fin D) ℂ)
    (A : o' → i' → Matrix (Fin D) (Fin E) ℂ)
    {Q₀ : Matrix (Fin D) (Fin D) ℂ} (hQ₀ : Q₀.PosDef)
    (hleftNorm : ∀ X ∈ prefixGramAffineHull F, trace (X * Q₀) = 1)
    (hleftPD : ∃ X ∈ prefixGramAffineHull F, X.PosDef)
    {Q₁ : Matrix (Fin E) (Fin E) ℂ} (hQ₁ : Q₁.PosDef)
    (hrightNorm : ∀ X ∈ prefixGramAffineHull
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2),
        trace (X * Q₁) = 1)
    (hrightPD : ∃ X ∈ prefixGramAffineHull
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2), X.PosDef) :
    ∃ P ∈ prefixGramAffineHull F,
      ∃ S ∈ prefixGramAffineHull
        (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2),
        P.PosDef ∧ S.PosDef ∧ (dualGramMetric P).PosDef ∧ (dualGramMetric S).PosDef ∧
        (∀ X ∈ prefixGramAffineHull F, trace (X * dualGramMetric P) = 1) ∧
        (∀ X ∈ prefixGramAffineHull
          (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2),
            trace (X * dualGramMetric S) = 1) ∧
        trace ((dualGramMetric P)⁻¹ * P⁻¹) = (D : ℂ) ^ 2 ∧
        trace ((dualGramMetric S)⁻¹ * S⁻¹) = (E : ℂ) ^ 2 ∧
        (vectorizedWeightedInterval A (CFC.sqrt P) (CFC.sqrt (dualGramMetric S)))ᴴ *
          vectorizedWeightedInterval A (CFC.sqrt P) (CFC.sqrt (dualGramMetric S)) = 1 := by
  obtain ⟨P, hPC, hP, hdualP, hPNorm, hPTrace⟩ :=
    exists_posDef_dualGramMetric_on_affineSubspace (prefixGramAffineHull F)
      (fun X hX ↦ isHermitian_of_mem_prefixGramAffineHull F hX) hQ₀ hleftNorm hleftPD
  obtain ⟨S, hSC, hS, hdualS, hSNorm, hSTrace⟩ :=
    exists_posDef_dualGramMetric_on_affineSubspace
      (prefixGramAffineHull (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2))
      (fun X hX ↦ isHermitian_of_mem_prefixGramAffineHull _ hX) hQ₁ hrightNorm hrightPD
  refine ⟨P, hPC, S, hSC, hP, hS, hdualP, hdualS,
    hPNorm, hSNorm, hPTrace, hSTrace, ?_⟩
  exact vectorizedWeightedInterval_isometry_of_prefixGramAffineHull F A hPC
    hP.posSemidef hdualS.posSemidef hSNorm

end MPUCircuit
