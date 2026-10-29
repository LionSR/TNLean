/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleWallGramSlopePositive
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The actual wall slope as a real quadratic form

The convergent correlation series is complex linear in the wall. Contracting
it against a second wall and taking the real part gives a real bilinear
form. Its diagonal is exactly the real part of the actual limiting Gram
coefficient, so the source coefficient is a nonnegative quadratic form
under the standing canonical normalizations.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1250–1265.
The full perturbation span is used only to obtain a positive witness,
not inserted into a definition of the quadratic coefficient.
-/

open scoped Matrix BigOperators ComplexOrder TNOperatorSpace Topology

namespace MPSTensor

variable {d a b : ℕ}

private theorem uncleWallSeed_add (B : MPSTensor d b)
    (R S : Fin d → Matrix (Fin a) (Fin b) ℂ) :
    uncleWallSeed B (R + S) = uncleWallSeed B R + uncleWallSeed B S := by
  simp [uncleWallSeed, Matrix.add_mul, Finset.sum_add_distrib]

private theorem uncleWallSeed_smul (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (c : ℂ) :
    uncleWallSeed B (c • R) = c • uncleWallSeed B R := by
  simp [uncleWallSeed, Matrix.smul_mul, Finset.smul_sum]

/-- The actual convergent wall correlation series is complex linear in its
wall argument under strict mixed spectral-radius damping;
arXiv:1210.6613, quadratic coefficient in the proof of Lemma lowenergystates. -/
noncomputable def uncleWallCorrelationLimitLinear
    (A : MPSTensor d a) (B : MPSTensor d b)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    (Fin d → Matrix (Fin a) (Fin b) ℂ) →ₗ[ℂ] Matrix (Fin a) (Fin b) ℂ where
  toFun := uncleWallCorrelationLimit A B
  map_add' R S := by
    simp only [uncleWallCorrelationLimit, uncleWallSeed_add, map_add]
    exact (uncleWallCorrelation_summable A B R hSpect).tsum_add
      (uncleWallCorrelation_summable A B S hSpect)
  map_smul' c R := by
    simp only [RingHom.id_apply, uncleWallCorrelationLimit, uncleWallSeed_smul, map_smul]
    exact (uncleWallCorrelation_summable A B R hSpect).tsum_const_smul c

@[simp] theorem uncleWallCorrelationLimitLinear_apply
    (A : MPSTensor d a) (B : MPSTensor d b)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) :
    uncleWallCorrelationLimitLinear A B hSpect R = uncleWallCorrelationLimit A B R := rfl

/-- The real bilinear contraction whose diagonal is the actual wall slope.
The mixed correlation is taken in the first wall and the adjoint in the
second; arXiv:1210.6613, proof of Lemma lowenergystates. -/
noncomputable def uncleWallSlopeBilin
    (A : MPSTensor d a) (B : MPSTensor d b)
    (ρ : Matrix (Fin a) (Fin a) ℂ)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    (Fin d → Matrix (Fin a) (Fin b) ℂ) →ₗ[ℝ]
      (Fin d → Matrix (Fin a) (Fin b) ℂ) →ₗ[ℝ] ℝ := by
  let Z := (uncleWallCorrelationLimitLinear A B hSpect).restrictScalars ℝ
  refine LinearMap.mk₂ ℝ (fun R S ↦
    (Matrix.trace (ρ * ∑ i, R i * (S i)ᴴ)).re +
      2 * (Matrix.trace (ρ * ∑ i, A i * Z R * (S i)ᴴ)).re) ?_ ?_ ?_ ?_
  · intro R R' S
    simp [map_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sum,
      Finset.sum_add_distrib, Matrix.trace_add]
    ring
  · intro c R S
    simp [map_smul, Matrix.smul_mul, Matrix.mul_smul, ← Finset.smul_sum,
      Matrix.trace_smul, smul_eq_mul]
    ring
  · intro R S S'
    simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.mul_sum,
      Finset.sum_add_distrib, Matrix.trace_add]
    ring
  · intro c R S
    simp [Matrix.conjTranspose_smul, Matrix.mul_smul, ← Finset.smul_sum,
      Matrix.trace_smul, smul_eq_mul]
    ring

/-- The actual source norm coefficient as a real quadratic form on the
space of rectangular walls; arXiv:1210.6613, proof of Lemma lowenergystates.
No positivity or genericity premise is used in this definition. -/
noncomputable def uncleWallSlopeQuadratic
    (A : MPSTensor d a) (B : MPSTensor d b)
    (ρ : Matrix (Fin a) (Fin a) ℂ)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    QuadraticForm ℝ (Fin d → Matrix (Fin a) (Fin b) ℂ) :=
  LinearMap.BilinMap.toQuadraticMap (uncleWallSlopeBilin A B ρ hSpect)

/-- Evaluating the real quadratic form gives exactly the real part of the
actual mixed-series slope, not a replacement coefficient;
arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallSlopeQuadratic_apply
    (A : MPSTensor d a) (B : MPSTensor d b)
    (ρ : Matrix (Fin a) (Fin a) ℂ)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) :
    uncleWallSlopeQuadratic A B ρ hSpect R = (uncleWallNormSlope A B R ρ).re := by
  change (Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ)).re +
    2 * (uncleWallCrossWeight A R ρ (uncleWallCorrelationLimit A B R)).re =
      (uncleWallNormSlope A B R ρ).re
  rw [uncleWallNormSlope, Complex.add_re, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- The source normalized wall quadratic form is nonnegative at every wall;
arXiv:1210.6613, norm coefficient in the proof of Lemma lowenergystates. -/
theorem uncleWallSlopeQuadratic_nonneg
    (A : MPSTensor d a) (B : MPSTensor d b)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosSemidef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) :
    0 ≤ uncleWallSlopeQuadratic A B ρ hSpect R := by
  rw [uncleWallSlopeQuadratic_apply]
  exact (Complex.nonneg_iff.mp (uncleWallNormSlope_nonneg A B R ρ hρ hA hB hSpect)).1

/-- The explicit annihilator wall makes the actual coefficient a nonzero
quadratic form whenever the physical dimension exceeds the right-block
matrix dimension. Source: arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallSlopeQuadratic_ne_zero_of_bond_sq_lt [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef) (hd : b * b < d)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    uncleWallSlopeQuadratic A B ρ hSpect ≠ 0 := by
  obtain ⟨R, _, _, hR⟩ := exists_uncleWallNormSlope_pos A B ρ hρ hd
  intro hzero
  have hq := congrArg
    (fun Q : QuadraticForm ℝ (Fin d → Matrix (Fin a) (Fin b) ℂ) ↦ Q R) hzero
  change uncleWallSlopeQuadratic A B ρ hSpect R = 0 at hq
  rw [uncleWallSlopeQuadratic_apply] at hq
  exact (ne_of_gt (Complex.pos_iff.mp hR).1) hq

/-- The actual quadratic coefficient is not identically zero in the source
full-perturbation setting with a faithful density;
arXiv:1210.6613, proof of Lemma lowenergystates, nonzero quadratic coefficient. -/
theorem uncleWallSlopeQuadratic_ne_zero [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    uncleWallSlopeQuadratic A B ρ hSpect ≠ 0 := by
  obtain ⟨R, _, _, hR⟩ :=
    exists_uncleWallNormSlope_pos_of_injective_perturbation A B R₀ L₀ hPert ρ hρ
  intro hzero
  have hq := congrArg
    (fun Q : QuadraticForm ℝ (Fin d → Matrix (Fin a) (Fin b) ℂ) ↦ Q R) hzero
  change uncleWallSlopeQuadratic A B ρ hSpect R = 0 at hq
  rw [uncleWallSlopeQuadratic_apply] at hq
  exact (ne_of_gt (Complex.pos_iff.mp hR).1) hq

end MPSTensor
