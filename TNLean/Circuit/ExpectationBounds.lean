/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryMulVecInner
import TNLean.Circuit.LocalCircuit

/-!
# Stability of expectations and connected correlations

The expectation of a unitary observable in a unit vector has modulus at most one.
Changing the unit vector by distance `η` changes the expectation by at most `2η`
and a connected two-point correlation by at most `6η`. These estimates use the
Euclidean distance between vectors and do not require a density-matrix representation.
-/

open Matrix
open scoped InnerProductSpace

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate expectation is the Euclidean inner product with the operator image. -/
theorem expect_eq_inner (ψ : (ι → Fin d) → ℂ)
    (A : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    expect ψ A = ⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (ι → Fin d)),
      WithLp.toLp 2 (A *ᵥ ψ)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- The expectation of a unitary in a unit vector has modulus at most one. -/
theorem norm_expect_le_one {ψ : (ι → Fin d) → ℂ}
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (ι → Fin d))‖ = 1)
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ unitary _) :
    ‖expect ψ A‖ ≤ 1 := by
  rw [expect_eq_inner]
  have hAψ : ‖(WithLp.toLp 2 (A *ᵥ ψ) : EuclideanSpace ℂ (ι → Fin d))‖ = 1 :=
    (Matrix.norm_eq_of_mulVec_eq hA rfl).trans hψ
  simpa [hψ, hAψ] using norm_inner_le_norm
    (WithLp.toLp 2 ψ : EuclideanSpace ℂ (ι → Fin d)) (WithLp.toLp 2 (A *ᵥ ψ))

/-- Expectations of a unitary differ by at most twice the distance between unit vectors. -/
theorem norm_expect_sub_le {ψ φ : (ι → Fin d) → ℂ}
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (ι → Fin d))‖ = 1)
    (hφ : ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ (ι → Fin d))‖ = 1)
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ unitary _) :
    ‖expect ψ A - expect φ A‖ ≤
      2 * ‖(WithLp.toLp 2 ψ - WithLp.toLp 2 φ : EuclideanSpace ℂ (ι → Fin d))‖ := by
  let x : EuclideanSpace ℂ (ι → Fin d) := WithLp.toLp 2 ψ
  let y : EuclideanSpace ℂ (ι → Fin d) := WithLp.toLp 2 φ
  let Ax : EuclideanSpace ℂ (ι → Fin d) := WithLp.toLp 2 (A *ᵥ ψ)
  let Ay : EuclideanSpace ℂ (ι → Fin d) := WithLp.toLp 2 (A *ᵥ φ)
  have hAx : ‖Ax‖ = 1 := (Matrix.norm_eq_of_mulVec_eq hA rfl).trans hψ
  have hdiff : ‖Ax - Ay‖ = ‖x - y‖ :=
    Matrix.norm_eq_of_mulVec_eq hA (by
      change (A *ᵥ ψ) - (A *ᵥ φ) = A *ᵥ (ψ - φ)
      exact (mulVec_sub A ψ φ).symm)
  have heq : expect ψ A - expect φ A = ⟪x - y, Ax⟫_ℂ + ⟪y, Ax - Ay⟫_ℂ := by
    rw [expect_eq_inner, expect_eq_inner, inner_sub_left, inner_sub_right]
    change ⟪x, Ax⟫_ℂ - ⟪y, Ay⟫_ℂ = _
    ring
  rw [heq]
  calc
    _ ≤ ‖⟪x - y, Ax⟫_ℂ‖ + ‖⟪y, Ax - Ay⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖Ax‖ + ‖y‖ * ‖Ax - Ay‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = 2 * ‖x - y‖ := by rw [hAx, hdiff, hφ]; ring

/-- Multiplying a state by a scalar of modulus one preserves every expectation. -/
theorem expect_smul_state {c : ℂ} (hc : ‖c‖ = 1) (ψ : (ι → Fin d) → ℂ)
    (A : Matrix (ι → Fin d) (ι → Fin d) ℂ) : expect (c • ψ) A = expect ψ A := by
  have hc' : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hc]
    norm_num
  simp only [expect, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [← mul_assoc, mul_comm c (star c), hc', one_mul]

/-- Connected two-point correlations of unitary observables are Lipschitz on unit vectors. -/
theorem norm_covariance_sub_le {ψ φ : (ι → Fin d) → ℂ}
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (ι → Fin d))‖ = 1)
    (hφ : ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ (ι → Fin d))‖ = 1)
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ unitary _) (hB : B ∈ unitary _) :
    ‖(expect ψ (A * B) - expect ψ A * expect ψ B) -
      (expect φ (A * B) - expect φ A * expect φ B)‖ ≤
      6 * ‖(WithLp.toLp 2 ψ - WithLp.toLp 2 φ : EuclideanSpace ℂ (ι → Fin d))‖ := by
  let η := ‖(WithLp.toLp 2 ψ - WithLp.toLp 2 φ : EuclideanSpace ℂ (ι → Fin d))‖
  have hAB := norm_expect_sub_le hψ hφ (Submonoid.mul_mem (unitary _) hA hB)
  have hAd := norm_expect_sub_le hψ hφ hA
  have hBd := norm_expect_sub_le hψ hφ hB
  have hAφ := norm_expect_le_one hφ hA
  have hBψ := norm_expect_le_one hψ hB
  have heq : (expect ψ (A * B) - expect ψ A * expect ψ B) -
      (expect φ (A * B) - expect φ A * expect φ B) =
      (expect ψ (A * B) - expect φ (A * B)) -
        ((expect ψ A - expect φ A) * expect ψ B +
          expect φ A * (expect ψ B - expect φ B)) := by ring
  rw [heq]
  calc
    _ ≤ ‖expect ψ (A * B) - expect φ (A * B)‖ +
        (‖expect ψ A - expect φ A‖ * ‖expect ψ B‖ +
          ‖expect φ A‖ * ‖expect ψ B - expect φ B‖) := by
      refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
      simpa only [norm_mul] using norm_add_le
        ((expect ψ A - expect φ A) * expect ψ B)
        (expect φ A * (expect ψ B - expect φ B))
    _ ≤ 2 * η + (2 * η * 1 + 1 * (2 * η)) :=
      add_le_add hAB (add_le_add
        (mul_le_mul hAd hBψ (norm_nonneg _) (by positivity))
        (mul_le_mul hAφ hBd (norm_nonneg _) (by norm_num)))
    _ = 6 * η := by ring

end QuantumCircuit
