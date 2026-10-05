/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normalizing a scalar-correct physical factorization

Positive scalar factors disappear after normalizing both states. The tensor
product retains its complete pair of physical indices. Source: SCP10,
arXiv:1001.3807, the physical state comparison in Observation 6.6, lines 1896–1909.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The coefficient tensor product, retaining both complete physical registers. -/
def physicalStateProduct (ψ : EuclideanSpace ℂ ι) (ω : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) := WithLp.toLp 2 (fun p => ψ p.1 * ω p.2)

/-- The Hilbert norm of the coefficient tensor product is multiplicative. -/
theorem norm_physicalStateProduct (ψ : EuclideanSpace ℂ ι) (ω : EuclideanSpace ℂ κ) :
    ‖physicalStateProduct ψ ω‖ = ‖ψ‖ * ‖ω‖ := by
  have h : ‖physicalStateProduct ψ ω‖ ^ 2 = (‖ψ‖ * ‖ω‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, physicalStateProduct]
    simp only [norm_mul, mul_pow, Fintype.sum_prod_type,
      ← Finset.mul_sum, ← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp h

/-- A nonzero physical vector has unit norm after inverse-norm rescaling. -/
theorem norm_normalized_physicalState (ψ : EuclideanSpace ℂ ι) (hψ : ψ ≠ 0) :
    ‖(‖ψ‖ : ℂ)⁻¹ • ψ‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg ψ),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψ)]

/-- An actual isometry and a positive scalar-correct factorization imply the
normalized tensor-product identity. A unit ancillary factor contributes no
additional normalization. -/
theorem LinearIsometry.normalized_physicalStateProduct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (I : E →ₗᵢ[ℂ] EuclideanSpace ℂ (ι × κ)) (x : E)
    (ψ : EuclideanSpace ℂ ι) (ω : EuclideanSpace ℂ κ) {r : ℝ} (hr : 0 < r)
    (hω : ‖ω‖ = 1) (h : I x = (r : ℂ) • physicalStateProduct ψ ω) :
    I ((‖x‖ : ℂ)⁻¹ • x) = physicalStateProduct ((‖ψ‖ : ℂ)⁻¹ • ψ) ω := by
  have hn : ‖x‖ = r * ‖ψ‖ := by
    rw [← I.norm_map x, h, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hr.le, norm_physicalStateProduct, hω, mul_one]
  rw [map_smul, h, smul_smul, hn, Complex.ofReal_mul, mul_inv_rev]
  have hscalar : ((r : ℂ) * (‖ψ‖ : ℂ))⁻¹ * (r : ℂ) = (‖ψ‖ : ℂ)⁻¹ := by
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), mul_one]
  rw [← mul_inv_rev, hscalar]
  apply WithLp.ofLp_injective 2
  funext p
  change (‖ψ‖ : ℂ)⁻¹ * (ψ p.1 * ω p.2) = ((‖ψ‖ : ℂ)⁻¹ * ψ p.1) * ω p.2
  exact (mul_assoc _ _ _).symm

end TNLean.PEPS
