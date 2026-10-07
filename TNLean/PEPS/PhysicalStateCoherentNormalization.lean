/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.PhysicalStateNormalization

/-!
# Coherent families under a uniform physical factorization

A single isometry and a single positive scalar transport every coherent sum
with one fixed unit ancillary state. Source: SCP10, arXiv:1001.3807,
Observation 6.6 and the closure span in Theorem 5.9.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

omit [Fintype ι] [Fintype κ] in
/-- A fixed ancillary factor commutes with arbitrary coherent linear sums. -/
theorem physicalStateProduct_sum (c : S → ℂ) (ψ : S → EuclideanSpace ℂ ι)
    (ω : EuclideanSpace ℂ κ) :
    physicalStateProduct (∑ p, c p • ψ p) ω =
      ∑ p, c p • physicalStateProduct (ψ p) ω := by
  apply WithLp.ofLp_injective 2
  funext q
  simp [physicalStateProduct, Finset.sum_mul, mul_assoc]

/-- Uniform scalar-correct factorization preserves every coherent sum,
including its nonvanishing and exact normalized vector. No independent
state-dependent choices of isometry or phase are made. -/
theorem LinearIsometry.coherent_physicalStateProduct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (I : E →ₗᵢ[ℂ] EuclideanSpace ℂ (ι × κ))
    (x : S → E) (ψ : S → EuclideanSpace ℂ ι) (ω : EuclideanSpace ℂ κ)
    {r : ℝ} (hr : 0 < r) (hω : ‖ω‖ = 1)
    (h : ∀ p, I (x p) = (r : ℂ) • physicalStateProduct (ψ p) ω)
    (c : S → ℂ) :
    I (∑ p, c p • x p) = (r : ℂ) • physicalStateProduct (∑ p, c p • ψ p) ω ∧
      ((∑ p, c p • x p) ≠ 0 ↔ (∑ p, c p • ψ p) ≠ 0) ∧
      I ((‖∑ p, c p • x p‖ : ℂ)⁻¹ • ∑ p, c p • x p) =
        physicalStateProduct ((‖∑ p, c p • ψ p‖ : ℂ)⁻¹ • ∑ p, c p • ψ p) ω := by
  have hf : I (∑ p, c p • x p) =
      (r : ℂ) • physicalStateProduct (∑ p, c p • ψ p) ω := by
    rw [physicalStateProduct_sum, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, h, smul_comm]
  have hn : ‖∑ p, c p • x p‖ = r * ‖∑ p, c p • ψ p‖ := by
    rw [← I.norm_map, hf, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hr.le, norm_physicalStateProduct, hω, mul_one]
  refine ⟨hf, ?_, LinearIsometry.normalized_physicalStateProduct I _ _ ω hr hω hf⟩
  have hiff : ‖∑ p, c p • x p‖ ≠ 0 ↔ ‖∑ p, c p • ψ p‖ ≠ 0 := by
    rw [hn, mul_ne_zero_iff]
    exact and_iff_right hr.ne'
  simpa only [norm_ne_zero_iff] using hiff

end TNLean.PEPS
