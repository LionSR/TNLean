/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondInterpolation
import TNLean.MPS.Symmetry.BondVectorInteraction

/-!
# Uniform gap along the normalized bond interpolation

The two-block bond vector of Schuch–Pérez-García–Cirac is normalized in the
Hilbert tensor product, and its parent interaction is `I - |ω⟩⟨ω|`.
The interaction is continuous, has norm at most one, and is an orthogonal
projection. The independent-bond Hamiltonians have ground energy zero
and spectral gap at least one for every real interpolation parameter and
every positive chain length.

**Local fix (second-block range):** The second block occupies coordinates
`D₀ + 1, …, D₀ + D₁`, as documented in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

This is the spectral step in arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma` and source lines 899–906. Identifying the interaction
with a nearest-neighbor interaction after regrouping physical registers,
and verifying its physical symmetry, are separate steps.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace MPSTensor

/-- The normalized interpolating bond in tensor-product coordinates.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def bondInterpolationVector (D₀ D₁ : ℕ) (γ : ℝ) :
    EuclideanSpace ℂ (Fin ((D₀ + D₁) * (D₀ + D₁))) :=
  WithLp.toLp 2 fun i => normalizedBondInterpolationMatrix D₀ D₁ γ
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- The interpolating bond has unit Hilbert norm at every real parameter.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem bondInterpolationVector_norm {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    ‖bondInterpolationVector D₀ D₁ γ‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.norm_sq_eq]
  simp only [bondInterpolationVector, PiLp.toLp_apply, ← Complex.normSq_eq_norm_sq, one_pow]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  exact normalizedBondInterpolationMatrix_sum_normSq h₀ h₁ γ

/-- The normalized bond vector depends continuously on the parameter.
Source: arXiv:1010.3732, Section II.F.2, source lines 899–906. -/
theorem continuous_bondInterpolationVector {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) :
    Continuous (bondInterpolationVector D₀ D₁) := by
  unfold bondInterpolationVector
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact (continuous_apply _).comp
    ((continuous_apply _).comp (continuous_normalizedBondInterpolationMatrix h₀ h₁))

/-- The complementary rank-one projection of the normalized bond interpolation.
Source: arXiv:1010.3732, Section II.F.2, source lines 904–906. -/
noncomputable def bondInterpolationInteraction (D₀ D₁ : ℕ) (γ : ℝ) :
    Matrix (Fin ((D₀ + D₁) * (D₀ + D₁))) (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ :=
  bondVectorInteraction (bondInterpolationVector D₀ D₁ γ)

/-- The normalized bond interpolation gives continuous bounded projector
interactions and independent-bond Hamiltonians with ground energy zero and
uniform gap at least one. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma` and source lines 899–906. -/
theorem bondInterpolationInteraction_uniform_gap {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) :
    Continuous (bondInterpolationInteraction D₀ D₁) ∧
    (∀ γ : ℝ, IsStarProjection (bondInterpolationInteraction D₀ D₁ γ) ∧
      ‖bondInterpolationInteraction D₀ D₁ γ‖ ≤ 1) ∧
    ∀ (γ : ℝ) (N : ℕ) (hN : 1 ≤ N),
      (0 : ℂ) ∈ spectrum ℂ (independentBondHamiltonian hN (bondInterpolationInteraction D₀ D₁ γ)) ∧
      ∀ z ∈ spectrum ℂ (independentBondHamiltonian hN (bondInterpolationInteraction D₀ D₁ γ)),
        0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  refine ⟨(continuous_bondVectorInteraction _).comp (continuous_bondInterpolationVector h₀ h₁),
    fun γ => ⟨bondVectorInteraction_isStarProjection _ (bondInterpolationVector_norm h₀ h₁ γ),
      bondVectorInteraction_norm_le_one _ (bondInterpolationVector_norm h₀ h₁ γ)⟩, ?_⟩
  intro γ N hN
  exact ⟨independentBondHamiltonian_zero_mem_spectrum hN _
      (bondVectorInteraction_isStarProjection _ (bondInterpolationVector_norm h₀ h₁ γ))
      (bondVectorInteraction_ne_one _ (bondInterpolationVector_norm h₀ h₁ γ)),
    independentBondHamiltonian_spectrum_gap hN _
      (bondVectorInteraction_isStarProjection _ (bondInterpolationVector_norm h₀ h₁ γ))⟩

end MPSTensor
