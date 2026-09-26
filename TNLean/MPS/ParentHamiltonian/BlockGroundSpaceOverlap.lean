/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.MixedBoundaryGram
import TNLean.MPS.ParentHamiltonian.GramInverseConvergence
import TNLean.Spectral.TransferOperatorGapNT

/-!
# Decay of overlaps between block ground spaces

Mixed-transfer decay and the invertibility of the limiting boundary Gram
operators give a uniform bound on inner products of ground-space vectors.
This follows Nachtergaele, arXiv:cond-mat/9410110, proof of Lemma `disjoint`,
equations `C1C2` and `limP12`.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

/-- A strict mixed-transfer spectral-radius bound gives operator-norm decay
of the mixed boundary Gram operator, as in Nachtergaele,
arXiv:cond-mat/9410110, proof of Lemma `disjoint`, equation `limP12`. -/
theorem adjoint_groundSpaceMapES_comp_tendsto_zero_of_spectralRadius_lt_one
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hgap : Kraus.mixedMapSpectralRadius B A < 1) :
    Filter.Tendsto (fun n ↦ (groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n))
      Filter.atTop (nhds 0) :=
  adjoint_groundSpaceMapES_comp_tendsto_zero A B
    (Kraus.mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one B A hgap)

variable [NeZero D₁] [NeZero D₂]

/-- The ground spaces of two primitive tensors become uniformly orthogonal
when the mixed transfer map has spectral radius less than one. This combines
the boundary normalization and mixed-transfer estimates in Nachtergaele,
arXiv:cond-mat/9410110, proof of Lemma `disjoint`, equations `C1C2` and `limP12`.
The spectral-radius hypothesis is supplied separately by inequivalence of the
normalized blocks. -/
theorem IsPrimitiveMPS.eventually_norm_inner_groundSpaceES_le_of_mixed_gap
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} {σ : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsPrimitiveMPS A ρ) (hB : IsPrimitiveMPS B σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hgap : Kraus.mixedMapSpectralRadius B A < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ x ∈ groundSpaceES A n, ∀ y ∈ groundSpaceES B n,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  let c := fun n ↦ Real.sqrt ‖Ring.inverse (groundSpaceGram A n)‖ *
    ‖(groundSpaceMapES A n).adjoint.comp (groundSpaceMapES B n)‖ *
    Real.sqrt ‖Ring.inverse (groundSpaceGram B n)‖
  have hc : Filter.Tendsto c Filter.atTop (nhds 0) := by
    have hleft := (Real.continuous_sqrt.tendsto _).comp
      (hA.groundSpaceGram_ringInverse_tendsto hρ).norm
    have hright := (Real.continuous_sqrt.tendsto _).comp
      (hB.groundSpaceGram_ringInverse_tendsto hσ).norm
    have hmiddle := (adjoint_groundSpaceMapES_comp_tendsto_zero_of_spectralRadius_lt_one
      A B hgap).norm
    simpa only [c, Function.comp_def, norm_zero, mul_zero, zero_mul] using
      (hleft.mul hmiddle).mul hright
  filter_upwards [(tendsto_order.1 hc).2 ε hε,
    hA.eventually_groundSpaceGram_isUnit_and_inverse_bound hρ
      (a := 1 / 2) (by norm_num) (by norm_num),
    hB.eventually_groundSpaceGram_isUnit_and_inverse_bound hσ
      (a := 1 / 2) (by norm_num) (by norm_num)] with n hn hnA hnB x hx y hy
  have h := norm_inner_groundSpaceES_le_mixedGram A B n
    (groundSpaceMapES_injective_of_isUnit_groundSpaceGram hnA.1)
    (groundSpaceMapES_injective_of_isUnit_groundSpaceGram hnB.1) hx hy
  simp only [ContinuousLinearMap.inverseGram_eq_ringInverse] at h
  change ‖⟪x, y⟫_ℂ‖ ≤ c n * ‖x‖ * ‖y‖ at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hn.le (norm_nonneg x)) (norm_nonneg y))

/-- Distinct normalized primitive blocks have asymptotically orthogonal local
ground spaces. This is Nachtergaele, arXiv:cond-mat/9410110, equation
`limitepsilonm` (lines 1661--1675), in the trace-preserving tensor convention.
Inequivalence is imposed only when the bond dimensions agree. -/
theorem IsPrimitiveMPS.eventually_norm_inner_groundSpaceES_le_of_inequivalent
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} {σ : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsPrimitiveMPS A ρ) (hB : IsPrimitiveMPS B σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ h : D₂ = D₁, ¬ GaugePhaseEquiv (h ▸ B) A)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ x ∈ groundSpaceES A n, ∀ y ∈ groundSpaceES B n,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  apply hA.eventually_norm_inner_groundSpaceES_le_of_mixed_gap hB hρ hσ _ hε
  by_cases hD : D₂ = D₁
  · subst D₂
    exact Kraus.mixedMapSpectralRadius_lt_one_of_irreducible_TP B A
      (hB.isIrreducibleMap_of_posDef hσ) (hA.isIrreducibleMap_of_posDef hρ)
      hB.norm hA.norm
      (fun h ↦ hDistinct rfl (gaugePhaseEquiv_of_krausGaugePhaseEquiv h))
  · exact Kraus.mixedMapSpectralRadius_lt_one_of_dim_ne_of_irreducible_TP B A
      (hB.isIrreducibleMap_of_posDef hσ) (hA.isIrreducibleMap_of_posDef hρ)
      hB.norm hA.norm hD

end MPSTensor
