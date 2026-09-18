/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.OperatorProduct
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients

/-!
# Power-sum coefficients of operator closure

For a finite family of normal pair-alphabet MPO tensors separated up to nonzero
scalar gauge, closure of a fixed operator product in their span at every positive
length gives unique finite multisets of nonzero complex weights. Their power sums
expand the product at every positive length and determine any other coefficients
eventually. The total weighted bond dimension is bounded by the product bond dimension.

This is the operator form of the unblocked MPS power-sum theorem, using the product
tensor of arXiv:1606.00608, Section 4.5. No positivity of the weights or renormalization
fixed-point channel structure is asserted.
-/

open scoped BigOperators

namespace MPOTensor

open MPSTensor

variable {d : ℕ}

private theorem mpo_eq_sum_iff_mpv {DB : ℕ} (B : MPOTensor d DB)
    {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ} (M : ∀ γ, MPOTensor d (DM γ))
    (L : ℕ) (c : Γ → ℂ) :
    mpo B L = ∑ γ, c γ • mpo (M γ) L ↔
      ∀ σ : Fin L → Fin (d * d),
        mpv B.toMPSTensor σ = ∑ γ, c γ * mpv (M γ).toMPSTensor σ := by
  constructor
  · intro h σ
    have he := congrArg (fun A => A (fun k => (σ k).divNat)
      (fun k => (σ k).modNat)) h
    simpa only [mpv, coeff, evalWord_toMPSTensor_ofFn, mpo_apply, mpoMatrixEntry,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using he
  · intro h
    ext σ τ
    have he := h (fun k => finProdFinEquiv (σ k, τ k))
    simpa only [mpv, coeff, evalWord_toMPSTensor_pairConfig, mpo_apply, mpoMatrixEntry,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using he

/-- Operator closure at every positive length yields a unique nonzero-weight
power-sum expansion for each output tensor. Arbitrary expansion coefficients agree
with these power sums beyond a positive threshold, and the sum of multiplicities
times output bond dimensions is at most the product bond dimension.

Normality and separation are imposed on the pair-alphabet MPS views. Separation
excludes every nonzero scalar gauge, not only unit-modulus phases. The weights are
complex and need not be positive. -/
theorem exists_operatorProduct_powerSum_coeff_unique
    {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ} (M : ∀ γ, MPOTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ).toMPSTensor) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv
        (cast (congr_arg (MPSTensor (d * d)) h) (M γ).toMPSTensor)
        (M δ).toMPSTensor)
    (a b : Γ)
    (hspan : ∀ L : ℕ, 0 < L → ∃ c : Γ → ℂ,
      mpo (M a) L * mpo (M b) L = ∑ γ, c γ • mpo (M γ) L) :
    ∃ (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      (∀ L : ℕ, 0 < L →
        mpo (M a) L * mpo (M b) L = ∑ γ, (∑ k, (μ γ k) ^ L) • mpo (M γ) L) ∧
      (∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∀ c : Γ → ℂ,
        (mpo (M a) L * mpo (M b) L = ∑ γ, c γ • mpo (M γ) L) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ L) ∧
      ∑ γ, n γ * DM γ ≤ DM a * DM b ∧
      ∀ (n' : Γ → ℕ) (μ' : ∀ γ, Fin (n' γ) → ℂ), (∀ γ k, μ' γ k ≠ 0) →
        (∃ L₁ : ℕ, ∀ L, L₁ ≤ L →
          mpo (M a) L * mpo (M b) L = ∑ γ, (∑ k, (μ' γ k) ^ L) • mpo (M γ) L) →
        ∀ γ, (↑(List.ofFn (μ' γ)) : Multiset ℂ) = ↑(List.ofFn (μ γ)) := by
  have bridge (L : ℕ) (c : Γ → ℂ) :=
    mpo_eq_sum_iff_mpv (mulTensor (M a) (M b)) M L c
  simp only [mpo_mulTensor] at bridge
  obtain ⟨n, μ, hμ, hexp, ⟨L₀, hL₀, hrig⟩, hbound, huniq⟩ :=
    MPSTensor.exists_unblocked_powerSum_coeff_unique
      (mulTensor (M a) (M b)).toMPSTensor (fun γ => (M γ).toMPSTensor)
      hM hD hdistinct (by
        intro L hL
        obtain ⟨c, hc⟩ := hspan L hL
        exact ⟨c, (bridge L c).mp hc⟩)
  refine ⟨n, μ, hμ, ?_, ⟨L₀, hL₀, ?_⟩, hbound, ?_⟩
  · intro L hL
    exact (bridge L _).mpr (hexp L hL)
  · intro L hL c hc
    exact hrig L hL c ((bridge L c).mp hc)
  · intro n' μ' hμ' ⟨L₁, hL₁⟩
    exact huniq n' μ' hμ' ⟨L₁, fun L hL => (bridge L _).mp (hL₁ L hL)⟩

end MPOTensor
