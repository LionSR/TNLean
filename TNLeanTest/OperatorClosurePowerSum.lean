/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.OperatorClosurePowerSum

/-!
# Signature and axiom checks for operator-closure power sums

The example checks the full public signature, including eventual uniqueness among
arbitrary coefficients and uniqueness of the nonzero-weight multisets. The guarded
axiom report checks that the theorem uses only the standard Lean axioms.
-/

open scoped BigOperators
open MPOTensor MPSTensor

variable {d : ℕ}

example
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
        ∀ γ, (↑(List.ofFn (μ' γ)) : Multiset ℂ) = ↑(List.ofFn (μ γ)) :=
  exists_operatorProduct_powerSum_coeff_unique M hM hD hdistinct a b hspan

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPOTensor.exists_operatorProduct_powerSum_coeff_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPOTensor.exists_operatorProduct_powerSum_coeff_unique

end AxiomChecks
