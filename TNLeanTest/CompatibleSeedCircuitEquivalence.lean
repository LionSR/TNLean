/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CompatibleSeedCircuitEquivalence
import TNLean.MPS.Preparation.GHZSeedCircuit

/-! Regression examples for full-vector compatible coherent seed conversion. -/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped InnerProductSpace

-- Exact common seeds need no preparation from a product state.
example {d N : ℕ} [NeZero N] (χ : MPVSpace d N) (hχ : ‖χ‖ = 1) :
    ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (ψ : MPVSpace d N),
      U = 1 ∧ IsLocalCircuitOfDepth U 0 ∧
      (fun s => ψ s) = U *ᵥ (fun s => χ s) ∧ 1 - ‖⟪ψ, χ⟫_ℂ‖ ≤ 0 := by
  have hI : IsLocalCircuitOfDepth (1 : Matrix (Cfg d N) (Cfg d N) ℂ) 0 :=
    ⟨[], rfl, rfl⟩
  have he : 1 - ‖⟪χ, χ⟫_ℂ‖ ≤ (0 : ℝ) := by
    simp [inner_self_eq_norm_sq_to_K, hχ]
  simpa using exists_isLocalCircuitOfDepth_of_common_seed hχ hχ hχ hI hI
    (by simp only [Matrix.one_mulVec]) (by simp only [Matrix.one_mulVec]) he he

-- A genuine ring circuit used as the seed matcher is counted at its full depth.
example {d N : ℕ} [NeZero N] {χ η : MPVSpace d N} (hχ : ‖χ‖ = 1)
    (hη : ‖η‖ = 1) {R : Matrix (Cfg d N) (Cfg d N) ℂ} {T : ℕ}
    (hR : IsLocalCircuitOfDepth R T)
    (hseed : (fun s => η s) = R *ᵥ fun s => χ s) :
    ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (ψ : MPVSpace d N),
      U = R ∧ IsLocalCircuitOfDepth U T ∧
      (fun s => ψ s) = U *ᵥ (fun s => χ s) ∧ 1 - ‖⟪ψ, η⟫_ℂ‖ ≤ 0 := by
  have hI : IsLocalCircuitOfDepth (1 : Matrix (Cfg d N) (Cfg d N) ℂ) 0 :=
    ⟨[], rfl, rfl⟩
  have heχ : 1 - ‖⟪χ, χ⟫_ℂ‖ ≤ (0 : ℝ) := by
    simp [inner_self_eq_norm_sq_to_K, hχ]
  have heη : 1 - ‖⟪η, η⟫_ℂ‖ ≤ (0 : ℝ) := by
    simp [inner_self_eq_norm_sq_to_K, hη]
  simpa using exists_isLocalCircuitOfDepth_of_compatible_seeds hχ hη hχ hI hI hR
    (by simp only [Matrix.one_mulVec]) (by simp only [Matrix.one_mulVec]) hseed heχ heη

-- The coherent register map accepts arbitrary complex amplitudes; it is not
-- tied to a positive-weight normalization convention or a measurement branch.
example {d N M r b D : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {ℓ : Fin M → ℕ} {hN : ∑ k, ℓ k = N} {hr : ∀ k, r + r ≤ ℓ k}
    {e : Fin b → Cfg d r} (he : Function.Injective e)
    {A : MPSTensor d D} {ω : Fin b → Fin D × Fin D → ℂ}
    {U : Matrix (Cfg d N) (Cfg d N) ℂ}
    (hU : ∀ j, U *ᵥ Pi.single (registerCfg hN hr (e j)) 1 =
      fun s => blockIsometryState A (ω j) hN s) (α : Fin b → ℂ) :
    U *ᵥ windowGHZState hN hr (Function.extend e (fun j => Complex.I * α j) 0) =
      fun s => ∑ j, (Complex.I * α j) * blockIsometryState A (ω j) hN s :=
  mulVec_windowGHZState_of_registerCfg he hU _
