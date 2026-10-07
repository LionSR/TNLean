/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.GHZSectorObstruction

/-! Regression examples for the closed-unitary GHZ sector-probability obstruction. -/

open Matrix QuantumCircuit MPSPreparation
open scoped InnerProductSpace

-- The first nonempty size covered at depth zero needs no extra state hypotheses.
example : (9 : ℝ) / 5000 ≤ 1 - ‖⟪
    (WithLp.toLp 2 (ghzState (M := 5)
      ![2 / (Real.sqrt 5 : ℂ), 1 / (Real.sqrt 5 : ℂ)]) :
        EuclideanSpace ℂ (Fin 5 → Fin 2)),
    WithLp.toLp 2 (ghzState (M := 5) ![Complex.invSqrtTwo, Complex.invSqrtTwo])⟫_ℂ‖ := by
  have hU : IsLocalCircuitOfDepth (1 : Matrix (Fin 5 → Fin 2) (Fin 5 → Fin 2) ℂ) 0 :=
    ⟨[], rfl, rfl⟩
  simpa using ghz_sector_weight_infidelity_lower_bound hU (by norm_num)

-- Arbitrary one-layer gates, including a wrap-around bond, are covered on nine sites.
example (L : Layer 2 9) : (9 : ℝ) / 5000 ≤ 1 - ‖⟪
    (WithLp.toLp 2 (L.op *ᵥ ghzState (M := 9)
      ![2 / (Real.sqrt 5 : ℂ), 1 / (Real.sqrt 5 : ℂ)]) :
        EuclideanSpace ℂ (Fin 9 → Fin 2)),
    WithLp.toLp 2 (ghzState (M := 9) ![Complex.invSqrtTwo, Complex.invSqrtTwo])⟫_ℂ‖ := by
  have hU : IsLocalCircuitOfDepth L.op 1 := ⟨[L], rfl, by simp [circuitOp]⟩
  exact ghz_sector_weight_infidelity_lower_bound hU (by norm_num)

-- Phase alignment is harmless: it changes neither a one-point expectation nor the covariance.
example {N : ℕ} (c : ℂ) (hc : ‖c‖ = 1) (a b : ℂ)
    (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    expect (c • ghzState (M := N) ![a, b]) A = expect (ghzState (M := N) ![a, b]) A :=
  expect_smul_state hc _ _

-- A branch label differing off the support kills the matrix element, without normalization.
example {N : ℕ} {S : Set (Fin N)} (i : Fin N) (hi : i ∉ S)
    (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (hA : A ∈ supportedOperators 2 S) : A (fun _ => 0) (fun _ => 1) = 0 :=
  apply_eq_zero_of_mem_supportedOperators hA ⟨i, hi, by decide⟩

-- Norms retain arbitrary complex phases rather than assuming positive amplitudes.
example : ‖(WithLp.toLp 2 (ghzState (M := 5) ![Complex.I, 0]) :
    EuclideanSpace ℂ (Fin 5 → Fin 2))‖ ^ 2 = 1 := by
  simpa using norm_ghzState_two_sq (N := 5) Complex.I 0

-- Rescaling acts on both coefficients, including on the empty-chain convention.
example (N : ℕ) (c a b : ℂ) : c • ghzState (M := N) ![a, b] =
    ghzState (M := N) ![c * a, c * b] := ghzState_smul_two c a b
