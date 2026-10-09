/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SpectatorOscillationSupport

/-!
Regression checks for the initial physical support estimate: arbitrary
spectator blocks, an empty support with a non-Hermitian spectator operator,
and an empty spectator all use the native site expectation and oscillation.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

-- An arbitrary supported physical operator can carry a non-Hermitian spectator.
example {q : ℕ} [NeZero q] {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux] (K : Finset ι) (y : ι)
    (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Matrix Aux Aux ℂ)
    (hA : A ∈ supportedOperators q (K : Set ι)) :
    siteOscillation q y (A ⊗ₖ S) ≤
      2 * ‖A ⊗ₖ S‖ * (K : Set ι).indicator (fun _ => (1 : ℝ)) y := by
  apply siteOscillation_le_support_indicator
  apply (spectatorSiteExpectation_eq_self_iff K (A ⊗ₖ S)).mp
  rw [spectatorSiteExpectation_kronecker, siteExpectation_of_mem_supportedOperators K hA]

-- Empty spectators need no witness of an inhabited spectator space.
example {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (y : ι)
    (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ) :
    spectatorSiteExpectation q K B = B ∧
      siteOscillation q y B ≤
        2 * ‖B‖ * (K : Set ι).indicator (fun _ => (1 : ℝ)) y := by
  have hB : ∀ a b : Empty, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (K : Set ι) := fun a => nomatch a
  exact ⟨(spectatorSiteExpectation_eq_self_iff K B).mpr hB,
    siteOscillation_le_support_indicator K B hB y⟩

-- Trivial physical dimension still permits arbitrary spectator blocks.
example {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux] (y : ι)
    (B : Matrix ((ι → Fin 1) × Aux) ((ι → Fin 1) × Aux) ℂ) :
    siteOscillation 1 y B = 0 := by
  apply siteOscillation_eq_zero_of_not_mem_support (∅ : Finset ι) B _ (by simp)
  intro a b
  have hblock : (Matrix.of fun σ τ => B (σ, a) (τ, b)) =
      B ((fun _ => 0), a) ((fun _ => 0), b) •
        (1 : Matrix (ι → Fin 1) (ι → Fin 1) ℂ) := by
    ext σ τ
    have hσ : σ = fun _ => 0 := Subsingleton.elim _ _
    have hτ : τ = fun _ => 0 := Subsingleton.elim _ _
    simp [hσ, hτ, Matrix.smul_apply]
  rw [hblock]
  simpa using (supportedOperators 1 (∅ : Set ι)).smul_mem
    (B ((fun _ => 0), a) ((fun _ => 0), b)) (one_mem_supportedOperators _)

private noncomputable def spectatorRaisingOperator : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single 0 1 1

private noncomputable def spectatorOnlyRaisingOperator :
    Matrix ((Unit → Fin 2) × Fin 2) ((Unit → Fin 2) × Fin 2) ℂ :=
  (1 : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) ⊗ₖ spectatorRaisingOperator

-- The concrete spectator observable is non-Hermitian on the full physical space.
example : ¬ spectatorOnlyRaisingOperator.IsHermitian := by
  intro h
  have hentry := congrArg
    (fun M => M ((fun _ => 0), 0) ((fun _ => 0), 1)) h.eq
  simp [spectatorOnlyRaisingOperator, spectatorRaisingOperator,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply] at hentry

-- Fixedness implies actual membership in the existing empty-support algebra.
example (a b : Fin 2) :
    (Matrix.of fun σ τ => spectatorOnlyRaisingOperator (σ, a) (τ, b)) ∈
      supportedOperators 2 (∅ : Set Unit) := by
  simpa using (spectatorSiteExpectation_eq_self_iff ∅ spectatorOnlyRaisingOperator).mp
    (spectatorSiteExpectation_one_kronecker ∅ spectatorRaisingOperator) a b

-- The indicator bound reduces to zero outside the empty physical support.
example : siteOscillation 2 () spectatorOnlyRaisingOperator ≤ 0 := by
  have hB := (spectatorSiteExpectation_eq_self_iff ∅ spectatorOnlyRaisingOperator).mp
    (spectatorSiteExpectation_one_kronecker ∅ spectatorRaisingOperator)
  simpa using
    siteOscillation_le_support_indicator ∅ spectatorOnlyRaisingOperator hB ()


/--
info: 'QuantumCircuit.spectatorSiteExpectation_eq_self_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.spectatorSiteExpectation_eq_self_iff


/--
info: 'QuantumCircuit.siteOscillation_eq_zero_of_not_mem_support' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_eq_zero_of_not_mem_support


/--
info: 'QuantumCircuit.siteOscillation_le_support_indicator' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_le_support_indicator
