/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteOscillation

/-!
Regression checks for physical-site oscillation with a finite spectator:
empty spectators, trivial local dimension, a non-Hermitian observable and
an arbitrary spectator-only operator all use the same operator-norm API.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

-- Empty spectators are allowed and give zero oscillation.
example {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι)
    (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ) :
    siteOscillation q y B = 0 := by
  have hB : B = 0 := Subsingleton.elim _ _
  simp [hB]

-- Trivial local dimension is allowed even with a nontrivial spectator.
example {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux] (y : ι)
    (B : Matrix ((ι → Fin 1) × Aux) ((ι → Fin 1) × Aux) ℂ) :
    siteOscillation 1 y B = 0 := by
  apply siteOscillation_eq_zero_of_commute
  intro U _
  have hU : U = U (fun _ => 0) (fun _ => 0) •
      (1 : Matrix (ι → Fin 1) (ι → Fin 1) ℂ) := by
    ext σ τ
    have hσ : σ = fun _ => 0 := Subsingleton.elim _ _
    have hτ : τ = fun _ => 0 := Subsingleton.elim _ _
    simp [hσ, hτ, Matrix.smul_apply]
  change (U ⊗ₖ 1) * B = B * (U ⊗ₖ 1)
  rw [hU]
  simp only [Matrix.smul_kronecker, Matrix.one_kronecker_one,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

-- A visibly non-Hermitian off-diagonal matrix needs no Hermiticity premise.
private noncomputable def raisingOperator :
    Matrix ((Unit → Fin 2) × Unit) ((Unit → Fin 2) × Unit) ℂ :=
  Matrix.single ((fun _ => 0), ()) ((fun _ => 1), ()) 1

example : ¬ raisingOperator.IsHermitian := by
  intro h
  have hentry := congrArg
    (fun M => M ((fun _ => 0), ()) ((fun _ => 1), ())) h.eq
  simp [raisingOperator, Matrix.conjTranspose_apply, funext_iff] at hentry

example : siteOscillation 2 () (Complex.I • raisingOperator) =
    siteOscillation 2 () raisingOperator := by
  simp

example : siteOscillation 2 () raisingOperator ≤ 2 * ‖raisingOperator‖ :=
  siteOscillation_le_two_mul_norm () raisingOperator

-- Spectator-only operators, without Hermiticity, are invisible to every site.
example {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux] (y : ι) (C : Matrix Aux Aux ℂ) :
    siteOscillation q y ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C) = 0 :=
  siteOscillation_one_kronecker y C

set_option linter.hashCommand false

/--
info: 'QuantumCircuit.siteOscillation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation

/--
info: 'QuantumCircuit.siteOscillation_bddAbove' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_bddAbove

/--
info: 'QuantumCircuit.norm_commutator_le_siteOscillation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_commutator_le_siteOscillation

/--
info: 'QuantumCircuit.norm_commutator_le_siteOscillation_right' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_commutator_le_siteOscillation_right

/--
info: 'QuantumCircuit.siteOscillation_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_nonneg

/--
info: 'QuantumCircuit.siteOscillation_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_le

/--
info: 'QuantumCircuit.siteOscillation_le_two_mul_norm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_le_two_mul_norm

/--
info: 'QuantumCircuit.siteOscillation_add_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_add_le

/--
info: 'QuantumCircuit.siteOscillation_eq_zero_of_commute' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_eq_zero_of_commute

/--
info: 'QuantumCircuit.siteOscillation_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_zero

/--
info: 'QuantumCircuit.siteOscillation_one_kronecker' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_one_kronecker

/--
info: 'QuantumCircuit.siteOscillation_smul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_smul

/--
info: 'QuantumCircuit.siteOscillation_neg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_neg

/--
info: 'QuantumCircuit.siteOscillation_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_sub_le

/--
info: 'QuantumCircuit.siteOscillation_sum_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.siteOscillation_sum_le
