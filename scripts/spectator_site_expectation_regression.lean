/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SpectatorSiteExpectation

/-!
# Spectator site-expectation regressions

Run after building `TNLean.Circuit.SpectatorSiteExpectation`:
`lake env lean scripts/spectator_site_expectation_regression.lean`.

A nonmaximally entangled input distinguishes physical-only averaging from
accidental averaging of the spectator. The other consumers cover arbitrary
non-Hermitian spectator operators, all sites retained, local dimension one,
and an empty spectator index type.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace SpectatorSiteExpectationRegression

private instance : Unique {x : Unit // x ∉ (∅ : Finset Unit)} where
  default := ⟨(), by simp⟩
  uniq x := Subtype.ext (Subsingleton.elim _ _)

private theorem sum_empty_complement (f : ({x : Unit // x ∉ (∅ : Finset Unit)} → Fin 2) → ℂ) :
    ∑ ρ, f ρ = f (fun _ => 0) + f (fun _ => 1) := by
  rw [← (Equiv.funUnique {x : Unit // x ∉ (∅ : Finset Unit)} (Fin 2)).symm.sum_comp]
  rw [Fin.sum_univ_two]
  rfl

/-- The unnormalized vector `|00⟩ + 2 |11⟩`. -/
private def entangled (x : (Unit → Fin 2) × Fin 2) : ℂ :=
  if x.1 () = x.2 then if x.2 = 0 then 1 else 2 else 0

-- The spectator marginal is diag(1,4), rather than a scalar multiple of its identity.
example :
    spectatorSiteExpectation 2 (∅ : Finset Unit) (vecMulVec entangled (star entangled)) =
      (1 : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) ⊗ₖ
        diagonal ![(1 / 2 : ℂ), 2] := by
  ext ⟨σ, a⟩ ⟨τ, b⟩
  rw [spectatorSiteExpectation_apply, ManyBody.regionExpectation_apply]
  have hcard : Fintype.card (ManyBody.ComplConfig (fun _ : Unit => Fin 2) ∅) = 2 := by
    simp [ManyBody.ComplConfig]
  have hglue (ρ : Unit → Fin 2) (y : ManyBody.ComplConfig (fun _ : Unit => Fin 2) ∅) :
      (ManyBody.cutEquiv (fun _ : Unit => Fin 2) ∅).symm
          ((ManyBody.cutEquiv (fun _ : Unit => Fin 2) ∅ ρ).1, y) =
        fun _ => y ⟨(), Finset.notMem_empty ()⟩ := by
    funext x
    exact ManyBody.cutEquiv_symm_apply_not_mem _ _ (Finset.notMem_empty x)
  have hagree : (∀ v ∉ (∅ : Finset Unit), σ v = τ v) ↔ σ = τ :=
    ⟨fun h => funext fun v => h v (Finset.notMem_empty v), fun h v _ => h ▸ rfl⟩
  simp only [hcard, hglue, hagree, Matrix.of_apply]
  rw [sum_empty_complement]
  simp only [Matrix.vecMulVec_apply, Pi.star_apply]
  fin_cases a <;> fin_cases b <;>
    simp [entangled, Matrix.kroneckerMap_apply, Matrix.one_apply]

-- No Hermiticity hypothesis is allowed for the spectator factor.
example {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι] [Fintype Aux] [DecidableEq Aux]
    (K : Finset ι) (S : Matrix Aux Aux ℂ) :
    spectatorSiteExpectation q K ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S) =
      (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S :=
  spectatorSiteExpectation_one_kronecker K S

-- This concrete off-diagonal spectator matrix is non-Hermitian.
example :
    spectatorSiteExpectation 2 (∅ : Finset Unit)
      ((1 : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) ⊗ₖ
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) =
      (1 : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) ⊗ₖ !![0, 1; 0, 0] := by
  simp

example (B : Matrix ((Unit → Fin 2) × Fin 2) ((Unit → Fin 2) × Fin 2) ℂ) :
    spectatorSiteExpectation 2 Finset.univ B = B :=
  spectatorSiteExpectation_univ B

-- With local dimension one, even averaging every physical site is the identity.
example {ι Aux : Type*} [Fintype ι] [DecidableEq ι] [Fintype Aux] [DecidableEq Aux]
    (K : Finset ι) (B : Matrix ((ι → Fin 1) × Aux) ((ι → Fin 1) × Aux) ℂ) :
    spectatorSiteExpectation 1 K B = B := by
  let S : Matrix Aux Aux ℂ := Matrix.of fun a b => B (default, a) (default, b)
  have hB : B = (1 : Matrix (ι → Fin 1) (ι → Fin 1) ℂ) ⊗ₖ S := by
    ext ⟨σ, a⟩ ⟨τ, b⟩
    have hσ : σ = default := Subsingleton.elim _ _
    have hτ : τ = default := Subsingleton.elim _ _
    simp [hσ, hτ, Matrix.kroneckerMap_apply, S]
  rw [hB, spectatorSiteExpectation_one_kronecker]

-- The contraction theorem imposes no nonemptiness condition on spectators.
example (B : Matrix ((Unit → Fin 2) × Fin 0) ((Unit → Fin 2) × Fin 0) ℂ) :
    ‖spectatorSiteExpectation 2 (∅ : Finset Unit) B‖ ≤ ‖B‖ :=
  norm_spectatorSiteExpectation_le _ B

example (B : Matrix ((Unit → Fin 2) × Fin 0) ((Unit → Fin 2) × Fin 0) ℂ) :
    spectatorSiteExpectation 2 (∅ : Finset Unit) B = B := by
  ext ⟨_, a⟩
  exact Fin.elim0 a

section AxiomChecks


/--
info: 'QuantumCircuit.spectatorSiteExpectation'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorSiteExpectation
/--
info: 'QuantumCircuit.spectatorSiteExpectation_kronecker'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorSiteExpectation_kronecker
/--
info: 'QuantumCircuit.spectatorSiteExpectation_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorSiteExpectation_commute
/--
info: 'QuantumCircuit.spectatorSiteExpectation_one_kronecker'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorSiteExpectation_one_kronecker
/--
info: 'QuantumCircuit.spectatorSiteExpectation_univ'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorSiteExpectation_univ
/--
info: 'QuantumCircuit.norm_spectatorSiteExpectation_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_spectatorSiteExpectation_le
/--
info: 'QuantumCircuit.norm_sub_spectatorSiteExpectation_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_sub_spectatorSiteExpectation_le

end AxiomChecks

end SpectatorSiteExpectationRegression
