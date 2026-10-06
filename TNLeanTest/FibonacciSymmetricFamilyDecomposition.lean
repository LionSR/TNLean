/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciSymmetricFamilyDecomposition

/-!+# Regressions for unrestricted physical Fibonacci actions

The concrete Fibonacci MPO consumer has no bound on the number of state blocks.
The three-block test is excluded by parity, the empty family remains admissible,
and a nonunital one-block NIM-representation checks the necessity of the unit premise.
-/

open scoped Matrix

open MPSTensor MPOTensor FibonacciCompression

namespace FibonacciSymmetricFamilyDecompositionTest

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

-- The actual Fibonacci operator family, with arbitrary many normal state blocks.
example {D : κ → ℕ} {A : ∀ x, MPSTensor 2 (D x)} {M : Fin 2 → κ → κ → ℂ}
    (hsym : IsMPOSymmetricFamily fibBlock A M)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x ↦ fun σ : Fin L₀ → Fin 2 ↦ mpv (A x) σ)
    (hunit : ∀ x, mpo (fibBlock 0) L₀ *ᵥ (fun σ ↦ mpv (A x) σ) =
      fun σ ↦ mpv (A x) σ) :
    Even (Fintype.card κ) ∧
      ∃ σ : κ ≃ {x // M 1 x x = 0} × Fin 2, ∀ a x y,
        M a x y = if (σ x).1 = (σ y).1 then
          (fibNim a (σ x).2 (σ y).2 : ℂ) else 0 :=
  exists_equiv_prod_of_isMPOSymmetricFamily_fibNim
    isMPOFusionAlgebra_fibBlock hsym hA hD hL₀ hli hunit

-- This rules out a rank beyond the previous rank-at-most-two consumer.
example {D : Fin 3 → ℕ} {A : ∀ x, MPSTensor 2 (D x)}
    {M : Fin 2 → Fin 3 → Fin 3 → ℂ}
    (hsym : IsMPOSymmetricFamily fibBlock A M)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x ↦ fun σ : Fin L₀ → Fin 2 ↦ mpv (A x) σ)
    (hunit : ∀ x, mpo (fibBlock 0) L₀ *ᵥ (fun σ ↦ mpv (A x) σ) =
      fun σ ↦ mpv (A x) σ) : False := by
  have heven := (exists_equiv_prod_of_isMPOSymmetricFamily_fibNim
    isMPOFusionAlgebra_fibBlock hsym hA hD hL₀ hli hunit).1
  norm_num at heven

-- Empty physical families satisfy the same theorem without a nonemptiness premise.
example (A : Fin 0 → MPSTensor 2 1) :
    Even (Fintype.card (Fin 0)) ∧
      ∃ σ : Fin 0 ≃ {x : Fin 0 // (0 : ℂ) = 0} × Fin 2, ∀ a x y,
        (0 : ℂ) = if (σ x).1 = (σ y).1 then
          (fibNim a (σ x).2 (σ y).2 : ℂ) else 0 :=
  exists_equiv_prod_of_isMPOSymmetricFamily_fibNim
    (A := A) (M := fun _ _ _ ↦ 0) isMPOFusionAlgebra_fibBlock
    (fun _ x ↦ Fin.elim0 x) (fun x ↦ Fin.elim0 x) (fun x ↦ Fin.elim0 x)
    (L₀ := 1) (by decide) linearIndependent_empty_type (fun x ↦ Fin.elim0 x)

-- The fusion law alone allows this odd-dimensional, nonunital representation.
example : IsNIMRep fibNim (fun (_ : Fin 2) (_ _ : Fin 1) ↦ 0) := by
  intro a b x y
  simp

example : ¬ ∀ x y : Fin 1, (0 : ℕ) = if x = y then 1 else 0 := by
  intro h
  have h00 := h 0 0
  simp at h00

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'FibonacciCompression.exists_equiv_prod_of_isMPOSymmetricFamily_fibNim'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FibonacciCompression.exists_equiv_prod_of_isMPOSymmetricFamily_fibNim

end AxiomChecks

end FibonacciSymmetricFamilyDecompositionTest
