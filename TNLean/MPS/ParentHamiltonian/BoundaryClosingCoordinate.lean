/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryClosing

/-!
# Coordinate consequences for closing the parent-Hamiltonian boundary

This file contains formula-level consequences of the boundary-condition
comparison lemmas in `BoundaryClosing`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The last-boundary first-product equation remains true after right
multiplication by any length-\(L_0\) word:
\[
  Y_\rho A^j A^\sigma =
  Y_{\tau^+_\eta(\mu)} A^j A^\sigma .
\] -/
theorem wrappedMiddleBackground_first_products_eq_of_complement_eq_right_word
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} (η : Fin d)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) (ρ : Fin (M + 1) → Fin d)
    {Yρ Yτ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ∀ k : Fin (M + 1 - (L₀ + 1)),
      ρ ⟨k.val + L₀, by omega⟩ = μ k)
    (hYρ : cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M, by omega⟩ : Fin (M + 1)) ρ ψ =
      groundSpaceMap A (L₀ + 1) Yρ)
    (hYτ : cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M, by omega⟩ : Fin (M + 1))
        (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      groundSpaceMap A (L₀ + 1) Yτ) :
    ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
      Yρ * A j * evalWord A (List.ofFn σ) =
        Yτ * A j * evalWord A (List.ofFn σ) := by
  intro j σ
  exact congrArg (fun Y => Y * evalWord A (List.ofFn σ))
    (wrappedMiddleBackground_first_products_eq_of_complement_eq
      (A := A) hInj hL₀ hM η μ ρ hρ hYρ hYτ j)

/-- The opposite-boundary first-product equation remains true after right
multiplication by any length-\(L_0\) word:
\[
  Y_\rho A^j A^\sigma =
  Y_{\tau^-_\eta(\mu)} A^j A^\sigma .
\] -/
theorem mirrorMiddleBackground_first_products_eq_of_complement_eq_right_word
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} (η : Fin d)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) (ρ : Fin (M + 1) → Fin d)
    {Yρ Yτ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ∀ k : Fin (M + 1 - (L₀ + 1)),
      ρ ⟨k.val + 1, by omega⟩ = μ k)
    (hYρ : cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) ρ ψ =
      groundSpaceMap A (L₀ + 1) Yρ)
    (hYτ : cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
        (mirrorMiddleBackground L₀ (M + 1) η μ) ψ =
      groundSpaceMap A (L₀ + 1) Yτ) :
    ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
      Yρ * A j * evalWord A (List.ofFn σ) =
        Yτ * A j * evalWord A (List.ofFn σ) := by
  intro j σ
  exact congrArg (fun Y => Y * evalWord A (List.ofFn σ))
    (mirrorMiddleBackground_first_products_eq_of_complement_eq
      (A := A) hInj hL₀ hM η μ ρ hρ hYρ hYτ j)

/-- The fixed-boundary-condition product equation after right multiplication
by an arbitrary matrix. -/
lemma closure_property_boundary_condition_product_of_window_witnesses_mul_right
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (ρ : Fin (M + 1) → Fin d) (R : Matrix (Fin D) (Fin D) ℂ) :
    YAt ⟨M + 1 - L₀, by omega⟩ ρ *
        evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
          ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) * R =
      evalWord A (List.ofFn (fun r : Fin (L₀ - 1) => ρ ⟨r.val + 1, by omega⟩)) *
        YAt ⟨M, by omega⟩ ρ * R := by
  exact congrArg (fun Y => Y * R)
    (closure_property_boundary_condition_product_of_window_witnesses
      (A := A) hInj hL₀ hM YAt hYAt ρ)

end MPSTensor
