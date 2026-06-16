/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryClosing

/-!
# Coordinate consequences for the periodic-boundary comparison

This file contains formula-level consequences of the boundary-condition
comparison lemmas in `BoundaryClosing`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The first-product equation for the boundary-crossing window beginning at
\(M\) remains true after right
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

/-- The first-product equation for the second boundary-crossing window remains
true after right multiplication by any length-\(L_0\) word:
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

/-- The fixed-boundary-condition product equation remains true after right
multiplication by an arbitrary matrix:
\[
  Y_{M+1-L_0}(\rho)A^{\rho_{M+1-L_0}}\cdots A^{\rho_{M-1}}R
  =
  A^{\rho_1}\cdots A^{\rho_{L_0-1}}Y_M(\rho)R .
\] -/
theorem closure_property_boundary_condition_product_of_window_witnesses_mul_right
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

/-- Adjacent-window transport followed by the one-sided equation at the window
beginning at \(M\).

For a boundary condition \(\rho\), the adjacent windows from \(M+1-L_0\) to
\(M\) give
\[
  Y_{M+1-L_0}(\rho) A^{\rho_{M+1-L_0}\cdots\rho_{M-1}}
  =
  A^{\rho_1\cdots\rho_{L_0-1}}Y_M(\rho).
\]
Multiplying by \(A^j\) and using the one-sided equation for the window beginning
at \(M\), for
\(\psi=\Gamma_{M+1}(X)\) gives the displayed formula below.  This is the
transport identity supplied by the adjacent-window argument; for
\(\rho=\tau^-_\eta(\mu)\) it is distinct from the remaining padded identity
in the periodic-boundary comparison. -/
theorem closure_property_boundary_condition_transport_wrapped_product_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (ρ : Fin (M + 1) → Fin d) (j : Fin d) :
    YAt ⟨M + 1 - L₀, by omega⟩ ρ *
        evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
          ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) * A j =
      evalWord A (List.ofFn (fun r : Fin (L₀ - 1) => ρ ⟨r.val + 1, by omega⟩)) *
        (evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
          ρ ⟨k.val + L₀, by omega⟩)) * A j * X) := by
  have htransport :=
    closure_property_boundary_condition_product_of_window_witnesses_mul_right
      (A := A) hInj hL₀ hM YAt hYAt ρ (A j)
  have hwrapped :=
    (closure_property_wrapped_mirror_compatibilities_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt).1 j ρ
  calc
    YAt ⟨M + 1 - L₀, by omega⟩ ρ *
          evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
            ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) * A j
        = evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
            ρ ⟨r.val + 1, by omega⟩)) * YAt ⟨M, by omega⟩ ρ * A j := htransport
    _ = evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
            ρ ⟨r.val + 1, by omega⟩)) * (YAt ⟨M, by omega⟩ ρ * A j) := by
          rw [Matrix.mul_assoc]
    _ = evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
            ρ ⟨r.val + 1, by omega⟩)) *
          (evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            ρ ⟨k.val + L₀, by omega⟩)) * A j * X) := by
          rw [← hwrapped]

end MPSTensor
