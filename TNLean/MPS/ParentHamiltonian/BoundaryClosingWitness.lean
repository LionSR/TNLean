/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryOverlap
import TNLean.MPS.ParentHamiltonian.WrappingWindow

/-!
# Boundary-crossing witness comparisons for the closure property

Coordinate identities saying that outside configurations with the same labels on
the sites outside a cyclic window determine the same boundary-crossing witness.
These are the witness-independence facts needed to choose a representative
outside configuration for the coordinate comparison used when closing the
periodic boundary.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Equal cyclic restrictions give the same products after one fixed physical
letter:
\[
  Y_1 A^j = Y_2 A^j .
\]

The conclusion is at length \(L\), where block injectivity makes \(\Gamma_L\)
injective; no uniqueness is claimed for the longer $(L+1)$-site matrices
themselves. -/
theorem cyclicRestrictₗ_first_products_eq_of_restriction_eq
    {A : MPSTensor d D} {N L : ℕ} (hInj : IsNBlkInjective A L)
    (hN : 0 < N) (hLN : L + 1 ≤ N)
    (i : Fin N) (τ₁ τ₂ : Fin N → Fin d) (ψ : NSiteSpace d N)
    {Y₁ Y₂ : Matrix (Fin D) (Fin D) ℂ}
    (hY₁ : cyclicRestrictₗ hN (L + 1) i τ₁ ψ = groundSpaceMap A (L + 1) Y₁)
    (hY₂ : cyclicRestrictₗ hN (L + 1) i τ₂ ψ = groundSpaceMap A (L + 1) Y₂)
    (heq : cyclicRestrictₗ hN (L + 1) i τ₁ ψ =
      cyclicRestrictₗ hN (L + 1) i τ₂ ψ) :
    ∀ j : Fin d, Y₁ * A j = Y₂ * A j := by
  intro j
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  have hfirst :
      restrictFirst (cyclicRestrictₗ hN (L + 1) i τ₁ ψ) j =
        restrictFirst (cyclicRestrictₗ hN (L + 1) i τ₂ ψ) j := by
    rw [heq]
  rw [cyclicRestrictₗ_restrictFirst hN hLN i τ₁ ψ j,
    cyclicRestrictₗ_restrictFirst hN hLN i τ₂ ψ j] at hfirst
  have hleft :=
    cyclicRestrictₗ_restrictFirst_groundSpaceMap
      (A := A) hN hLN i τ₁ ψ hY₁ j
  have hright :=
    cyclicRestrictₗ_restrictFirst_groundSpaceMap
      (A := A) hN hLN i τ₂ ψ hY₂ j
  exact hleft.symm.trans (hfirst.trans hright)

/-- For the boundary-crossing interval starting at the last site, any outside
configuration with the same word on the sites outside the window gives the same
restriction as the local coordinate configuration \(\tau^+_\eta(\mu)\) used here
for a coordinate form of the closure property. -/
theorem cyclicRestrictₗ_wrappedMiddleBackground_eq_of_complement_eq
    {L₀ M : ℕ} (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} (η : Fin d)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) (ρ : Fin (M + 1) → Fin d)
    (hρ : ∀ k : Fin (M + 1 - (L₀ + 1)),
      ρ ⟨k.val + L₀, by omega⟩ = μ k) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M, by omega⟩ : Fin (M + 1)) ρ ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M, by omega⟩ : Fin (M + 1))
        (wrappedMiddleBackground L₀ (M + 1) η μ) ψ := by
  apply cyclicRestrictₗ_congr_outside
  intro k hkout
  have hk_ne_last : k.val ≠ M := by
    intro hkM
    apply hkout
    rw [hkM]
    have hsum : M + (M + 1) - M = M + 1 := by omega
    rw [hsum, Nat.mod_self]
    omega
  have hk_lt_last : k.val < M := by omega
  have hoff : (k.val + (M + 1) - M) % (M + 1) = k.val + 1 := by
    have hsum : k.val + (M + 1) - M = k.val + 1 := by omega
    rw [hsum]
    exact Nat.mod_eq_of_lt (by omega)
  have hkL : L₀ ≤ k.val := by
    by_contra hkL
    push Not at hkL
    apply hkout
    rw [hoff]
    omega
  rw [wrappedMiddleBackground, dif_pos ⟨hkL, hk_lt_last⟩]
  let r : Fin (M + 1 - (L₀ + 1)) := ⟨k.val - L₀, by omega⟩
  have hrho := hρ r
  have hsite : (⟨r.val + L₀, by omega⟩ : Fin (M + 1)) = k := by
    ext
    simp [r]
    omega
  rwa [hsite] at hrho

/-- Matrix consequence at the last-site boundary-crossing support. If an
outside configuration has the same word on the sites outside the window as
\(\tau^+_\eta(\mu)\), then
\[
  Y_\rho A^j = Y_{\tau^+_\eta(\mu)} A^j .
\] -/
theorem wrappedMiddleBackground_first_products_eq_of_complement_eq
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
    ∀ j : Fin d, Yρ * A j = Yτ * A j := by
  exact cyclicRestrictₗ_first_products_eq_of_restriction_eq
    (A := A) hInj (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (⟨M, by omega⟩ : Fin (M + 1)) ρ (wrappedMiddleBackground L₀ (M + 1) η μ) ψ
    hYρ hYτ
    (cyclicRestrictₗ_wrappedMiddleBackground_eq_of_complement_eq
      hL₀ hM η μ ρ hρ)

/-- Witness uniqueness at the last-site boundary-crossing support.

If an outside configuration has the same word on the sites outside the window
as the local coordinate configuration \(\tau^+_\eta(\mu)\), then the two
matrices representing the last-site restriction are equal. This is the
last-site witness-independence step for the periodic-boundary coordinate
comparison. -/
theorem wrappedMiddleBackground_witness_eq_of_complement_eq
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
    Yρ = Yτ :=
  right_witness_unique_of_isNBlkInjective hInj hL₀
    (wrappedMiddleBackground_first_products_eq_of_complement_eq
      (A := A) hInj hL₀ hM η μ ρ hρ hYρ hYτ)

/-- For the second boundary-crossing interval, any outside configuration with
the same word on the sites outside the window gives the same restriction as the
local coordinate configuration \(\tau^-_\eta(\mu)\) used here for a coordinate
form of the closure property. -/
theorem cyclicRestrictₗ_mirrorMiddleBackground_eq_of_complement_eq
    {L₀ M : ℕ} (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} (η : Fin d)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) (ρ : Fin (M + 1) → Fin d)
    (hρ : ∀ k : Fin (M + 1 - (L₀ + 1)),
      ρ ⟨k.val + 1, by omega⟩ = μ k) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) ρ ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
        (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  apply cyclicRestrictₗ_congr_outside
  intro k hkout
  have hk_pos : 1 ≤ k.val := by
    by_contra hkpos
    push Not at hkpos
    have hk0 : k.val = 0 := by omega
    apply hkout
    rw [hk0]
    have hsum : 0 + (M + 1) - (M + 1 - L₀) = L₀ := by omega
    rw [hsum, Nat.mod_eq_of_lt (by omega : L₀ < M + 1)]
    omega
  have hk_lt : k.val < M + 1 - L₀ := by
    by_contra hklt
    push Not at hklt
    apply hkout
    have hsum :
        k.val + (M + 1) - (M + 1 - L₀) = k.val + L₀ := by
      omega
    rw [hsum]
    have hsplit : k.val + L₀ = (M + 1) + (k.val + L₀ - (M + 1)) := by
      omega
    rw [hsplit, Nat.add_mod_left]
    rw [Nat.mod_eq_of_lt (by omega : k.val + L₀ - (M + 1) < M + 1)]
    omega
  rw [mirrorMiddleBackground, dif_pos ⟨hk_pos, hk_lt⟩]
  let r : Fin (M + 1 - (L₀ + 1)) := ⟨k.val - 1, by omega⟩
  have hrho := hρ r
  have hsite : (⟨r.val + 1, by omega⟩ : Fin (M + 1)) = k := by
    ext
    simp [r]
    omega
  rwa [hsite] at hrho

/-- Matrix consequence at the second boundary-crossing support. If an
outside configuration has the same word on the sites outside the window as
\(\tau^-_\eta(\mu)\), then
\[
  Y_\rho A^j = Y_{\tau^-_\eta(\mu)} A^j .
\] -/
theorem mirrorMiddleBackground_first_products_eq_of_complement_eq
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
    ∀ j : Fin d, Yρ * A j = Yτ * A j := by
  exact cyclicRestrictₗ_first_products_eq_of_restriction_eq
    (A := A) hInj (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) ρ
    (mirrorMiddleBackground L₀ (M + 1) η μ) ψ hYρ hYτ
    (cyclicRestrictₗ_mirrorMiddleBackground_eq_of_complement_eq
      hL₀ hM η μ ρ hρ)

/-- Witness uniqueness at the second boundary-crossing support.

If an outside configuration has the same word on the sites outside the window
as the local coordinate configuration \(\tau^-_\eta(\mu)\), then the two
matrices representing the second boundary-crossing restriction are equal. This
is the second-window witness-independence step for the periodic-boundary
coordinate comparison. -/
theorem mirrorMiddleBackground_witness_eq_of_complement_eq
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
    Yρ = Yτ :=
  right_witness_unique_of_isNBlkInjective hInj hL₀
    (mirrorMiddleBackground_first_products_eq_of_complement_eq
      (A := A) hInj hL₀ hM η μ ρ hρ hYρ hYτ)

end MPSTensor
