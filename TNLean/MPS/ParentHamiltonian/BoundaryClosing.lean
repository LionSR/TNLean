/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryOverlap
import TNLean.MPS.ParentHamiltonian.WrappingWindow

/-!
# Boundary assignments for the closure property

This file records elementary coordinate facts for the two boundary-crossing
supports used in the closure property of the normal parent-Hamiltonian
argument.
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
configuration with the same complementary word gives the same restriction as the
boundary assignment \(\tau^+_\eta(\mu)\) used in the closure property. -/
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

/-- Matrix consequence at the last-site boundary-crossing support.  If an
outside configuration has the same complementary word as
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

/-- For the opposite boundary-crossing interval, any outside configuration with
the same complementary word gives the same restriction as the boundary
assignment \(\tau^-_\eta(\mu)\) used in the closure property. -/
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

/-- Matrix consequence at the opposite boundary-crossing support.  If an
outside configuration has the same complementary word as
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

/-- Pointwise complement reduction for the boundary-closing product equation.

The auxiliary boundary assignments may depend on the fixed physical letter and
the length-\(L_0\) word. If, for each pair \(j,\sigma\), the assignments
\(\rho^+_{j,\sigma}\) and \(\rho^-_{j,\sigma}\) carry the same complementary
word as \(\tau^+_\eta(\mu)\) and \(\tau^-_\eta(\mu)\), respectively, then a
product equation for those auxiliary assignments gives the corresponding
canonical boundary-assignment equation:
\[
  Y_M(\tau^+_\eta(\mu)) A^j A^\sigma
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu)) A^j A^\sigma .
\] -/
theorem boundary_closing_product_eq_of_pointwise_compatible_boundary_assignments
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (ρPlus ρMinus :
      (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d)
    (hρPlus : ∀ (j : Fin d) (σ : Fin L₀ → Fin d)
        (k : Fin (M + 1 - (L₀ + 1))),
      ρPlus j σ ⟨k.val + L₀, by omega⟩ = μ k)
    (hρMinus : ∀ (j : Fin d) (σ : Fin L₀ → Fin d)
        (k : Fin (M + 1 - (L₀ + 1))),
      ρMinus j σ ⟨k.val + 1, by omega⟩ = μ k)
    (hProductEq : ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M, by omega⟩ (ρPlus j σ) * A j * evalWord A (List.ofFn σ) =
        YAt ⟨M + 1 - L₀, by omega⟩ (ρMinus j σ) * A j *
          evalWord A (List.ofFn σ)) :
    ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) =
        YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) := by
  intro j σ
  have hwrap := wrappedMiddleBackground_first_products_eq_of_complement_eq
    (A := A) hInj hL₀ hM η μ (ρPlus j σ) (hρPlus j σ)
    (hYAt ⟨M, by omega⟩ (ρPlus j σ))
    (hYAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ)) j
  have hmirror := mirrorMiddleBackground_first_products_eq_of_complement_eq
    (A := A) hInj hL₀ hM η μ (ρMinus j σ) (hρMinus j σ)
    (hYAt ⟨M + 1 - L₀, by omega⟩ (ρMinus j σ))
    (hYAt ⟨M + 1 - L₀, by omega⟩
      (mirrorMiddleBackground L₀ (M + 1) η μ)) j
  calc
    YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ)
        = YAt ⟨M, by omega⟩ (ρPlus j σ) * A j *
          evalWord A (List.ofFn σ) := by
            rw [← hwrap]
    _ = YAt ⟨M + 1 - L₀, by omega⟩ (ρMinus j σ) * A j *
          evalWord A (List.ofFn σ) :=
            hProductEq j σ
    _ = YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) := by
            rw [hmirror]

/-- Complement reduction for the boundary-closing product equation.

Suppose two auxiliary outside assignments have the same complementary words as
\(\tau^+_\eta(\mu)\) and \(\tau^-_\eta(\mu)\), respectively.  If the desired
product equation has already been proved for those two assignments, then it also
holds for the canonical boundary assignments:
\[
  Y_M(\tau^+_\eta(\mu)) A^j A^\sigma
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu)) A^j A^\sigma .
\]

This isolates the remaining closure-property task as an adjacent-window product
identity between compatible outside assignments. -/
theorem boundary_closing_product_eq_of_compatible_backgrounds
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (ρPlus ρMinus : Fin (M + 1) → Fin d)
    (hρPlus : ∀ k : Fin (M + 1 - (L₀ + 1)),
      ρPlus ⟨k.val + L₀, by omega⟩ = μ k)
    (hρMinus : ∀ k : Fin (M + 1 - (L₀ + 1)),
      ρMinus ⟨k.val + 1, by omega⟩ = μ k)
    (htransport : ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M, by omega⟩ ρPlus * A j * evalWord A (List.ofFn σ) =
        YAt ⟨M + 1 - L₀, by omega⟩ ρMinus * A j * evalWord A (List.ofFn σ)) :
    ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) =
        YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) := by
  exact boundary_closing_product_eq_of_pointwise_compatible_boundary_assignments
    (A := A) hInj hL₀ hM YAt hYAt η μ
    (fun _ _ => ρPlus) (fun _ _ => ρMinus)
    (by intro _ _ k; exact hρPlus k)
    (by intro _ _ k; exact hρMinus k)
    (by intro j σ; exact htransport j σ)

/-- The two one-sided equations obtained from the boundary-crossing cyclic
windows.

Assume \(\psi=\Gamma_{M+1}(X)\), and suppose \(Y_i(\tau)\) represents the
length-\((L_0+1)\) cyclic restriction of \(\psi\) beginning at \(i\).  Then the
two boundary-crossing positions give, for every physical letter \(j\) and
boundary condition \(\tau\),
\[
  A^{\tau_{L_0}\cdots\tau_{M-1}} A^j X = Y_M(\tau) A^j,
  \qquad
  X A^j A^{\tau_1\cdots\tau_{M-L_0}} = A^j Y_{M+1-L_0}(\tau).
\]

This is the one-sided part of the closure-property argument in
arXiv:2011.12127, Section IV.C, lines 2078--2090. -/
theorem closure_property_wrapped_mirror_compatibilities_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ)) :
    (∀ (j : Fin d) (τ : Fin (M + 1) → Fin d),
      evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
        τ ⟨k.val + L₀, by omega⟩)) * A j * X =
          YAt ⟨M, by omega⟩ τ * A j) ∧
    (∀ (j : Fin d) (τ : Fin (M + 1) → Fin d),
      X * A j * evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
        τ ⟨k.val + 1, by omega⟩)) =
          A j * YAt ⟨M + 1 - L₀, by omega⟩ τ) := by
  constructor
  · exact wrapping_window_compatibility_of_isNBlkInjective
      (A := A) hInj hL₀ hM (YAt ⟨M, by omega⟩)
      (fun τ σ_w => by
        simpa [groundSpaceMap_apply, cyclicRestrictₗ_apply, hψX]
          using congr_fun (hYAt ⟨M, by omega⟩ τ) σ_w)
  · exact wrapping_window_mirror_compatibility_of_isNBlkInjective
      (A := A) hInj hL₀ hM (YAt ⟨M + 1 - L₀, by omega⟩)
      (fun τ σ_w => by
        simpa [groundSpaceMap_apply, cyclicRestrictₗ_apply, hψX]
          using congr_fun (hYAt ⟨M + 1 - L₀, by omega⟩ τ) σ_w)

/-- Product form of the boundary-crossing restrictions at the closing boundary.

For the \(L_0-1\) adjacent restrictions from \(M+1-L_0\) to \(M\), the two
boundary letters are indexed by
\[
  M+1-L_0+r,
  \qquad
  M+1-L_0+r+L_0+1 \equiv r+1 \pmod {M+1}.
\]
Thus the iterated product equation is
\[
  Y_0(\rho)\,
  A^{\rho_{M+1-L_0}\cdots \rho_{M-1}}
  =
  A^{\rho_1\cdots\rho_{L_0-1}}\,Y_{L_0-1}(\rho).
\]
For \(L_0=1\) both products are empty.

This is the product form of the closure-property step in arXiv:2011.12127,
Section IV.C, lines 2078--2090. -/
theorem boundary_closing_endpoint_word_products_common_background
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} (ρ : Fin (M + 1) → Fin d)
    (Y : Fin ((L₀ - 1) + 1) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ r : Fin ((L₀ - 1) + 1),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (cyclicForwardSite (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) r.val) ρ ψ =
        groundSpaceMap A (L₀ + 1) (Y r)) :
    Y 0 * evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
        ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) =
      evalWord A (List.ofFn (fun r : Fin (L₀ - 1) => ρ ⟨r.val + 1, by omega⟩)) *
        Y (Fin.last (L₀ - 1)) := by
  refine adjacent_cyclicRestrictₗ_witness_product_common_background_named
    (A := A) hInj (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) ρ ψ Y
    (fun r : Fin (L₀ - 1) => ρ ⟨M + 1 - L₀ + r.val, by omega⟩)
    (fun r : Fin (L₀ - 1) => ρ ⟨r.val + 1, by omega⟩) hY ?_ ?_
  · ext r
    have hsite :
        cyclicForwardSite (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) r.val =
          ⟨M + 1 - L₀ + r.val, by omega⟩ := by
      ext
      simp only [cyclicForwardSite, Fin.val_mk]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hsite]
  · ext r
    have hsite :
        cyclicForwardSite
            (cyclicForwardSite (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) r.val)
            (L₀ + 1) =
          ⟨r.val + 1, by omega⟩ := by
      ext
      simp only [cyclicForwardSite, Fin.val_mk]
      have hsum : ((M + 1 - L₀ + r.val) % (M + 1)) + (L₀ + 1) =
          M + 1 + (r.val + 1) := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsite]

/-- Product equation obtained by moving through the \(L_0-1\) boundary-crossing
windows from \(M+1-L_0\) to \(M\).

For a fixed boundary condition \(\rho\), the window matrices satisfy
\[
  Y_{M+1-L_0}(\rho)
  A^{\rho_{M+1-L_0}}\cdots A^{\rho_{M-1}}
  =
  A^{\rho_1}\cdots A^{\rho_{L_0-1}}Y_M(\rho).
\]
For \(L_0=1\), both word products are empty.

This is the fixed-boundary-condition product isolated from the
closure-property step in arXiv:2011.12127, Section IV.C, lines 2078--2090. -/
theorem closure_property_boundary_condition_product_of_window_witnesses
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (ρ : Fin (M + 1) → Fin d) :
    YAt ⟨M + 1 - L₀, by omega⟩ ρ *
        evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
          ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) =
      evalWord A (List.ofFn (fun r : Fin (L₀ - 1) => ρ ⟨r.val + 1, by omega⟩)) *
        YAt ⟨M, by omega⟩ ρ := by
  let i₀ : Fin (M + 1) := ⟨M + 1 - L₀, by omega⟩
  let Y : Fin ((L₀ - 1) + 1) → Matrix (Fin D) (Fin D) ℂ :=
    fun r => YAt (cyclicForwardSite i₀ r.val) ρ
  have hY : ∀ r : Fin ((L₀ - 1) + 1),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (cyclicForwardSite i₀ r.val) ρ ψ =
        groundSpaceMap A (L₀ + 1) (Y r) := by
    intro r
    exact hYAt (cyclicForwardSite i₀ r.val) ρ
  have hprod := boundary_closing_endpoint_word_products_common_background
    (A := A) hInj hL₀ hM ρ Y hY
  have hstart : cyclicForwardSite i₀ 0 = ⟨M + 1 - L₀, by omega⟩ := by
    ext
    simp only [i₀, cyclicForwardSite, Fin.val_mk]
    exact Nat.mod_eq_of_lt (by omega)
  have hend : cyclicForwardSite i₀ (L₀ - 1) = ⟨M, by omega⟩ := by
    ext
    simp only [i₀, cyclicForwardSite, Fin.val_mk]
    have hsum : M + 1 - L₀ + (L₀ - 1) = M := by omega
    rw [hsum, Nat.mod_eq_of_lt (by omega)]
  simpa [Y, hstart, hend] using hprod

/-- Auxiliary boundary-assignment product equation needed at the closing
boundary.

For each pair \(j,\sigma\), this states the existence of boundary assignments
\(\rho^+_{j,\sigma}\) and \(\rho^-_{j,\sigma}\) with the same complementary
word \(\mu\) as the two canonical assignments, and satisfying
\[
  Y_M(\rho^+_{j,\sigma}) A^j A^\sigma
  =
  Y_{M+1-L_0}(\rho^-_{j,\sigma}) A^j A^\sigma .
\]

**Open gap:** This is the remaining closure-property equation from
arXiv:2011.12127, Section IV.C, lines 2078--2090.  It is documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and tracked in #2405. -/
theorem closure_property_auxiliary_boundary_product_eq_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    ∃ ρPlus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d,
    ∃ ρMinus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d,
      (∀ (j : Fin d) (σ : Fin L₀ → Fin d)
          (k : Fin (M + 1 - (L₀ + 1))),
        ρPlus j σ ⟨k.val + L₀, by omega⟩ = μ k) ∧
      (∀ (j : Fin d) (σ : Fin L₀ → Fin d)
          (k : Fin (M + 1 - (L₀ + 1))),
        ρMinus j σ ⟨k.val + 1, by omega⟩ = μ k) ∧
      ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
        YAt ⟨M, by omega⟩ (ρPlus j σ) * A j * evalWord A (List.ofFn σ) =
          YAt ⟨M + 1 - L₀, by omega⟩ (ρMinus j σ) * A j *
            evalWord A (List.ofFn σ) := by
  sorry

end MPSTensor
