/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryOverlap
import TNLean.MPS.ParentHamiltonian.WrappingWindow

/-!
# Boundary conditions for the closure property

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
boundary condition \(\tau^+_\eta(\mu)\) used in the closure property. -/
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
condition \(\tau^-_\eta(\mu)\) used in the closure property. -/
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

The auxiliary boundary conditions may depend on the fixed physical letter and
the length-\(L_0\) word. If, for each pair \(j,\sigma\), the conditions
\(\rho^+_{j,\sigma}\) and \(\rho^-_{j,\sigma}\) carry the same complementary
word as \(\tau^+_\eta(\mu)\) and \(\tau^-_\eta(\mu)\), respectively, then a
product equation for these two conditions gives the corresponding equation for
\(\tau^+_\eta(\mu)\) and \(\tau^-_\eta(\mu)\):
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

Suppose two auxiliary boundary conditions have the same complementary words as
\(\tau^+_\eta(\mu)\) and \(\tau^-_\eta(\mu)\), respectively.  If the desired
product equation has already been proved for those two conditions, then it also
holds for the displayed boundary conditions:
\[
  Y_M(\tau^+_\eta(\mu)) A^j A^\sigma
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu)) A^j A^\sigma .
\]

This reduces the closure-property comparison to an adjacent-window product
identity between compatible boundary conditions. -/
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

These are the one-sided equations obtained from the inverting and growing-back
argument described in arXiv:2011.12127, Section IV.C, lines 2078--2090, when
the boundary is closed. -/
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

/-- One-sided boundary equations with the shared complementary word \(\mu\).

For the two displayed boundary conditions, the one-sided equations become
\[
  Y_M(\tau^+_\eta(\mu))A^j = A^\mu A^j X,
  \qquad
  X A^j A^\mu = A^jY_{M+1-L_0}(\tau^-_\eta(\mu)).
\]
These are the boundary-crossing equations after reindexing the complementary
sites by the same word \(\mu\). -/
lemma closure_property_boundary_one_sided_products_of_groundSpaceMap
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
    (∀ (η j : Fin d),
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j =
        evalWord A (List.ofFn μ) * A j * X) ∧
    (∀ (η j : Fin d),
      X * A j * evalWord A (List.ofFn μ) =
        A j * YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ)) := by
  obtain ⟨hWrap, hMirror⟩ :=
    closure_property_wrapped_mirror_compatibilities_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt
  constructor
  · intro η j
    have h := hWrap j (wrappedMiddleBackground L₀ (M + 1) η μ)
    have hcomp := wrappedMiddleBackground_complement L₀ (M + 1) η μ
    rw [hcomp] at h
    simpa using h.symm
  · intro η j
    have h := hMirror j (mirrorMiddleBackground L₀ (M + 1) η μ)
    have hcomp := mirrorMiddleBackground_complement L₀ (M + 1) η μ
    rw [hcomp] at h
    simpa using h

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

This records one adjacent-window product identity used in the coordinate proof
of the closure property described in arXiv:2011.12127, Section IV.C,
lines 2078--2090. -/
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

This records the fixed-boundary-condition product obtained from adjacent
windows in the coordinate proof of the closure property described in
arXiv:2011.12127, Section IV.C, lines 2078--2090. -/
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

/-- Product equation obtained by moving from the last site through the closing
boundary to the opposite boundary-crossing support.

For a fixed boundary condition \(\rho\), the window matrices satisfy
\[
  Y_M(\rho)A^{\rho_M}A^{\rho_0}\cdots A^{\rho_{M-L_0}}
  =
  A^{\rho_{L_0}}\cdots A^{\rho_M}A^{\rho_0}Y_{M+1-L_0}(\rho),
\]
with the products read cyclically and with \(M+2-L_0\) one-site factors on
each side.  This is an adjacent-window product used to reconstruct the closure
property described in arXiv:2011.12127, Section IV.C,
lines 2078--2090. -/
lemma closure_property_boundary_condition_long_product_of_window_witnesses
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (ρ : Fin (M + 1) → Fin d) :
    YAt ⟨M, by omega⟩ ρ *
        evalWord A (List.ofFn (fun r : Fin (M + 2 - L₀) =>
          ρ ⟨(M + r.val) % (M + 1), Nat.mod_lt _ (by omega)⟩)) =
      evalWord A (List.ofFn (fun r : Fin (M + 2 - L₀) =>
          ρ ⟨(L₀ + r.val) % (M + 1), Nat.mod_lt _ (by omega)⟩)) *
        YAt ⟨M + 1 - L₀, by omega⟩ ρ := by
  let i₀ : Fin (M + 1) := ⟨M, by omega⟩
  let Y : Fin ((M + 2 - L₀) + 1) → Matrix (Fin D) (Fin D) ℂ :=
    fun r => YAt (cyclicForwardSite i₀ r.val) ρ
  have hY : ∀ r : Fin ((M + 2 - L₀) + 1),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (cyclicForwardSite i₀ r.val) ρ ψ =
        groundSpaceMap A (L₀ + 1) (Y r) := by
    intro r
    exact hYAt (cyclicForwardSite i₀ r.val) ρ
  have hprod := adjacent_cyclicRestrictₗ_witness_product_common_background_named
    (A := A) hInj (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    i₀ ρ ψ Y
    (fun r : Fin (M + 2 - L₀) =>
      ρ ⟨(M + r.val) % (M + 1), Nat.mod_lt _ (by omega)⟩)
    (fun r : Fin (M + 2 - L₀) =>
      ρ ⟨(L₀ + r.val) % (M + 1), Nat.mod_lt _ (by omega)⟩)
    hY ?_ ?_
  · have hstart : cyclicForwardSite i₀ 0 = ⟨M, by omega⟩ := by
      ext
      simp only [i₀, cyclicForwardSite, Fin.val_mk]
      exact Nat.mod_eq_of_lt (by omega)
    have hend : cyclicForwardSite i₀ (M + 2 - L₀) =
        ⟨M + 1 - L₀, by omega⟩ := by
      ext
      simp only [i₀, cyclicForwardSite, Fin.val_mk]
      have hsum : M + (M + 2 - L₀) = M + 1 + (M + 1 - L₀) := by omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simpa [Y, hstart, hend] using hprod
  · ext r
    have hsite : cyclicForwardSite i₀ r.val =
        ⟨(M + r.val) % (M + 1), Nat.mod_lt _ (by omega)⟩ := by
      ext
      simp only [i₀, cyclicForwardSite, Fin.val_mk]
    rw [hsite]
  · ext r
    have hsite : cyclicForwardSite (cyclicForwardSite i₀ r.val) (L₀ + 1) =
        ⟨(L₀ + r.val) % (M + 1), Nat.mod_lt _ (by omega)⟩ := by
      rw [cyclicForwardSite_forwardSite]
      ext
      simp only [i₀, cyclicForwardSite, Fin.val_mk]
      have hsum : M + (r.val + (L₀ + 1)) = M + 1 + (L₀ + r.val) := by omega
      rw [hsum, Nat.add_mod_left]
    rw [hsite]

/-- Right-products determine the two restrictions at the closed boundary.

Suppose the two length-\((L_0+1)\) restrictions at the closed boundary are
represented by \(Y_M(\tau^+_\eta(\mu))\) and
\(Y_{M+1-L_0}(\tau^-_\eta(\mu))\).  If, for every physical letter \(j\),
\[
  Y_M(\tau^+_\eta(\mu))A^j
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^j,
\]
then the restrictions themselves agree:
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]
This is a consequence of first-letter restrictions; it does not assert that the
displayed one-site product equality is already known. -/
lemma closure_property_boundary_restriction_eq_of_first_products
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (YPlus YMinus : Matrix (Fin D) (Fin D) ℂ)
    (hPlus :
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
        groundSpaceMap A (L₀ + 1) YPlus)
    (hMinus :
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) η μ) ψ =
        groundSpaceMap A (L₀ + 1) YMinus)
    (hProd : ∀ j : Fin d,
      YPlus * A j = YMinus * A j) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M, by omega⟩ : Fin (M + 1))
        (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
        (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  apply eq_of_forall_restrictFirst_eq
  intro j
  rw [cyclicRestrictₗ_restrictFirst
      (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
      (⟨M, by omega⟩ : Fin (M + 1))
      (wrappedMiddleBackground L₀ (M + 1) η μ) ψ j]
  rw [cyclicRestrictₗ_restrictFirst
      (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
      (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
      (mirrorMiddleBackground L₀ (M + 1) η μ) ψ j]
  have hleft := cyclicRestrictₗ_restrictFirst_groundSpaceMap
    (A := A) (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (⟨M, by omega⟩ : Fin (M + 1))
    (wrappedMiddleBackground L₀ (M + 1) η μ) ψ
    hPlus j
  have hright := cyclicRestrictₗ_restrictFirst_groundSpaceMap
    (A := A) (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
    (mirrorMiddleBackground L₀ (M + 1) η μ) ψ
    hMinus j
  exact hleft.trans ((congrArg (fun Y => groundSpaceMap A L₀ Y) (hProd j)).trans hright.symm)

/-- Auxiliary boundary-condition product obtained from equality of the two
closing-boundary restrictions.

Suppose that, for every physical letter \(j\), the two boundary conditions with
outside letter \(j\) and complementary word \(\mu\) give the same
length-\((L_0+1)\) restriction:
\[
  \operatorname{Res}^{\tau^+_j(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_j(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]
Then there are boundary conditions with the same complementary word and with
\[
  Y_M(\rho^+_{j,\sigma})A^jA^\sigma
  =
  Y_{M+1-L_0}(\rho^-_{j,\sigma})A^jA^\sigma .
\]
The source says that the same inverting and growing-back argument may be used
when closing the boundary.  In coordinates, the remaining comparison is the
displayed restriction equality; it is recorded in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
lemma closure_property_auxiliary_boundary_product_eq_of_closing_restrictions
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hRestrict : ∀ j : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) j μ) ψ =
        cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) j μ) ψ) :
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
  let ρPlus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d :=
    fun j _ => wrappedMiddleBackground L₀ (M + 1) j μ
  let ρMinus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d :=
    fun j _ => mirrorMiddleBackground L₀ (M + 1) j μ
  refine ⟨ρPlus, ρMinus, ?_, ?_, ?_⟩
  · intro j σ k
    have h := congr_fun (wrappedMiddleBackground_complement L₀ (M + 1) j μ) k
    simpa [ρPlus] using h
  · intro j σ k
    have h := congr_fun (mirrorMiddleBackground_complement L₀ (M + 1) j μ) k
    simpa [ρMinus] using h
  · intro j σ
    have hfirst :
        YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) j μ) * A j =
          YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) j μ) * A j := by
      apply groundSpaceMap_injective_of_isNBlkInjective hInj
      have hvec :
          restrictFirst
              (cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
                (⟨M, by omega⟩ : Fin (M + 1))
                (wrappedMiddleBackground L₀ (M + 1) j μ) ψ) j =
            restrictFirst
              (cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
                (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
                (mirrorMiddleBackground L₀ (M + 1) j μ) ψ) j := by
        rw [hRestrict j]
      have hleft :=
        cyclicRestrictₗ_restrictFirst_groundSpaceMap
          (A := A) (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) j μ) ψ
          (hYAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) j μ)) j
      have hright :=
        cyclicRestrictₗ_restrictFirst_groundSpaceMap
          (A := A) (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) j μ) ψ
          (hYAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) j μ)) j
      rw [cyclicRestrictₗ_restrictFirst
          (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) j μ) ψ j,
        cyclicRestrictₗ_restrictFirst
          (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) j μ) ψ j] at hvec
      exact hleft.symm.trans (hvec.trans hright)
    simpa [ρPlus, ρMinus] using
      congrArg (fun Y => Y * evalWord A (List.ofFn σ)) hfirst

/-- Auxiliary boundary-condition product obtained from right-products at the
two closing boundary matrices.

Suppose that, for every boundary letter \(\eta\) and every physical letter
\(j\),
\[
  Y_M(\tau^+_\eta(\mu)) A^j
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu)) A^j .
\]
Then there are boundary conditions with the same complementary word and with
\[
  Y_M(\rho^+_{j,\sigma})A^jA^\sigma
  =
  Y_{M+1-L_0}(\rho^-_{j,\sigma})A^jA^\sigma .
\]
This is the composition of the right-product-to-restriction step with the
auxiliary product extraction from equal closing-boundary restrictions. -/
lemma closure_property_auxiliary_boundary_product_eq_of_right_products
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hProd : ∀ (η j : Fin d),
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j =
        YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j) :
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
  refine closure_property_auxiliary_boundary_product_eq_of_closing_restrictions
    (A := A) hInj hL₀ hM YAt hYAt μ ?_
  intro η
  exact closure_property_boundary_restriction_eq_of_first_products
    (A := A) hL₀ hM η μ
    (YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (YAt ⟨M + 1 - L₀, by omega⟩ (mirrorMiddleBackground L₀ (M + 1) η μ))
    (hYAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (hYAt ⟨M + 1 - L₀, by omega⟩
      (mirrorMiddleBackground L₀ (M + 1) η μ)) (hProd η)

/-- Cancellation form of the opposite-boundary coordinate comparison.

If the difference
\[
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^j - A^\mu A^jX
\]
vanishes after multiplication by \(A^\sigma\) on the right for every word
\(\sigma\) of length \(L_0\), then it vanishes.  This uses \(L_0\)-block
injectivity, so that the length-\(L_0\) word products span the full matrix
algebra. -/
lemma closure_property_mirror_right_product_eq_of_right_word_products
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hWord : ∀ (η j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) =
        evalWord A (List.ofFn μ) * A j * X *
          evalWord A (List.ofFn σ)) :
    ∀ (η j : Fin d),
      YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j =
        evalWord A (List.ofFn μ) * A j * X := by
  intro η j
  have hzero : ∀ σ : Fin L₀ → Fin d,
      (YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j -
          evalWord A (List.ofFn μ) * A j * X) *
        evalWord A (List.ofFn σ) = 0 := by
    intro σ
    simpa [sub_mul, sub_eq_zero, Matrix.mul_assoc] using hWord η j σ
  have hsub :
      YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j -
          evalWord A (List.ofFn μ) * A j * X = 0 :=
    eq_zero_of_mul_evalWord_eq_zero_of_isNBlkInjective_of_le_mul
      (A := A) (L₀ := L₀) (k := L₀) (q := 1) hInj (by omega) (by omega) hzero
  exact sub_eq_zero.mp hsub

/-- Auxiliary boundary-condition product obtained from the opposite-boundary
coordinate comparison after multiplication by length-\(L_0\) words.

Suppose that the last boundary already gives
\[
  Y_M(\tau^+_\eta(\mu)) A^j = A^\mu A^jX
\]
and that the opposite boundary satisfies the comparison
\[
  Y_{M+1-L_0}(\tau^-_\eta(\mu)) A^j A^\sigma
  =
  A^\mu A^j X A^\sigma
\]
for every word \(\sigma\) of length \(L_0\).  Since the length-\(L_0\) word
products span the full matrix algebra, this comparison implies
\[
  Y_{M+1-L_0}(\tau^-_\eta(\mu)) A^j = A^\mu A^jX .
\]
Together with the last-boundary equation this supplies the product equations
needed for the auxiliary boundary-condition product. -/
lemma closure_property_auxiliary_boundary_product_eq_of_mirror_padded_products
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (X : Matrix (Fin D) (Fin D) ℂ)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLast : ∀ (η j : Fin d),
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j =
        evalWord A (List.ofFn μ) * A j * X)
    (hMirrorPadded : ∀ (η j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) =
        evalWord A (List.ofFn μ) * A j * X *
          evalWord A (List.ofFn σ)) :
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
  refine closure_property_auxiliary_boundary_product_eq_of_right_products
    (A := A) hInj hL₀ hM YAt hYAt μ ?_
  have hMirrorRight :=
    closure_property_mirror_right_product_eq_of_right_word_products
      (A := A) hInj hL₀ hM YAt X μ hMirrorPadded
  intro η j
  exact (hLast η j).trans (hMirrorRight η j).symm

/-- Auxiliary boundary-condition product equation needed at the closing
boundary.

For each pair \(j,\sigma\), this states the existence of boundary conditions
\(\rho^+_{j,\sigma}\) and \(\rho^-_{j,\sigma}\) with the same complementary
word \(\mu\) as the two displayed boundary conditions, and satisfying
\[
  Y_M(\rho^+_{j,\sigma}) A^j A^\sigma
  =
  Y_{M+1-L_0}(\rho^-_{j,\sigma}) A^j A^\sigma .
\]

**Open gap:** The source does not display this coordinate equation.  Its
closing-boundary paragraph is represented here by the following coordinate
identity.  After the one-sided equation
\[
  Y_M(\tau^+_\eta(\mu)) A^j = A^\mu A^j X
\]
is obtained from the last boundary, the remaining comparison is the coordinate
form at the opposite boundary after multiplication by a length-\(L_0\) word,
\[
  Y_{M+1-L_0}(\tau^-_\eta(\mu)) A^j A^\sigma
  =
  A^\mu A^j X A^\sigma .
\]
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and tracked
in #2405. -/
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
  have hOneSided :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt μ
  suffices hMirrorPadded : ∀ (η j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) =
        evalWord A (List.ofFn μ) * A j * X *
          evalWord A (List.ofFn σ) by
    exact closure_property_auxiliary_boundary_product_eq_of_mirror_padded_products
      (A := A) hInj hL₀ hM YAt hYAt X μ hOneSided.1 hMirrorPadded
  sorry

end MPSTensor
