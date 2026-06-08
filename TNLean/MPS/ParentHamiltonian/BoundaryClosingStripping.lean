/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryClosing
import TNLean.MPS.ParentHamiltonian.BoundaryStripping

/-!
# Stripping reductions for the closing boundary

This file records the left-word form of the remaining coordinate comparison in
the closure-property argument.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Left-word stripping for the opposite-boundary coordinate comparison.

Let \(Y_{M+1-L_0}(\tau^-_\eta(\mu))\) be the matrix representing the opposite
boundary-crossing restriction. If, after fixing the physical letter \(j\) and
the right word \(\sigma\), the difference
\[
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma
  -A^\mu A^jXA^\sigma
\]
is killed by left multiplication by every length-\(L_0\) word product, then the
difference is zero.

**Open gap:** This is only a stripping reduction. It does not prove the
left-multiplied coordinate equation; that equation is the remaining coordinate
reconstruction used here for the boundary-closing sentence in arXiv:2011.12127,
Section IV.C, lines 2078--2079. The interpretive step is documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_mirror_padded_products_of_left_word_products
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ))) :
    ∀ (η j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) =
        evalWord A (List.ofFn μ) * A j * X *
          evalWord A (List.ofFn σ) := by
  intro η j σ
  let Z : Matrix (Fin D) (Fin D) ℂ :=
    YAt ⟨M + 1 - L₀, by omega⟩
        (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
        evalWord A (List.ofFn σ) -
      evalWord A (List.ofFn μ) * A j * X * evalWord A (List.ofFn σ)
  have hzero : ∀ α : Fin L₀ → Fin d, evalWord A (List.ofFn α) * Z = 0 := by
    intro α
    have h := hLeft η j σ α
    dsimp [Z]
    simpa [Matrix.mul_sub, sub_eq_zero] using h
  have hZ : Z = 0 :=
    eq_zero_of_evalWord_mul_eq_zero_of_isNBlkInjective_of_le_mul
      (A := A) (L₀ := L₀) (k := L₀) (q := 1) hInj (by omega) (by omega) hzero
  exact sub_eq_zero.mp hZ

/-- Auxiliary boundary-condition product from the left-word form of the
opposite-boundary coordinate comparison.

Suppose the last boundary gives
\[
  Y_M(\tau^+_\eta(\mu))A^j=A^\mu A^jX
\]
and the opposite-boundary difference becomes zero after left multiplication by
every length-\(L_0\) word product:
\[
  A^\alpha\,Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma
  =
  A^\alpha\,A^\mu A^jXA^\sigma .
\]
Then the auxiliary boundary conditions \(\rho^+_{j,\sigma}\) and
\(\rho^-_{j,\sigma}\) satisfying the required product equation exist.

**Open gap:** This is a reduction toward the coordinate reconstruction used here
for the closing-boundary sentence in arXiv:2011.12127, Section IV.C,
lines 2078--2079. The formula is not displayed in the source; it is
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
lemma closure_property_auxiliary_boundary_product_eq_of_mirror_left_word_products
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
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ))) :
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
  have hMirrorPadded :=
    closure_property_mirror_padded_products_of_left_word_products
      (A := A) hInj hL₀ hM YAt X μ hLeft
  exact closure_property_auxiliary_boundary_product_eq_of_mirror_padded_products
    (A := A) hInj hL₀ hM YAt hYAt X μ hLast hMirrorPadded

/-- Auxiliary boundary-condition product from the left-multiplied coordinate
form and the one-sided boundary equations of an open-chain representation.

For \(\psi=\Gamma_{M+1}(X)\), the last boundary supplies
\[
  Y_M(\tau^+_\eta(\mu))A^j=A^\mu A^jX.
\]
Thus the auxiliary product equation follows once, for every pair of
length-\(L_0\) words \(\alpha,\sigma\), the opposite boundary satisfies the
left-multiplied coordinate comparison
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(A^\mu A^jXA^\sigma\bigr)
\]

**Open gap:** This theorem combines the preceding reductions in the
closure-property argument. It does not prove the displayed left-multiplied
comparison; that comparison is the coordinate reconstruction used here for the
boundary-closing sentence in arXiv:2011.12127, Section IV.C, lines 2078--2079.
The source does not display this formula. See
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_auxiliary_boundary_product_eq_of_groundSpaceMap_left_words
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ))) :
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
  exact closure_property_auxiliary_boundary_product_eq_of_mirror_left_word_products
    (A := A) hInj hL₀ hM YAt hYAt X μ hOneSided.1 hLeft

/-- Left-multiplied opposite-boundary comparison for an open-chain
representation.

For \(\psi=\Gamma_{M+1}(X)\), after fixing a boundary letter \(\eta\), a
physical letter \(j\), and length-\(L_0\) words \(\alpha,\sigma\), the
remaining boundary-closing comparison is
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(A^\mu A^jXA^\sigma\bigr).
\]

**Open gap:** The source does not display this formula. It is the coordinate
reconstruction used here for the sentence in arXiv:2011.12127, Section IV.C,
lines 2078--2079, that the inverting-and-growing-back argument may also be
applied when closing the boundary. See
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_mirror_left_word_products_of_groundSpaceMap
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
    ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ)) := by
  sorry

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

**Open gap:** This theorem is now reduced to the displayed left-multiplied
comparison above. That formula is not displayed in the source; it is the
coordinate reconstruction used here for arXiv:2011.12127, Section IV.C, lines
2078--2079. -/
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
  have hLeft :=
    closure_property_mirror_left_word_products_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt μ
  exact closure_property_auxiliary_boundary_product_eq_of_groundSpaceMap_left_words
    (A := A) hInj hL₀ hM hψX YAt hYAt μ hLeft

end MPSTensor
