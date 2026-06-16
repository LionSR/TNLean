/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryClosing
import TNLean.MPS.ParentHamiltonian.BoundaryStripping
import TNLean.MPS.ParentHamiltonian.BoundaryMatrixBlock

/-!
# Stripping reductions for the closing boundary

Left-word stripping reductions for the closing boundary: a boundary difference
killed by every length-\(L_0\) word product on the left vanishes (block
injectivity), reducing the closing-boundary comparison to a single padded
coordinate identity in arXiv:2011.12127, Section IV.C.
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

**Scope restriction (conditional reduction):** This is only a stripping
reduction. It assumes the left-multiplied coordinate comparison through the
hypothesis `hLeft`, and does not derive that comparison from the
source sentence on closing the boundaries in arXiv:2011.12127, Section IV.C,
lines 2078--2079.
The remaining reconstruction is documented in
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

/-- Boundary matrix identity obtained from the closing-boundary local
constraints.

Let \(A\) be \(L_0\)-block-injective, let \(L_0<M\), let
\(\psi=\Gamma_{M+1}(X)\), and suppose that every cyclic window of length
\(L_0+1\) belongs to the corresponding local MPS ground space. The
closure-property step at the periodic boundary gives matrices \(Y_\nu\),
indexed by nonempty complementary words \(\nu\), such that for every
length-\(L_0\) word \(\alpha\),
\[
  X A^\alpha A^\nu = A^\alpha Y_\nu .
\]
This is the coordinate comparison needed by the block-injective
boundary-matrix commutation lemma.

**Open gap:** The proof is the missing coordinate form of the
inverting-and-growing-back argument when closing the periodic boundary in
arXiv:2011.12127, Section IV.C, lines 2078--2079. The statement is the
source-faithful coordinate obligation; the body remains open. Documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. Elimination: prove the
displayed matrix equation from the closing-boundary local constraints; tracked
in issue 2405. -/
theorem closure_property_boundary_block_window_equation_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d),
        X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν) =
          evalWord A (List.ofFn α) * Y ν := by
  sorry

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

**Scope restriction (conditional reduction):** This lemma assumes the
left-multiplied coordinate comparison and derives the auxiliary boundary-product
condition from it. The comparison is the coordinate reconstruction used here for
the closing-boundary sentence in arXiv:2011.12127, Section IV.C,
lines 2078--2079, and is documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
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

**Scope restriction (conditional reduction):** This theorem combines the
preceding reductions under the displayed left-multiplied comparison. It does not
derive that comparison from the source sentence on closing the boundaries in
arXiv:2011.12127, Section IV.C, lines 2078--2079. The source does not display
this formula; see `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
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

/-- Boundary restrictions from the left-multiplied closing-boundary comparison.

Let \(\psi=\Gamma_{M+1}(X)\), and let \(Y_i(\tau)\) represent the
length-\((L_0+1)\) cyclic restrictions of \(\psi\). If, for every boundary
letter \(\eta\), physical letter \(j\), and length-\(L_0\) words
\(\alpha,\sigma\),
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(A^\mu A^jXA^\sigma\bigr),
\]
then
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]

**Scope restriction (left-multiplied closing-boundary comparison):** This theorem
assumes the displayed left-multiplied comparison rather than deriving it from
the closing-boundary equality in arXiv:2011.12127, Section IV.C,
lines 2078--2079. Documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_boundary_restrictions_eq_of_groundSpaceMap_left_words
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
    ∀ η : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  have hMirrorPadded :=
    closure_property_mirror_padded_products_of_left_word_products
      (A := A) hInj hL₀ hM YAt X μ hLeft
  have hMirrorRight :=
    closure_property_mirror_right_product_eq_of_right_word_products
      (A := A) hInj hL₀ hM YAt X μ hMirrorPadded
  have hOneSided :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt μ
  refine closure_property_boundary_restrictions_eq_of_first_products
    (A := A) hL₀ hM YAt hYAt μ ?_
  intro η j
  exact (hOneSided.1 η j).trans (hMirrorRight η j).symm

/-- Equality of the two cyclic restrictions used when closing the boundary.

Let \(\psi=\Gamma_{M+1}(X)\), and suppose each length-\((L_0+1)\) cyclic
restriction of \(\psi\) lies in \(G_{L_0+1}(A)\). For every outside letter
\(\eta\), the two outside configurations \(\tau^+_\eta(\mu)\) and
\(\tau^-_\eta(\mu)\) are local coordinate notation for the cyclic support
crossing the last site and the opposite boundary-crossing support, with the same
word \(\mu\) on the sites outside the window. The closure-property comparison
at the periodic boundary is the equality
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]
After choosing window witnesses, the remaining coordinate reconstruction is the
boundary product comparison
\[
  Y_M(\tau^+_\eta(\mu))A^j
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^j,
\]
for all outside letters \(\eta\) and physical letters \(j\).

**Unfaithful:** This proof relies on
`closure_property_boundary_block_window_equation_of_groundSpaceMap`, whose proof
is the open boundary matrix identity in the argument for closing the periodic
boundary in arXiv:2011.12127, Section IV.C, lines 2078--2079. The verified
block-injective commutation lemma turns that coordinate comparison into the
one-site commutation identity for the boundary matrix \(X\). The verified
boundary-restriction equality lemma
`boundary_restrictions_eq_of_commutes_and_one_sided` and the block-injective
commutation lemma
`boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq` reduce the whole
closure-property step at the periodic boundary to this boundary matrix identity,
which is the transitive dependency for the coordinate consequences below.
Documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. Elimination: prove the
boundary matrix identity from the closing-boundary local constraints; tracked in
issue 2405. -/
theorem closure_property_boundary_restrictions_eq_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    ∀ η : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  have hLocalWitness : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
          groundSpaceMap A (L₀ + 1) Y := by
    intro i τ
    have hmem := hLocal i τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    exact ⟨Y, hY.symm⟩
  choose YAt hYAt using hLocalWitness
  suffices hProd : ∀ η j : Fin d,
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j =
        YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j by
    exact closure_property_boundary_restrictions_eq_of_first_products
      (A := A) hL₀ (le_of_lt hM) YAt hYAt μ hProd
  obtain ⟨hWrap, hMirror⟩ :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      hInj hL₀ (le_of_lt hM) hψX YAt hYAt μ
  obtain ⟨YBlock, hBlock⟩ :=
    closure_property_boundary_block_window_equation_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX hLocal
  have hComm : ∀ k : Fin d, X * A k = A k * X :=
    boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq
      (A := A) hInj hL₀ YBlock hBlock
  exact boundary_restrictions_eq_of_commutes_and_one_sided hInj hL₀
    (fun η => YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (fun η => YAt ⟨M + 1 - L₀, by omega⟩ (mirrorMiddleBackground L₀ (M + 1) η μ))
    μ hComm hWrap hMirror

/-- Left-multiplied comparison of the two cyclic restriction coordinates from
equality of the two restrictions at the periodic boundary.

If the two cyclic restrictions agree, then their first-letter restrictions give
\[
  Y_M(\tau^+_\eta(\mu))A^j
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^j.
\]
Multiplying this equality on the left by \(A^\alpha\) and on the right by
\(A^\sigma\) gives the displayed coordinate comparison.

**Scope restriction (periodic-boundary restriction equality):** This lemma
assumes the equality of the two restrictions at the periodic boundary rather than
deriving it from arXiv:2011.12127, Section IV.C, lines 2078--2079. Documented
in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
lemma closure_property_wrapped_mirror_left_word_products_of_boundary_restrictions
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hRestrict : ∀ η : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
        cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) η μ) ψ) :
    ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (YAt ⟨M, by omega⟩
              (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) := by
  intro η j σ α
  have hFirst := closure_property_boundary_first_products_of_restrictions
    (A := A) hInj hL₀ hM η μ
    (YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (YAt ⟨M + 1 - L₀, by omega⟩ (mirrorMiddleBackground L₀ (M + 1) η μ))
    (hYAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (hYAt ⟨M + 1 - L₀, by omega⟩
      (mirrorMiddleBackground L₀ (M + 1) η μ)) (hRestrict η) j
  rw [← hFirst]

/-- Left-multiplied comparison of the two cyclic restriction coordinates.

For \(\psi=\Gamma_{M+1}(X)\), after fixing a boundary letter \(\eta\), a
physical letter \(j\), and length-\(L_0\) words \(\alpha,\sigma\), the
periodic-boundary coordinate comparison is
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(Y_M(\tau^+_\eta(\mu))A^jA^\sigma\bigr).
\]

**Unfaithful:** This proof currently relies on
`closure_property_boundary_restrictions_eq_of_groundSpaceMap`, whose proof
depends on the unproved boundary matrix identity at the closing boundary. This
deviates from arXiv:2011.12127, Section IV.C, lines 2078--2079 by leaving open
the coordinate form of the inverting-and-growing-back argument when closing the
periodic boundary.
Documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`.
Elimination: prove the boundary matrix identity from the closing-boundary local
constraints and reprove this theorem without the unfaithful dependency; tracked
in issue 2405.

The comparison is derived from the periodic-boundary restriction equality
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]
The displayed restriction equality is the remaining local form of the sentence
in arXiv:2011.12127, Section IV.C, lines 2078--2079, that the
inverting-and-growing-back argument may also be applied when closing the
boundary. See `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_wrapped_mirror_left_word_products_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
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
          (YAt ⟨M, by omega⟩
              (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) := by
  have hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1) := by
    intro i τ
    rw [hYAt i τ]
    rw [groundSpace, LinearMap.mem_range]
    exact ⟨YAt i τ, rfl⟩
  have hRestrict :=
    closure_property_boundary_restrictions_eq_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX hLocal μ
  exact closure_property_wrapped_mirror_left_word_products_of_boundary_restrictions
    (A := A) hInj hL₀ (le_of_lt hM) YAt hYAt μ hRestrict

/-- Left-multiplied periodic-boundary comparison for an open-chain
representation.

For \(\psi=\Gamma_{M+1}(X)\), after fixing a boundary letter \(\eta\), a
physical letter \(j\), and length-\(L_0\) words \(\alpha,\sigma\), the
remaining periodic-boundary coordinate comparison is
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(A^\mu A^jXA^\sigma\bigr).
\]

**Unfaithful:** This proof uses
`closure_property_wrapped_mirror_left_word_products_of_groundSpaceMap`; that theorem
transitively depends on the unproved boundary matrix identity at the closing
boundary in `closure_property_boundary_restrictions_eq_of_groundSpaceMap`. This
deviates from arXiv:2011.12127, Section IV.C, lines 2078--2079 by leaving open
the coordinate form of the inverting-and-growing-back argument when closing the
periodic boundary.
Documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`.
Elimination: prove the boundary matrix identity from the closing-boundary local
constraints and reprove this theorem without the unfaithful dependency; tracked
in issue 2405. -/
theorem closure_property_mirror_left_word_products_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
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
  intro η j σ α
  have hCompare :=
    closure_property_wrapped_mirror_left_word_products_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt μ
  have hOneSided :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      (A := A) hInj hL₀ (le_of_lt hM) hψX YAt hYAt μ
  calc
    evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ))
        = evalWord A (List.ofFn α) *
          (YAt ⟨M, by omega⟩
              (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) := hCompare η j σ α
    _ = evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ)) := by
          rw [hOneSided.1 η j]

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

**Unfaithful:** This proof currently relies on
`closure_property_mirror_left_word_products_of_groundSpaceMap`, which
transitively depends on the unproved boundary matrix identity at the closing
boundary in `closure_property_boundary_restrictions_eq_of_groundSpaceMap`. This
deviates from arXiv:2011.12127, Section IV.C, lines 2078--2079 by leaving open
the coordinate form of the inverting-and-growing-back argument when closing the
periodic boundary.
Documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`.
Elimination: prove the boundary matrix identity from the closing-boundary local
constraints and reprove this theorem without the unfaithful dependency; tracked
in issue 2405. -/
theorem closure_property_auxiliary_boundary_product_eq_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
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
    (A := A) hInj hL₀ (le_of_lt hM) hψX YAt hYAt μ hLeft

end MPSTensor
