/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.WrappingWindow

/-!
# Block-injective boundary-matrix commutation

For a block-injective MPS tensor (injective after blocking \(L_0\) sites), a boundary
matrix `X` whose length-\(L_0\) windowed products satisfy a single matrix equation
commutes with every one-site matrix `A j`. This is the block-injective analogue of
`boundary_matrix_commutes`, with the single-site spanning replaced by the
length-\(L_0\) block span and the complement cancellation handled by the block
annihilation lemma `eq_zero_of_mul_evalWord_eq_zero_of_isNBlkInjective_of_le_mul`.

This is the "L2" step of the boundary-closing decomposition for the normal
range-reduction argument of arXiv:2011.12127, Section IV.C; it isolates the whole
remaining obligation onto the block matrix equation hypothesis `hMatEq` (the "L1"
keystone, not yet proved). See `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **Block-injective boundary-matrix commutation (L2).**

Let `A` be block injective with injectivity length \(L_0 > 0\). Suppose a boundary
matrix `X` and a family `Y` of matrices indexed by length-`K` complement words
satisfy the block matrix equation
\[
  X \cdot A^{\sigma_{\mathrm{tail}}} \cdot A^{\sigma_{\mathrm{comp}}}
  = A^{\sigma_{\mathrm{tail}}} \cdot Y_{\sigma_{\mathrm{comp}}}
\]
for every length-\(L_0\) head word `σ_tail` and every length-`K` complement word
`σ_comp`. Then `X` commutes with every one-site matrix `A j`.

The length-\(L_0\) head span exhausts the full matrix algebra, promoting the equation
to all matrices \(M_1\), and the block annihilation lemma cancels the length-`K`
complement.
This isolates the whole boundary-closing gap onto `hMatEq`. -/
theorem boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq
    {A : MPSTensor d D} {L₀ K : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hMatEq : ∀ (σ_tail : Fin L₀ → Fin d) (σ_comp : Fin K → Fin d),
      X * evalWord A (List.ofFn σ_tail) * evalWord A (List.ofFn σ_comp)
        = evalWord A (List.ofFn σ_tail) * Y σ_comp) :
    ∀ j : Fin d, X * A j = A j * X := by
  -- Step 1: span the length-\(L_0\) head to promote the equation to all matrices \(M_1\).
  have hStep1 : ∀ (M₁ : Matrix (Fin D) (Fin D) ℂ) (σ_comp : Fin K → Fin d),
      X * M₁ * evalWord A (List.ofFn σ_comp) = M₁ * Y σ_comp := by
    intro M₁ σ_comp
    have hfg : (LinearMap.mulLeft ℂ X).comp
        (LinearMap.mulRight ℂ (evalWord A (List.ofFn σ_comp)))
        = LinearMap.mulRight ℂ (Y σ_comp) := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
      · simpa [wordSpan] using (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
      · intro σ_tail
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply]
        rw [← Matrix.mul_assoc]
        exact hMatEq σ_tail σ_comp
    have hcong := congrArg (· M₁) hfg
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply] at hcong
    rw [← Matrix.mul_assoc] at hcong
    exact hcong
  -- Step 2: take \(M_1 = 1\) to identify \(Y_{\sigma} = X \cdot A^{\sigma}\) on the complement.
  have hY : ∀ σ_comp : Fin K → Fin d,
      Y σ_comp = X * evalWord A (List.ofFn σ_comp) := by
    intro σ_comp
    have h := hStep1 1 σ_comp
    simp only [mul_one, one_mul] at h
    exact h.symm
  -- Step 3: the commutator annihilates every length-`K` complement word.
  intro j
  have hB : ∀ σ_comp : Fin K → Fin d,
      (X * A j - A j * X) * evalWord A (List.ofFn σ_comp) = 0 := by
    intro σ_comp
    have h1 := hStep1 (A j) σ_comp
    rw [hY σ_comp, ← Matrix.mul_assoc] at h1
    rw [sub_mul, sub_eq_zero]
    exact h1
  -- Step 4: block injectivity turns annihilation at length \(K \le (K+1)\cdot L_0\) into \(0\).
  have hzero : X * A j - A j * X = 0 :=
    eq_zero_of_mul_evalWord_eq_zero_of_isNBlkInjective_of_le_mul hInj
      (q := K + 1) (Nat.succ_le_succ (Nat.zero_le K))
      (le_trans (Nat.le_succ K) (Nat.le_mul_of_pos_right (K + 1) hL₀)) hB
  exact sub_eq_zero.mp hzero

end MPSTensor
