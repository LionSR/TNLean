import MPSLean.MPS.MultiBlock

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Basis / normality tools for the multi-block Fundamental Theorem

This file contains the (purely algebraic) Vandermonde-based separation lemmas that underpin the
"eventual linear independence" arguments for multi-block MPS canonical forms.

The key point is that, if the block scaling factors `μ k` are pairwise distinct, then the vectors
`(μ k) ^ N` form an invertible Vandermonde system for `N = 0, …, r-1`.  This lets us separate block
contributions once we can reduce to an equation of the form

`∑ k, v k * (μ k) ^ N = 0` for `N = 0, …, r-1`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The MPV at system size `N` viewed as a vector in the function space
`(Fin N → Fin d) → ℂ`. -/
def mpvFun (A : MPSTensor d D) (N : ℕ) : (Fin N → Fin d) → ℂ :=
  fun σ => mpv A σ

@[simp] lemma mpvFun_apply (A : MPSTensor d D) (N : ℕ) (σ : Fin N → Fin d) :
    mpvFun A N σ = mpv A σ := rfl

/-- The Vandermonde separation lemma: if the scaling factors `μ k` are distinct,
then any linear relation `∑ k, c k * (μ k) ^ N = 0` holding for `N = 0, …, r-1`
forces all coefficients `c k` to vanish.

This is a direct wrapper around Mathlib's
`Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero`.
-/
theorem vandermonde_separation (C : CanonicalForm d)
    (hμ : Function.Injective C.μ)
    (c : Fin C.numBlocks → ℂ)
    (hc : ∀ N : Fin C.numBlocks,
      (∑ k : Fin C.numBlocks, c k * (C.μ k) ^ (N : ℕ)) = 0) :
    c = 0 := by
  simpa using
    (Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := C.μ) (v := c) hμ hc)

/-- A function-valued variant of `vandermonde_separation`.

If `μ` is injective and we have Vandermonde-type relations pointwise in `a : α`, then the whole
family of functions must vanish.
-/
theorem vandermonde_separation_fun {n : ℕ} {α : Type*}
    (μ : Fin n → ℂ) (hμ : Function.Injective μ)
    (v : Fin n → α → ℂ)
    (hv : ∀ i : Fin n, ∀ a : α, (∑ j : Fin n, v j a * μ j ^ (i : ℕ)) = 0) :
    v = 0 := by
  classical
  funext j a
  -- Fix `a` and apply the scalar Vandermonde lemma to the coefficient vector `j ↦ v j a`.
  have h0 : (fun j : Fin n => v j a) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := μ) (v := fun j => v j a) hμ ?_
    intro i
    simpa using hv i a
  simpa using congrArg (fun f : Fin n → ℂ => f j) h0

/-- Vandermonde separation for MPVs of blocks at a *fixed* system size.

This is the basic linear-algebraic fact we use later: once the coefficient vectors are fixed (here,
functions `σ ↦ mpv (blockTensor k) σ` for a fixed `N₀`), distinct scaling factors `μ k` allow one to
separate the contributions by looking at finitely many powers.
-/
theorem block_mpvs_separation_at_fixed_size (C : CanonicalForm d)
    (hμ : Function.Injective C.μ) (N₀ : ℕ)
    (c : Fin C.numBlocks → ℂ)
    (hc : ∀ i : Fin C.numBlocks, ∀ σ : Fin N₀ → Fin d,
      (∑ k : Fin C.numBlocks,
        (c k * mpv (C.blockTensor k) σ) * (C.μ k) ^ (i : ℕ)) = 0) :
    ∀ k : Fin C.numBlocks, c k • mpvFun (C.blockTensor k) N₀ = 0 := by
  classical
  intro k
  -- Apply `vandermonde_separation_fun` pointwise in `σ`.
  have hv : (fun j : Fin C.numBlocks => c j • mpvFun (C.blockTensor j) N₀) = 0 := by
    -- We show each coefficient function vanishes by evaluating at `σ` and using Vandermonde.
    refine vandermonde_separation_fun (n := C.numBlocks) (α := Fin N₀ → Fin d)
      (μ := C.μ) hμ (v := fun j σ => (c j • mpvFun (C.blockTensor j) N₀) σ) ?_
    intro i σ
    -- Unfold the scalar multiplication on functions.
    -- Note: `•` on `ℂ` is multiplication.
    simpa [mpvFun, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using (hc i σ)
  -- Extract the `k`th component.
  simpa using congrArg (fun f => f k) hv

/-- A convenient corollary of `block_mpvs_separation_at_fixed_size`:

if each block MPV is nonzero at size `N₀`, then the Vandermonde relations force the coefficients
themselves to vanish.
-/
theorem block_mpvs_lin_indep_at_fixed_size (C : CanonicalForm d)
    (hμ : Function.Injective C.μ) (N₀ : ℕ)
    (hnonzero : ∀ k : Fin C.numBlocks, mpvFun (C.blockTensor k) N₀ ≠ 0)
    (c : Fin C.numBlocks → ℂ)
    (hc : ∀ i : Fin C.numBlocks, ∀ σ : Fin N₀ → Fin d,
      (∑ k : Fin C.numBlocks,
        (c k * mpv (C.blockTensor k) σ) * (C.μ k) ^ (i : ℕ)) = 0) :
    c = 0 := by
  classical
  -- First, separate blockwise: each `c k` annihilates the MPV function of block `k`.
  have hsep := block_mpvs_separation_at_fixed_size (C := C) hμ (N₀ := N₀) (c := c) hc
  -- Then use `hnonzero` to conclude `c k = 0` for each `k`.
  funext k
  have hk0 : c k • mpvFun (C.blockTensor k) N₀ = 0 := hsep k
  -- Pick a configuration `σ` where the block MPV does not vanish.
  have hσ : ∃ σ : Fin N₀ → Fin d, mpvFun (C.blockTensor k) N₀ σ ≠ 0 := by
    by_contra h
    apply hnonzero k
    funext σ
    by_contra hσ'
    exact h ⟨σ, hσ'⟩
  rcases hσ with ⟨σ, hσ⟩
  -- Evaluate the function equality at `σ`.
  have : c k * mpvFun (C.blockTensor k) N₀ σ = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun f => f σ) hk0
  -- Since `mpvFun … σ ≠ 0`, we get `c k = 0`.
  exact (mul_eq_zero.mp this).resolve_right hσ

end MPSTensor
