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
forces all coefficients `c k` to vanish. -/
theorem vandermonde_separation (C : CanonicalForm d)
    (hμ : Function.Injective C.μ)
    (c : Fin C.numBlocks → ℂ)
    (hc : ∀ N : Fin C.numBlocks,
      (∑ k : Fin C.numBlocks, c k * (C.μ k) ^ (N : ℕ)) = 0) :
    c = 0 := by
  simpa using Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hμ hc

/-- A function-valued variant of `vandermonde_separation`.

If `μ` is injective and we have Vandermonde-type relations pointwise in `a : α`, then the whole
family of functions must vanish. -/
theorem vandermonde_separation_fun {n : ℕ} {α : Type*}
    (μ : Fin n → ℂ) (hμ : Function.Injective μ)
    (v : Fin n → α → ℂ)
    (hv : ∀ i : Fin n, ∀ a : α, (∑ j : Fin n, v j a * μ j ^ (i : ℕ)) = 0) :
    v = 0 := by
  classical
  funext j a
  exact congr_fun
    (Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hμ (fun i => by simpa using hv i a)) j

/-- Vandermonde separation for MPVs of blocks at a *fixed* system size.

This is the basic linear-algebraic fact we use later: once the coefficient vectors are fixed (here,
functions `σ ↦ mpv (blockTensor k) σ` for a fixed `N₀`), distinct scaling factors `μ k` allow one to
separate the contributions by looking at finitely many powers. -/
theorem block_mpvs_separation_at_fixed_size (C : CanonicalForm d)
    (hμ : Function.Injective C.μ) (N₀ : ℕ)
    (c : Fin C.numBlocks → ℂ)
    (hc : ∀ i : Fin C.numBlocks, ∀ σ : Fin N₀ → Fin d,
      (∑ k : Fin C.numBlocks,
        (c k * mpv (C.blockTensor k) σ) * (C.μ k) ^ (i : ℕ)) = 0) :
    ∀ k : Fin C.numBlocks, c k • mpvFun (C.blockTensor k) N₀ = 0 := by
  classical
  intro k
  have hv := vandermonde_separation_fun C.μ hμ
    (v := fun j σ => (c j • mpvFun (C.blockTensor j) N₀) σ) (fun i σ => by
      simpa [mpvFun, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hc i σ)
  exact congr_fun hv k

/-- A convenient corollary of `block_mpvs_separation_at_fixed_size`:

if each block MPV is nonzero at size `N₀`, then the Vandermonde relations force the coefficients
themselves to vanish. -/
theorem block_mpvs_lin_indep_at_fixed_size (C : CanonicalForm d)
    (hμ : Function.Injective C.μ) (N₀ : ℕ)
    (hnonzero : ∀ k : Fin C.numBlocks, mpvFun (C.blockTensor k) N₀ ≠ 0)
    (c : Fin C.numBlocks → ℂ)
    (hc : ∀ i : Fin C.numBlocks, ∀ σ : Fin N₀ → Fin d,
      (∑ k : Fin C.numBlocks,
        (c k * mpv (C.blockTensor k) σ) * (C.μ k) ^ (i : ℕ)) = 0) :
    c = 0 := by
  classical
  have hsep := block_mpvs_separation_at_fixed_size C hμ N₀ c hc
  funext k
  obtain ⟨σ, hσ⟩ := Function.ne_iff.mp (hnonzero k)
  exact (mul_eq_zero.mp (by simpa [Pi.smul_apply, smul_eq_mul] using congr_fun (hsep k) σ)
    ).resolve_right hσ

end MPSTensor
