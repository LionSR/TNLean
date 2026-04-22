/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry.EqualCaseFTHyp

/-!
# Theorem 4.1 definitions

This module contains the `p`-divisibility and `p`-refinement definitions used in
Theorem 4.1 of arXiv:1708.00029.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Theorem 4.1 — `p`-refinement and `p`-divisibility (definitions only) -/

section Theorem41

variable {d D : ℕ}

/-- **`p`-divisibility of a CP linear endomorphism.**

A linear endomorphism `E` of `Mat_D ℂ` is *`p`-divisible* if it equals the `p`-fold
composition of some CPTP map `E'`. This is the channel-theoretic notion appearing in
arXiv:1708.00029, §4.1. -/
def IsPDivisibleChannel
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (p : ℕ) : Prop :=
  ∃ E' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
    IsChannel E' ∧ E = E' ^ p

/-- **`p`-refinement of an MPS tensor (arXiv:1708.00029, §4.1, Eq. (4.1)).**

`B : MPSTensor d D` admits a `p`-refinement if there exists another tensor
`A : MPSTensor d D` and an isometry `W : ℂ^d → (ℂ^d)^{⊗p}` (encoded as a matrix
`Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ` with `Wᴴ * W = 1`) such that the `p`-blocked
`A` matches the `W`-image of `B` at the level of MPV coefficients:
`coeff (blockTensor A p) (List.ofFn τ) = ∑_σ (∏_k W (τ k) (σ k)) · coeff B (List.ofFn σ)`
for every length `N` and every `τ : Fin N → Fin (blockPhysDim d p)`.

In paper notation, this encodes `|V_{pN}(A)⟩ = W^{⊗N} |V_N(B)⟩` for every `N`. -/
def IsPRefinable (B : MPSTensor d D) (p : ℕ) : Prop :=
  ∃ (A : MPSTensor d D)
    (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ),
    Wᴴ * W = 1 ∧
    ∀ (N : ℕ) (τ : Fin N → Fin (blockPhysDim d p)),
      coeff (blockTensor A p) (List.ofFn τ) =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ)

end Theorem41

end MPSTensor
