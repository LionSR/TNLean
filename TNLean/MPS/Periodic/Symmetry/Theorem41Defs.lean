/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry.EqualCaseFTHyp

/-!
# Theorem 4.1 definitions

This module contains the \(p\)-divisibility and \(p\)-refinement definitions used in
arXiv:1708.00029, Theorem 4.1, lines 717--731.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Theorem 4.1 — `p`-refinement and `p`-divisibility (definitions only) -/

section Theorem41

variable {d D : ℕ}

/-- **\(p\)-divisibility of a transfer map.**

A linear endomorphism \(E\) of \(M_D(\mathbb C)\) is \(p\)-divisible if it equals the
\(p\)-fold composition of some trace-preserving completely positive map \(E'\). This is
the definition in arXiv:1708.00029, lines 717--718. -/
def IsPDivisibleChannel
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (p : ℕ) : Prop :=
  ∃ E' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
    IsChannel E' ∧ E = E' ^ p

/-- **\(p\)-refinement of an MPS family.**

The matrix product vector family of \(B\) can be \(p\)-refined, in this same-bond
version, if there exists another tensor \(A\) with the same bond dimension as \(B\)
and an isometry \(W : \mathbb C^d \to (\mathbb C^d)^{\otimes p}\) (encoded as a
matrix with \(W^\dagger W = 1\)) such that the \(p\)-blocked tensor \(A^{[p]}\)
matches the \(W^{\otimes N}\)-image of \(B\) at the level of MPV coefficients:
`coeff (blockTensor A p) (List.ofFn τ) = ∑_σ (∏_k W (τ k) (σ k)) · coeff B (List.ofFn σ)`
for every length `N` and every `τ : Fin N → Fin (blockPhysDim d p)`.

In the paper notation of arXiv:1708.00029, lines 719--724, this encodes
\(|V_{pN}(A)\rangle = W^{\otimes N}|V_N(B)\rangle\) for every \(N\). -/
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
