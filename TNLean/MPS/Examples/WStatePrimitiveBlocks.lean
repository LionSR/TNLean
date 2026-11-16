/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.FiniteLengthPrimitiveBlocks
import TNLean.MPS.Examples.WStateBlocking

/-!
# Primitive sectors for the blocked W vector at arbitrary length

Every positive-length periodic W representation has an expansion into primitive sectors
after blocking by `gcd N D!`. The blocked W equation is derived from the original vector,
and the sectors have the common injectivity length `(D² + 1)²` in the blocked alphabet.
No canonical form, primitive blocks or blocked-vector identity is assumed.

Source: the blocking device in PGVWC07, arXiv:quant-ph/0608197, lines 2090–2097,
applied to the W vector of arXiv:2011.12127, Appendix A, lines 2348–2362.

**Scope restriction (blocking cost and block separation):** the factorial blocking cost
does not give the review's polynomial bound. Phase grouping and the quantitative cut-rank
argument remain to be composed with this expansion; see
`docs/paper-gaps/rmp_w_state_ti_bound.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- An arbitrary single-length periodic W representation supplies primitive blocks of its
blocked vector, with total bond dimension at most the original dimension. The equality uses
the existing physical blocking equivalence and is derived from the original W equation.
The statement is valid for every positive length, including powers of small primes. -/
theorem exists_primitive_blocks_of_mpv_eq_smul_wIndicator {D N : ℕ}
    (A : MPSTensor 2 D) (hN : 0 < N) {c : ℂ}
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    let p := N.gcd D.factorial
    let M := N / p
    0 < p ∧ p ∣ N ∧ p ≤ D.factorial ∧
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (B : (j : Fin r) → MPSTensor (blockPhysDim 2 p) (dim j)) (coef : Fin r → ℂ),
      (∀ j, 0 < dim j) ∧ (∑ j, dim j) ≤ D ∧
      (∀ j, IsPeriodic 1 (B j)) ∧
      (∀ j, Kraus.IsNBlkInjective (B j) ((D ^ 2 + 1) ^ 2)) ∧
      (∀ j, coef j ≠ 0) ∧
      ∀ σ : Cfg (blockPhysDim 2 p) M,
        (∑ j, coef j * mpv (B j) σ) =
          c * wIndicator (M * p) (blockedConfigEquiv 2 M p σ) := by
  let p := N.gcd D.factorial
  let M := N / p
  obtain ⟨hp, hpN, hpD, r, dim, B, coef, hdim, hsum, hper, hC1, hcoef, hdecomp⟩ :=
    exists_primitive_blocks_at_gcd_factorial A hN
  have hMp : M * p = N := Nat.div_mul_cancel hpN
  have hWflat : ∀ σ : Cfg 2 (M * p), mpv A σ = c * wIndicator (M * p) σ := by
    simpa only [hMp] using hW
  refine ⟨hp, hpN, hpD, r, dim, B, coef, hdim, hsum, hper, hC1, hcoef, ?_⟩
  intro σ
  rw [← hdecomp σ, mpv, coeff, evalWord_blockTensor, ← ofFn_blockedConfigEquiv]
  exact hWflat (blockedConfigEquiv 2 M p σ)

end MPSTensor
