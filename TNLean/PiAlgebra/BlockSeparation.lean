/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.FundamentalTheoremComplete

/-!
# Block separation: from `SameMPV₂` to per-block `SameMPV`

The step from global `SameMPV₂` on block-diagonal tensors to per-block `SameMPV` requires
separating the weighted sum `∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` into
individual block equalities `mpv(A_k, σ) = mpv(B_k, σ)` for each `k`.

**The difficulty**: the standard Vandermonde argument (as in `vandermonde_separation_fun`)
requires *fixed* coefficients at each power, but here the "coefficients"
`mpv(A_k, σ) - mpv(B_k, σ)` depend on `σ : Fin N → Fin d` whose type varies with `N`.

**Proof strategy (repeated-word / Newton's identities)**:

1. For any fixed word `w` of length `M`, consider the `L`-fold concatenation `w^L` of
   length `M · L`. The evalWord identity gives
   `evalWord(A_k, w^L) = (evalWord(A_k, w))^L`, so the SameMPV₂ equation becomes:
   `∑_k (μ_k^M)^L · [tr(T_k^L) - tr(U_k^L)] = 0` for all `L ≥ 0`
   where `T_k = evalWord(A_k, w)` and `U_k = evalWord(B_k, w)`.

2. By Newton's identities (power sums determine symmetric functions), the eigenvalue
   multisets `{μ_k^M · λ_{k,j} : k, j}` and `{μ_k^M · ν_{k,j} : k, j}` coincide
   (where `λ_{k,j}` and `ν_{k,j}` are eigenvalues of `T_k` and `U_k` respectively).

3. Since this holds for ALL words `w` (of all lengths `M`), the algebraic independence of
   eigenvalues across blocks (separation by the distinct phases `μ_k`) forces per-block
   eigenvalue matching: `{λ_{k,j}} = {ν_{k,j}}` for each `k` individually.

4. Per-block eigenvalue matching for ALL words `w` implies per-block SameMPV.

Steps 1, 2 (for the multiset equality), and 4 are elementary. The main gap is step 3:
separating the combined eigenvalue multiset into per-block multisets. This is a
polynomial/algebraic-geometry argument (Zariski density of the non-collision locus)
that is not yet available in Mathlib.

## Main results

* `evalWord_replicate` — evalWord on replicated single letters gives matrix powers
* `evalWord_flatten_replicate` — evalWord on flattened replicated words gives matrix powers
* `mpv_const_eq_trace_pow` — mpv of constant configurations as traces of powers

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac (quant-ph/0608197), Appendix E
* [Cirac2017MPS] De las Cuevas, Schuch, Pérez-García, Cirac (arXiv:2011.12127), §IV
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

section BlockSeparation

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-! #### Helper: evalWord of a replicated list -/

/-- `evalWord A` on a replicated single letter gives a matrix power. -/
lemma evalWord_replicate (A : MPSTensor d D) (i : Fin d) (L : ℕ) :
    evalWord A (List.replicate L i) = (A i) ^ L := by
  induction L with
  | zero => simp [evalWord]
  | succ n ih => rw [List.replicate_succ, evalWord, ih, pow_succ']

/-- `evalWord A` on a flattened replicated word gives a matrix power. -/
lemma evalWord_flatten_replicate (A : MPSTensor d D) (w : List (Fin d)) (L : ℕ) :
    evalWord A ((List.replicate L w).flatten) = (evalWord A w) ^ L := by
  induction L with
  | zero => simp [evalWord, List.replicate]
  | succ n ih => simp only [List.replicate_succ, List.flatten_cons]; rw [evalWord_append, ih, pow_succ']

/-- The mpv of a constant configuration equals a trace of a matrix power. -/
lemma mpv_const_eq_trace_pow (A : MPSTensor d D) (i : Fin d) (L : ℕ) :
    mpv A (fun _ : Fin L => i) = Matrix.trace ((A i) ^ L) := by
  simp only [mpv, coeff, List.ofFn_const, evalWord_replicate]

/-! #### Block separation: the algebraic core

The step from `∑_k μ_k^N · (mpv(A_k,σ) - mpv(B_k,σ)) = 0` (for all N, σ) to
per-block `mpv(A_k,σ) = mpv(B_k,σ)` uses the multiplicative structure of `evalWord`:

**(1) Repeated-word identity**: For any word `w` of length `M` and repetition count `L`,
    `evalWord(A_k, w^L) = (evalWord(A_k, w))^L` (by `evalWord_flatten_replicate`).
    This gives `∑_k (μ_k^M)^L · [tr(T_k^L) - tr(U_k^L)] = 0` for all `L ≥ 0`.

**(2) Newton's identities**: Power-sum agreement for all `L` implies the combined
    eigenvalue multisets `{μ_k^M · spec(T_k)}_k = {μ_k^M · spec(U_k)}_k`.

**(3) Block separation**: For generic `w`, the eigenvalue clusters from different blocks
    don't collide after μ-scaling, forcing per-block matching.

The formal gap is step (3): the genericity argument (Zariski density of the non-collision
locus) requires algebraic geometry tools not currently in Mathlib.

See also `evalWord_flatten_replicate` for the key combinatorial identity.
-/

/-!
### Status

The per-block separation statement one might hope for,

`(∀ N σ, ∑ k, (μ k) ^ N • (mpv (A k) σ - mpv (B k) σ) = 0) → ∀ k, SameMPV (A k) (B k)`,

is **false** without additional hypotheses (e.g. canonical-form normalization preventing
rescalings between the block tensors and the phases `μ k`).

Accordingly, this file currently only provides the combinatorial helper lemmas
`evalWord_replicate`, `evalWord_flatten_replicate`, and `mpv_const_eq_trace_pow`.

For end-to-end results from `SameMPV₂`, use
`fundamentalTheorem_multiBlock_fromSameMPV₂` (in `PiAlgebra/FundamentalTheoremComplete.lean`),
which takes per-block separation as an explicit hypothesis.
-/

end BlockSeparation

end MPSTensor
