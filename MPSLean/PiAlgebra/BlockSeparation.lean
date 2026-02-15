/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.PiAlgebra.FundamentalTheoremComplete

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
* `sameMPV₂_implies_perBlock_sameMPV` — block separation from SameMPV₂ (contains sorry)
* `fundamentalTheorem_multiBlock_complete` — the final multi-block FT (no separation hyp)

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
  | zero => simp [evalWord, List.replicate_zero]
  | succ n ih =>
    rw [List.replicate_succ, evalWord, ih, pow_succ']

/-- `evalWord A` on a flattened replicated word gives a matrix power. -/
lemma evalWord_flatten_replicate (A : MPSTensor d D) (w : List (Fin d)) (L : ℕ) :
    evalWord A ((List.replicate L w).flatten) = (evalWord A w) ^ L := by
  induction L with
  | zero => simp [evalWord, List.replicate]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [evalWord_append, ih, pow_succ']

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

/-- Algebraic block separation: from `∑_k μ_k^N · δ_k(σ) = 0` for all `N, σ`
(with `δ_k(σ) = mpv(A_k,σ) - mpv(B_k,σ)`), conclude per-block `SameMPV`.

See the section docstring above for the mathematical proof strategy. -/
private theorem block_powsum_separation
    (μ : Fin r → ℂ) (hμ_inj : Function.Injective μ) (hμ_ne : ∀ k, μ k ≠ 0)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hδ : ∀ N (σ : Fin N → Fin d),
      ∑ k, (μ k) ^ N • (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) := by
  intro k N σ
  -- For each fixed N and σ, we need to extract δ_k(σ) = 0 from the summed equation.
  -- The hypothesis gives us: ∀ N σ, ∑_j μ_j^N · δ_j(σ) = 0
  -- The multiplicative structure of evalWord (via repeated words) combined with
  -- Newton's identities and the distinctness of μ_k forces per-block vanishing.
  -- See the section docstring for the full mathematical argument.
  sorry

/-- **Block separation from `SameMPV₂`.**

From the global trace identities for block-diagonal tensors, recover per-block MPV equality.
This is the key separation step in the multi-block Fundamental Theorem.

The proof reduces to `block_powsum_separation` via `sameMPV₂_summed_blocks`. -/
theorem sameMPV₂_implies_perBlock_sameMPV
    (μ : Fin r → ℂ) (hμ_inj : Function.Injective μ)
    (hμ_ne : ∀ k, μ k ≠ 0)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) := by
  -- Step 0: From SameMPV₂, derive the summed equation
  have hsum : ∀ N (σ : Fin N → Fin d),
      ∑ k, (μ k) ^ N • mpv (A k) σ = ∑ k, (μ k) ^ N • mpv (B k) σ :=
    sameMPV₂_summed_blocks μ A B hSame₂
  -- Step 1: Rewrite as ∑_k μ_k^N • δ_k(σ) = 0 where δ_k(σ) = mpv(A_k,σ) - mpv(B_k,σ)
  have hδ : ∀ N (σ : Fin N → Fin d),
      ∑ k, (μ k) ^ N • (mpv (A k) σ - mpv (B k) σ) = 0 := by
    intro N σ
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hsum N σ)
  -- Step 2: Separate per block using the Vandermonde structure + Newton/algebraic separation
  -- The key insight: for repeated words, we get power-sum equations whose structure
  -- (via evalWord_flatten_replicate) constrains eigenvalue multisets.
  -- Combined with the distinctness of μ_k, this forces per-block equality.
  -- This algebraic separation step requires Newton's identities for eigenvalues of
  -- matrices over ℂ plus a genericity/Zariski-density argument, beyond current Mathlib.
  exact block_powsum_separation μ hμ_inj hμ_ne A B hA hδ

/-- **Full multi-block Fundamental Theorem (no separation hypothesis).**

Combining `sameMPV₂_implies_perBlock_sameMPV` with the assembly machinery
gives the complete result: `SameMPV₂` on block-diagonal tensors with distinct
nonzero phases implies global gauge equivalence. -/
theorem fundamentalTheorem_multiBlock_complete
    (μ : Fin r → ℂ) (hμ_inj : Function.Injective μ)
    (hμ_ne : ∀ k, μ k ≠ 0)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  (fundamentalTheorem_multiBlock_fromSameMPV₂ μ A B hA hSame₂
    (sameMPV₂_implies_perBlock_sameMPV μ hμ_inj hμ_ne A B hA hSame₂)).2.1

end BlockSeparation

end MPSTensor
