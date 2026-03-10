/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.BlockSeparation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Block separation proof: from `SameMPV₂` to per-block `SameMPV`

**STATUS: DEPRECATED / VESTIGIAL.** This file contains a `sorry` in
`per_block_trace_eq_of_summed_blocks` that is **false as stated** (see the counterexample in the
docstring below). The downstream theorems are never imported by the main build (`TNLean.lean`);
only `TNLean/Experimental.lean` references this file.

The correct block-separation results are in `TNLean.PiAlgebra.BlockSeparation` and
`TNLean.PiAlgebra.CanonicalFormSep`, which use `IsCanonicalForm` / `IsNormalCanonicalForm`
hypotheses to avoid the block-swap issue.

This file proves the block separation theorem under the hypothesis that the
scaling factors `μ k` are pairwise distinct (injective) and nonzero.

## Strategy

Given `SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)`, i.e.,
`∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` for all `N`, `σ`,
we prove `∀ k, SameMPV (A k) (B k)` when `μ` is injective and nonzero.

### Proof outline

1. **Repeated-word identity**: For word `w` of length `M` and repetition count `L`:
   `∑_k (μ_k^M)^L · [tr(T_k^L) - tr(U_k^L)] = 0`
   where `T_k = evalWord(A_k, w)`, `U_k = evalWord(B_k, w)`.

2. **Newton's identities**: The power trace identity for all `L ≥ 0` implies
   equality of characteristic polynomials for the combined block-diagonal matrices:
   `∏_k charpoly(μ_k^M · T_k) = ∏_k charpoly(μ_k^M · U_k)`.

3. **Vandermonde on polynomial coefficients**: Each coefficient of the combined
   charpoly gives a polynomial equation in the `μ_k`. Using Vandermonde separation
   on the coefficients (varying `M`), we extract per-block charpoly equality.

4. **Trace extraction**: Per-block polynomial equality at the linear coefficient
   gives `tr(T_k) = tr(U_k)`, i.e., `mpv(A_k, w) = mpv(B_k, w)` for all `w`.

## Main results

* `sameMPV_of_sameMPV₂_injective` — per-block SameMPV from SameMPV₂ (injective μ)
* `fundamentalTheorem_multiBlock_noSep` — the full FT without `hSep`

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac (quant-ph/0608197), Appendix E
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators
open Polynomial

namespace MPSTensor

variable {d : ℕ}

/-! ### Repeated-word trace identity -/
section RepeatedWordTrace

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- The length of a flattened replicated list. -/
private lemma length_flatten_replicate {α : Type*} (w : List α) (L : ℕ) :
    ((List.replicate L w).flatten).length = w.length * L := by
  rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul, Nat.mul_comm]

/-- The SameMPV₂ condition applied to a repeated word `w^L` gives:
`∑_k (μ_k)^{|w|·L} · Δ_k = 0`
where `Δ_k = tr(evalWord(A_k,w)^L) - tr(evalWord(B_k,w)^L)`. -/
theorem sameMPV₂_repeated_word
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (w : List (Fin d)) (L : ℕ) :
    ∑ k, (μ k) ^ (w.length * L) *
      (Matrix.trace ((evalWord (A k) w) ^ L) -
       Matrix.trace ((evalWord (B k) w) ^ L)) = 0 := by
  -- Build σ : Fin (w.length * L) → Fin d from the flattened repeated word
  set flat := (List.replicate L w).flatten with flat_def
  have hlen : flat.length = w.length * L := length_flatten_replicate w L
  -- Define σ by reading off elements of `flat`
  set σ : Fin (w.length * L) → Fin d :=
    fun i => flat.get (Fin.cast hlen.symm i) with σ_def
  -- Key fact: List.ofFn σ = flat
  have hofFn : List.ofFn σ = flat := by
    rw [σ_def]
    conv_rhs => rw [← List.ofFn_getElem flat]
    apply List.ofFn_congr (by omega)
  -- Apply the summed block equation at system size w.length * L
  have hsummed := sameMPV₂_summed_blocks μ A B hSame (w.length * L) σ
  -- Rewrite: mpv (A k) σ = Matrix.trace (evalWord (A k) (List.ofFn σ))
  -- = Matrix.trace (evalWord (A k) flat) = Matrix.trace ((evalWord (A k) w) ^ L)
  simp only [mpv, coeff, hofFn, flat_def, evalWord_flatten_replicate] at hsummed
  -- hsummed now has smul form; convert to mul and derive the result
  simp only [smul_eq_mul] at hsummed
  -- Goal: ∑ k, μ k ^ _ * (tr(... ^ L) - tr(... ^ L)) = 0
  rw [show (∑ k, (μ k) ^ (w.length * L) *
    (Matrix.trace ((evalWord (A k) w) ^ L) -
     Matrix.trace ((evalWord (B k) w) ^ L))) =
    ∑ k, (μ k) ^ (w.length * L) * Matrix.trace ((evalWord (A k) w) ^ L) -
    ∑ k, (μ k) ^ (w.length * L) * Matrix.trace ((evalWord (B k) w) ^ L)
    from by rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring]
  rw [hsummed, sub_self]

end RepeatedWordTrace

/-! ### Per-block separation from SameMPV₂

The main theorem, proved using the repeated-word identity and a
key algebraic separation lemma. -/
section Separation

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- **Per-block trace equality from SameMPV₂** (key algebraic separation).

If `μ : Fin r → ℂ` are distinct nonzero scalars and
`SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)`,
then for every block `k` and every word `w`:
  `tr(evalWord(A_k, w)) = tr(evalWord(B_k, w))`.

### Known issue: additional hypotheses needed

**Warning**: As currently stated, this lemma is **false** for `r ≥ 2` without
additional structural hypotheses on the blocks. The SameMPV₂ condition with
injective nonzero `μ` is necessary but NOT sufficient for per-block trace equality.

**Counterexample** (r = 2, d = 2, dim = [1, 1], μ = (1, 2)):
  Take A₀(0) = 4, A₀(1) = 2, A₁(0) = 1, A₁(1) = 3  (1×1 matrices).
  Define B by "block swap": B₀(i) = (μ₁/μ₀) · A₁(i), B₁(i) = (μ₀/μ₁) · A₀(i).
  So B₀(0) = 2, B₀(1) = 6, B₁(0) = 2, B₁(1) = 1.

  Then for any word w, the scaled blocks satisfy:
    μ₀ · B₀(i) = μ₁ · A₁(i) and μ₁ · B₁(i) = μ₀ · A₀(i)
  so the block-diagonal matrices for A and B have the same blocks up to permutation.
  This gives SameMPV₂ (the trace of the product is the sum of per-block traces,
  which is unchanged by permutation of summands).

  But tr(A₀(0)) = 4 ≠ 2 = tr(B₀(0)), violating per-block trace equality.

**The issue**: the "block swap" symmetry `A_k ↔ B_{π(k)}` preserves the combined
trace sum but permutes the block assignment. The injectivity of `μ` prevents
`μ_k = μ_{π(k)}` for `k ≠ π(k)`, but the scaled products `μ_k · A_k(i)` can
still match `μ_{π(k)} · B_{π(k)}(i)` through the swap.

**What would make it true**: In the canonical form setting (Pérez-García et al.),
the blocks have normalized transfer matrices (spectral radius 1), and the `μ_k`
are determined by the block structure. This normalization prevents the block-swap
counterexample: if `B₀(i) = (μ₁/μ₀) · A₁(i)`, then the spectral radius of B₀'s
transfer matrix is `|μ₁/μ₀|² · ρ(E₁)`, which equals 1 only if `|μ₀| = |μ₁|`.

Possible fixes:
1. Add a "spectral radius normalization" hypothesis
2. Weaken the conclusion to `∃ π, ∀ k w, tr(evalWord (A k) w) = tr(evalWord (B (π k)) w)`
3. Add an explicit "no block swap" hypothesis

For now, this is left as `sorry`. The downstream theorems
(`fundamentalTheorem_multiBlock_noSep`) also use `IsInjective`, which
may provide the additional structure needed in the canonical form setting.

### Mathematical proof sketch (under appropriate additional hypotheses)

See `sameMPV₂_repeated_word` for the repeated-word identity, and
`MvPolynomial.mul_esymm_eq_sum` for Newton's identities. The argument uses
the power-trace identity to derive product-charpolyRev equality, then
Vandermonde separation on polynomial coefficients. -/
private lemma per_block_trace_eq_of_summed_blocks
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_ne : ∀ k, μ k ≠ 0)
    (hμ_inj : Function.Injective μ)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ (k : Fin r) (w : List (Fin d)),
      Matrix.trace (evalWord (A k) w) = Matrix.trace (evalWord (B k) w) := by
  sorry

/-- **Per-block SameMPV from injective μ.**

If the scaling factors `μ k` are pairwise distinct and nonzero, and the
block-diagonal tensors generate the same MPV family, then each individual
block tensor generates the same MPV as its counterpart. -/
theorem sameMPV_of_sameMPV₂_injective
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_ne : ∀ k, μ k ≠ 0)
    (hμ_inj : Function.Injective μ)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) := by
  -- Apply the algebraic separation lemma
  have h_trace := per_block_trace_eq_of_summed_blocks μ A B hμ_ne hμ_inj hSame₂
  -- Unfold SameMPV and use the per-block trace equality
  intro k N σ
  -- mpv (A k) σ = coeff (A k) (List.ofFn σ) = tr(evalWord (A k) (List.ofFn σ))
  simp only [mpv, coeff]
  exact h_trace k (List.ofFn σ)

end Separation

/-! ### Multi-block Fundamental Theorem without `hSep` -/
section NoSep

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- **Multi-block Fundamental Theorem without the separation hypothesis.**

Under the assumptions that:
- Each block tensor `A k` is injective
- The scaling factors `μ k` are pairwise distinct (`μ` injective)
- The scaling factors are all nonzero
- The block-diagonal tensors generate the same MPV₂ family

we conclude:
- Per-block gauge equivalence: `GaugeEquiv (A k) (B k)` for all `k`
- Global gauge equivalence of the block-diagonal tensors -/
theorem fundamentalTheorem_multiBlock_noSep
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hμ_ne : ∀ k, μ k ≠ 0)
    (hμ_inj : Function.Injective μ)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) := by
  have hSep := sameMPV_of_sameMPV₂_injective μ A B hμ_ne hμ_inj hSame₂
  exact ⟨fun k => fundamentalTheorem_singleBlock (hA k) (hSep k),
         fundamentalTheorem_multiBlock_global μ A B hA hSep⟩

/-- **Multi-block Fundamental Theorem with explicit gauge matrices** (no `hSep`). -/
theorem fundamentalTheorem_multiBlock_explicit_noSep
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hμ_ne : ∀ k, μ k ≠ 0)
    (hμ_inj : Function.Injective μ)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  have hSep := sameMPV_of_sameMPV₂_injective μ A B hμ_ne hμ_inj hSame₂
  exact fundamentalTheorem_multiBlock_explicit A B hA hSep

end NoSep

end MPSTensor
