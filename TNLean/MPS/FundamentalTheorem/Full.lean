/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.BlocksMatch

/-!
# Heterogeneous BNT block matching

This module contains the heterogeneous block-matching lemma for canonical-form BNT
families.  It exposes the constructions developed in three supporting sub-modules and
provides the public lemma `fundamentalTheorem_equalMPV_CFBNT_hetero`.

The source-paper equal-MPV corollary is stronger: after the BNT blocks have been matched,
it compares the repeated-copy coefficients and obtains one global gauge for the original
canonical-form tensors.  The lemma in this file proves the block-count, dimension, and
gauge-phase matching part only.

For common-block and proportional comparison lemmas, see
`TNLean.MPS.FundamentalTheorem.EqualProportional`.

## Main statements

### Heterogeneous equal-MPV block matching
(`fundamentalTheorem_equalMPV_CFBNT_hetero`)

Given two `IsCanonicalFormBNT` families with *different* block structures
(`rA`, `rB`, `dimA`, `dimB`, `μA`, `μB`), the hypothesis `SameMPV₂` alone (no coefficient
convergence data from the caller) forces block-count equality, a block permutation, and
blockwise gauge-phase equivalence.  It does not yet produce the global weighted gauge
conclusion of Corollary II.2 in the source paper.

## Implementation notes

The proof is split across supporting sub-modules for readability:

* `TNLean.MPS.FundamentalTheorem.Full.DominantWeight` — the largest-weight norm
  comparison used by the dominant-block projection, together with small
  overlap / inner-product auxiliary lemmas.
* `TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap` — Layer 1a,
  `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`, a strong induction on `rA + rB` using a
  dominant-weight projection argument.
* `TNLean.MPS.FundamentalTheorem.Full.BlocksMatch` — Layer 1b,
  `blocks_match_of_sameMPV₂_CFBNT`, which converts the non-decaying overlap data into a
  full `ProportionalDecompositionConclusion` via the overlap dichotomy.

## References

* Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
* Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017).

## Tags

matrix product states, BNT, heterogeneous, block matching, gauge-phase equivalence
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- **Heterogeneous equal-MPV block matching for CF-BNT families.**

Given two `IsCanonicalFormBNT` families with *different* block structures
(`rA`, `rB`, `dimA`, `dimB`, `μA`, `μB`), the hypothesis `SameMPV₂` for the assembled
block-diagonal tensors, with no coefficient convergence data from the caller,
forces:
1. Equal block counts: `rA = rB`.
2. A block permutation: `perm : Fin rA ≃ Fin rB`.
3. Blockwise gauge-phase equivalence: for each `j`, `dimA j = dimB (perm j)` and
   `GaugePhaseEquiv (cast … (A j)) (B (perm j))`.

**Scope restriction (one-copy-per-sector)**: This is not the full equal-MPV Corollary II.2 of
arXiv:1606.00608.  The `IsCanonicalFormBNT` hypothesis forces `mu_strict_anti`, which fixes one
block per modulus class (`r_j = 1`).  Consequently: (a) the Newton–Girard multiplicity recovery
(`Lem:app_simple` on `∑_q μ_{j,q}^N`) is bypassed; (b) the global gauge `Y = ⊕_j Id_{r_j} ⊗ Y_j`
is never assembled; the conclusion is per-block `GaugePhaseEquiv` only.  The proof of this
restricted version is **complete (no sorry)**.  For the general route see issue #1559 and
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`.  The BNT decomposition identity
  `∑_j (μA j)^N * mpv(A j) σ = ∑_k (μB k)^N * mpv(B k) σ`
is analyzed directly via the overlap dichotomy (CPSV17 Appendix A), yielding per-block
gauge-phase matching.

### Proof structure

The proof delegates to `blocks_match_of_sameMPV₂_CFBNT`, which is fully proved:

- Base cases `rA = 0` or `rB = 0`: linear independence + vanishing sum → contradiction.
- Non-decaying overlap existence: `exists_nondecaying_overlap_of_sameMPV₂_CFBNT` via
  strong induction on `rA + rB` with a dominant-weight projection argument (CPSV17
  Appendix A): project onto `mpvState(B 0, N)`, derive `‖μA 0‖ = ‖μB 0‖`, match
  dominant blocks, subtract, and recurse on the tail families.
- Overlap dichotomy (dim mismatch → decay, non-GPE → decay): fully proved.
- Matching injectivity (BNT separation + GPE cross-overlap norm → 1): fully proved.
- `rA = rB` (injective maps on finite types): fully proved.
- Permutation construction and per-block data extraction: fully proved. -/
-- SCOPE(one-copy-per-sector): r_j=1 via IsCanonicalFormBNT; complete but restricted.
-- Multiplicity recovery (Lem:app_simple) and global gauge assembly absent. See #1559.
lemma fundamentalTheorem_equalMPV_CFBNT_hetero
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ProportionalDecompositionConclusion A B :=
  blocks_match_of_sameMPV₂_CFBNT A B hA hB hEqual

end MPSTensor
