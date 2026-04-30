/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.BlocksMatch

/-!
# Full Fundamental Theorem of MPS — Heterogeneous Equal Case

This module contains **Theorem 5**: the self-contained equal-case fundamental theorem for
heterogeneous `IsCanonicalFormBNT` families. It is the entry point that exposes the
constructions developed in three supporting sub-modules and provides the public theorem
`fundamentalTheorem_equalMPV_CFBNT_hetero`.

For Theorems 1–4 (equal-MPV FT, proportional-MPV FT, equal ⟹ proportional, power-sum
multiset equality) and combined corollaries, see
`TNLean.MPS.FundamentalTheorem.EqualProportional`.

## Main statements

### Theorem 5: Self-contained equal-case FT for heterogeneous CF-BNT
(`fundamentalTheorem_equalMPV_CFBNT_hetero`)

Given two `IsCanonicalFormBNT` families with *different* block structures
(`rA`, `rB`, `dimA`, `dimB`, `μA`, `μB`), the hypothesis `SameMPV₂` alone (no coefficient
convergence data from the caller) forces block-count equality, a block permutation, and
blockwise gauge-phase equivalence.

## Implementation notes

The proof is split across three sub-modules for readability:

* `TNLean.MPS.FundamentalTheorem.Full.Helpers` — small overlap / inner-product helpers and
  the single-block Layer-2 gauge-phase equivalence lemma.
* `TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap` — Layer 1a,
  `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`, a strong induction on `rA + rB` using a
  dominant-weight projection argument.
* `TNLean.MPS.FundamentalTheorem.Full.BlocksMatch` — Layer 1b,
  `blocks_match_of_sameMPV₂_CFBNT`, which converts the non-decaying overlap data into a
  full `BlockPermutationGaugeWitness` via the overlap dichotomy.

## References

* Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
* Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017).

## Tags

matrix product states, fundamental theorem, BNT, heterogeneous, gauge-phase equivalence
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- **Self-contained equal-case Fundamental Theorem for heterogeneous CF-BNT**
([CPSV21, Corollary IV.5] / [CPSV17, Theorem 4.4 + equal-case corollary]).

Given two `IsCanonicalFormBNT` families with *different* block structures
(`rA`, `rB`, `dimA`, `dimB`, `μA`, `μB`), the hypothesis `SameMPV₂` for the assembled
block-diagonal tensors — with **no** coefficient convergence data from the caller —
forces:
1. Equal block counts: `rA = rB`.
2. A block permutation: `perm : Fin rA ≃ Fin rB`.
3. Blockwise gauge-phase equivalence: for each `j`, `dimA j = dimB (perm j)` and
   `GaugePhaseEquiv (cast … (A j)) (B (perm j))`.

Unlike `fundamentalTheorem_proportionalMPV_CFBNT` and `fundamentalTheorem_equalMPV_full`,
this theorem requires **no** explicit `aCoeff`, `bCoeff`, `aLim`, `bLim` arguments. The
coefficient convergence question that plagues the general proportional-case theorem is
bypassed entirely: the BNT decomposition identity
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
theorem fundamentalTheorem_equalMPV_CFBNT_hetero
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    BlockPermutationGaugeWitness (d := d) A B :=
  blocks_match_of_sameMPV₂_CFBNT A B hA hB hEqual

end MPSTensor
