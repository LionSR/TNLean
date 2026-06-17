# Issue #934 — pair trace-separation predecessor (2026-04-27)

## Scope

Wave 18 Slot C targeted the remaining Route B parent-Hamiltonian step

```lean
IsCanonicalFormBNT μ A → ∃ S, HasPairBlockSeparatingWords A S
```

or equivalently a direct construction of finite block-selector words from separated
CF/BNT data.  The full implication from `blocks_not_equiv` is still not proved in
this pass.  What is now checked is the finite-dimensional **dual trace criterion**
immediately preceding the pairwise selector theorem.

## Checked Lean progress

File: `TNLean/MPS/MPDO/BiCFDerivation.lean`

New public declarations:

- `MPSTensor.pairWordTuple`
  - The two-block homogeneous word tuple `w ↦ (evalWord A w, evalWord B w)` at a fixed length.

- `MPSTensor.PairWordTupleSpanTop`
  - Pair-level product-algebra span: the length-`S` pair word tuples span
    `M_{D₁}(ℂ) × M_{D₂}(ℂ)`.

- `MPSTensor.PairTraceSeparatingAt`
  - The dual trace-separation criterion: the only pair of matrices `(ΔA, ΔB)` whose trace pairing
    with every length-`S` pair tuple vanishes is `(0,0)`.

- `MPSTensor.pairWordTupleSpanTop_of_pairTraceSeparatingAt`
  - Proves the trace criterion is strong enough to give pair product-span.  The proof uses
    `Submodule.exists_le_ker_of_lt_top` and represents a nonzero annihilating functional by the
    matrix trace pairing.

- `MPSTensor.hasBlockSelectorOn_of_pairWordTupleSpanTop`
  - Extracts the tuple `(I,0)` from pair product-span and reuses its coefficients on the ambient
    block family to get `HasBlockSelectorOn A k S {j}`.

- `MPSTensor.hasBlockSelectorOn_of_pairTraceSeparatingAt`
  - Combines the two previous facts.

- `MPSTensor.hasPairBlockSeparatingWords_of_forall_pairWordTupleSpanTop`
- `MPSTensor.hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt`
- `MPSTensor.exists_hasPairBlockSeparatingWords_of_exists_forall_pairTraceSeparatingAt`
  - Common-length pair criteria for all ordered distinct pairs imply `HasPairBlockSeparatingWords`.

File: `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean`

New Route-B-facing compositions:

- `MPSTensor.wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt`
- `MPSTensor.exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt`

These say that once the pair trace-separation criterion is proved at a common finite length under
CF/BNT hypotheses, the already-merged pairwise selector assembly gives the issue-#934 product-word
span needed by Route B.

Blueprint Chapter 14 now records:

- `def:pair_trace_separation_words`
- `lem:pair_trace_separation_to_pairwise_selectors`

and adds the trace-separation route to `lem:product_word_span_from_bnt_selectors`.

## Remaining mathematical blocker

The real paper step is now isolated as the homogeneous finite-dimensional
Burnside/Jacobson-density statement:

```lean
IsCanonicalFormBNT μ A →
  ∃ S, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S
```

A pairwise version under split hypotheses would be:

```lean
IsInjective A → IsInjective B →
left-canonical A → left-canonical B →
¬ GaugePhaseEquiv A B →
∃ S, PairTraceSeparatingAt A B S
```

with casts/equal-dimension bookkeeping, plus the dimension-mismatch branch.  This is not a
convenience assumption: it is exactly the assertion that no nonzero trace functional survives on all
homogeneous pair words.  In algebraic terms, the simultaneous homogeneous word representation of two
non-gauge-equivalent simple matrix blocks must contain enough words of one common length to separate
`(I,0)`.

The expected proof route is:

1. Use BNT separation (`blocks_not_equiv`) and the existing mixed-transfer/spectral-gap
   infrastructure to rule out a nonzero asymptotically nondecaying mixed trace functional.
2. Convert the absence of such functionals into a finite length `S`; finite-dimensionality should
   turn the infinite homogeneous annihilator intersection into a finite cutoff.
3. Apply `pairWordTupleSpanTop_of_pairTraceSeparatingAt` and
   `hasBlockSelectorOn_of_pairTraceSeparatingAt`.
4. Use the already-checked pairwise selector assembly from PR #950.

## Source references

- `Papers/2011.12127/TN-Review-main.tex` lines 2115--2116 define block-injective canonical form
  by access to every element of the direct-sum block algebra:

  > `A tensor A is in block injective canonical form ... for each element X\in \bigoplus_{j=1}^g ...`

- `Papers/2011.12127/TN-Review-main.tex` lines 2123--2128 state the parent-Hamiltonian BNT
  ground-space result and the strengthened `N ≥ L_0+1` version after restricting to block-diagonal
  boundary conditions.

- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 320--326 give the MPDO/biCF analogue, including
  the inverse tensor identity with the extra `δ_{j,j'}` block selector factor.  Lines 340--344 cite
  the finite blocking theorem producing biCF.

## Validation

Checks run on branch `wave18-C-934-bnt-separators`:

- `lake exe cache get`
- `lake env lean TNLean/MPS/MPDO/BiCFDerivation.lean`
- `lake build TNLean.MPS.MPDO.BiCFDerivation TNLean.MPS.CanonicalForm.BlockDiagonalCommutant`
  - The first two build attempts reached the command timeout after building dependencies; the
    immediate continuation completed successfully.
- `lake env lean TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean && lake env lean \
  TNLean/MPS/MPDO/BiCFDerivation.lean`

Further blueprint and repository hygiene checks are recorded in the PR validation summary.
