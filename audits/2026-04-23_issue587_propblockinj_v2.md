# Issue #587 — Prop IV.3 / biCF derivation v2 audit (2026-04-23)

## Scope of this pass

This pass does **not** delete the `biCF` field from `MPOTensor.HorizontalCFData`.
Instead it adds a substantive finite-dimensional reduction step in
`TNLean/MPS/MPDO/BiCFDerivation.lean` and sharpens the remaining blocker.

## What landed in Lean

New declarations in `TNLean/MPS/MPDO/BiCFDerivation.lean`:

- `MPSTensor.BlockEntryIndex`
- `MPSTensor.blockEntryValue`
- `MPSTensor.wordEntryFamily`
- `MPSTensor.hasBlockSelectorWords_of_wordTupleSpanTop`
- `MPSTensor.wordTupleSpanTop_of_wordEntryFamily_linearIndependent`
- `MPSTensor.hasBlockSelectorWords_of_wordEntryFamily_linearIndependent`
- `MPSTensor.hasBiCF_of_wordEntryFamily_linearIndependent`
- `MPOTensor.horizontalCFData_of_wordEntryFamily_linearIndependent`

Mathematical content:

1. The old abstract route
   $$\texttt{WordTupleSpanTop} \Rightarrow \texttt{HasBiCF}$$
   is now complemented by the new concrete route
   $$\texttt{LinearIndependent}\bigl(\texttt{wordEntryFamily } A\,L\bigr)
     \Rightarrow \texttt{WordTupleSpanTop } A\,L.$$
2. Since `wordEntryFamily A L` indexes **every block matrix entry** across the whole
   family, its linear independence exactly gives a dual coefficient family on the
   finite word space. Those dual coefficients reconstruct arbitrary tuples of block
   matrices, hence force `WordTupleSpanTop`.
3. As corollaries, the same linear-independence criterion yields block selectors,
   a `HasBiCF` witness, and a direct `HorizontalCFData`.

So the issue is now reduced to a more precise criterion than the earlier abstract
selector data: it is enough to prove

> `∃ L, LinearIndependent ℂ (MPSTensor.wordEntryFamily A L)`

from the canonical-form/BNT hypotheses of CPGSV17 Proposition IV.3.

## Why this still does not close #587

The remaining gap is **not** a generic linear-algebra reduction issue anymore.
It is the actual block-separation theorem from CPGSV17 / David2006.

The current `HorizontalCFData` fields still do **not** imply `biCF` directly; the
counterexample already documented in `BiCFDerivation.lean` remains valid.
What is missing is a theorem that produces finite-length separation between the
full families of inserted/block-entry word functionals for distinct BNT sectors.

A clean target statement for the next PR is:

```lean
∃ L : ℕ, LinearIndependent ℂ (MPSTensor.wordEntryFamily A L)
```

for a block family `A` satisfying the relevant canonical-form/BNT minimality
hypotheses (pairwise non-gauge-phase-equivalent sectors, normality/injectivity
after blocking, etc.).

## Best next proof route

The most plausible in-repo route is the Gram-limit strategy already suggested by
existing infrastructure:

1. Define matrix-inserted trace/word states for each block-entry basis element.
2. Prove off-diagonal overlap decay between different BNT sectors using the
   canonical/BNT separation machinery.
3. Prove that within one sector the Gram matrix tends to a nondegenerate limit
   coming from the positive-definite fixed point.
4. Apply
   `TNLean.Algebra.GramMatrixLI.eventually_linearIndependent_of_gram_tendsto_nondegenerate`
   to obtain eventual linear independence of the whole block-entry family.
5. Convert that eventual linear independence at some finite length `L` into
   `wordTupleSpanTop A L` by the new theorem added in this pass.

## Exact paper / repo blocker reference

Paper statement:

- `Papers/1606.00608/MPDO-22-12-17-2.tex:342-345`
  Proposition `propblockinj`: after blocking at most `3 D^5` spins, any tensor in
  CF is in biCF.

Current repo-side missing criterion:

- no theorem in `TNLean/MPS/BNT/` or `TNLean/MPS/CanonicalForm/` currently produces
  finite-length linear independence of the **block-entry** word family, or the
  equivalent `WordTupleSpanTop`/selector data, from BNT minimality.

## Status

This pass is substantive forward progress, not a vacuous alias: it proves that one
concrete finite-dimensional criterion (`wordEntryFamily` linear independence) is
already sufficient to obtain the full abstract `biCF` witness. But the pass does
**not** yet derive that criterion from the paper's hypotheses, so issue #587 stays open.
