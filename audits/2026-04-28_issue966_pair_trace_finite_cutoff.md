# Issue #966 — finite cumulative pair trace-separation step (2026-04-28)

## Scope

Issue #966 asks for the finite homogeneous pair trace-separation length

```lean
IsCanonicalFormBNT μ A →
  ∃ S, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S
```

from the BNT non-equivalence data.  The full homogeneous statement is still open.
This pass proves the finite-dimensional compactness part for the cumulative version:
if no nonzero trace functional annihilates all finite pair words, then a finite
cutoff already detects every nonzero test pair.

## Checked Lean progress

File: `TNLean/MPS/MPDO/BiCFDerivation.lean`

New public declarations:

- `MPSTensor.pairEvalWordTuple`
  - The pair word tuple `(A^w, B^w)` for an arbitrary finite word `w`.

- `MPSTensor.pairCumulativeSpan`
- `MPSTensor.PairCumulativeWordTupleSpanTop`
  - The span of pair word tuples of length at most `S`, and the assertion that this span is the
    whole product matrix algebra.

- `MPSTensor.PairTraceSeparatingUpTo`
  - Cumulative trace separation up to length `S`.

- `MPSTensor.PairTraceSeparatingAll`
- `MPSTensor.pairAllWordsSpan`
- `MPSTensor.PairAllWordsSpanTop`
  - All-length trace separation and its span formulation.

- `MPSTensor.pairEvalWordTuple_mem_pairCumulativeSpan`
- `MPSTensor.pairCumulativeSpan_mono`
- `MPSTensor.PairTraceSeparatingUpTo.mono`
- `MPSTensor.pairTraceSeparatingUpTo_of_pairTraceSeparatingAt`
  - Basic membership, monotonicity, and the implication from homogeneous to cumulative separation.

- `MPSTensor.pairCumulativeWordTupleSpanTop_of_pairTraceSeparatingUpTo`
- `MPSTensor.pairTraceSeparatingUpTo_of_pairCumulativeWordTupleSpanTop`
- `MPSTensor.pairCumulativeWordTupleSpanTop_iff_pairTraceSeparatingUpTo`
  - Finite cumulative trace duality, using the matrix trace pairing.

- `MPSTensor.pairCumulativeWordTupleSpanTop_of_pairWordTupleSpanTop`
- `MPSTensor.pairCumulativeWordTupleSpanTop_of_pairTraceSeparatingAt`
  - Homogeneous pair span or homogeneous trace separation implies the cumulative span statement at
    the same bound.

- `MPSTensor.pairAllWordsSpanTop_of_pairTraceSeparatingAll`
- `MPSTensor.pairTraceSeparatingAll_of_pairAllWordsSpanTop`
- `MPSTensor.pairAllWordsSpanTop_iff_pairTraceSeparatingAll`
  - All-length trace duality.

- `MPSTensor.exists_pairCumulativeWordTupleSpanTop_of_pairAllWordsSpanTop`
  - Finite-dimensional stabilization: if all finite pair words span the product algebra, then words
    up to some finite length already span.  The proof uses Noetherian stabilization of the increasing
    sequence of cumulative spans.

- `MPSTensor.exists_pairTraceSeparatingUpTo_of_pairTraceSeparatingAll`
- `MPSTensor.exists_pairTraceSeparatingUpTo_iff_pairTraceSeparatingAll`
- `MPSTensor.exists_forall_pairTraceSeparatingUpTo_of_forall_pairTraceSeparatingAll`
  - If all finite words trace-separate a pair, then some finite cumulative cutoff trace-separates it;
    for finitely many ordered block pairs, one may take a common cutoff.

Blueprint Chapter 14 now records the cumulative/all-length variants in
`def:pair_trace_separation_words` and adds
`lem:all_length_pair_trace_separation_finite_cutoff`.

## Remaining mathematical blocker

The new theorem closes the finite-dimensional stabilization for cumulative spans,
not the homogeneous word-length assertion used by the Route B selector construction.
To finish issue #966 one still needs a BNT/Burnside-Jacobson argument proving either:

1. the exact homogeneous statement `PairTraceSeparatingAt (A k) (A j) S` at one common length, or
2. an additional homogenization theorem that converts the finite cumulative cutoff supplied here into
   such a homogeneous length under the paper's normal-block hypotheses.

The expected paper path remains the one identified in the issue: BNT non-equivalence rules out a
nonzero trace functional surviving on all pair words; finite-dimensionality then supplies a finite
bound.  This PR formalizes the second sentence for the cumulative version.

## Source anchors

- `Papers/2011.12127/TN-Review-main.tex` lines 2115--2116 define block-injective canonical form by
  access to every element of the direct-sum block algebra.
- `Papers/2011.12127/TN-Review-main.tex` lines 2123--2128 state the parent-Hamiltonian BNT
  ground-space result after blocking and the block-diagonal boundary improvement.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 320--326 give the MPDO/biCF pair-separation
  analogue with the selector factor `δ_{j,j'}`; lines 340--344 cite the finite blocking theorem
  producing biCF.

## Validation

Local checks on branch `issue966-bnt-density`:

- `lake env lean TNLean/MPS/MPDO/BiCFDerivation.lean`
- `lake build TNLean.MPS.MPDO.BiCFDerivation TNLean.MPS.CanonicalForm.BlockDiagonalCommutant`
  - The first combined build timed out after completing `BiCFDerivation`; the immediate continuation
    built `BlockDiagonalCommutant` successfully.
- `lake build TNLean`
  - Before the final rebase, several continuations were needed because of the command timeout.  After
    rebasing onto current `origin/main`, the command completed successfully in one run.  Warnings were
    pre-existing `sorry` and line-length warnings in unrelated modules.
- `cd blueprint && leanblueprint web`
  - The normal run hit the existing local TikZ path-with-spaces problem in the SVG renderer.  Rerun
    with LaTeX hidden from `PATH` so the renderer emitted placeholder SVG messages; the web build then
    succeeded.
- `cd blueprint && leanblueprint checkdecls`
- `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls`
- `python3 scripts/blueprint_lean_sync.py --root . --ci`
