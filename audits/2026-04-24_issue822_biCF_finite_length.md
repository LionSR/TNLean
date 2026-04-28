# Issue #822 — biCF finite-length wave 9 audit (2026-04-24)

## Outcome of this pass

The requested theorem

```lean
∃ L, LinearIndependent ℂ (MPSTensor.wordEntryFamily A L)
```

cannot be derived from the current `origin/main` hypotheses
`HorizontalCFData.block_injective` + `HorizontalCFData.left_canonical` alone.
On the present repository state that implication is **false**, so the honest
outcome here is a conditional endpoint plus a formal obstruction theorem.

## What landed

### Lean

Ported the word-entry endpoint from the earlier Prop. IV.3 work into
`TNLean/MPS/MPDO/BiCFDerivation.lean`:

- `MPSTensor.BlockEntryIndex`
- `MPSTensor.blockEntryValue`
- `MPSTensor.wordEntryFamily`
- `MPSTensor.hasBlockSelectorWords_of_wordTupleSpanTop`
- `MPSTensor.wordTupleSpanTop_of_wordEntryFamily_linearIndependent`
- `MPSTensor.hasBlockSelectorWords_of_wordEntryFamily_linearIndependent`
- `MPSTensor.hasBiCF_of_wordEntryFamily_linearIndependent`
- `MPOTensor.horizontalCFData_of_wordEntryFamily_linearIndependent`

Added a **formal obstruction** to the stronger Issue-#822 target:

- `MPSTensor.duplicateScalarBlocks_isInjective`
- `MPSTensor.duplicateScalarBlocks_leftCanonical`
- `MPSTensor.duplicateScalarWeights_ne_zero`
- `MPSTensor.duplicateScalarBlocks_not_linearIndependent_wordEntryFamily`
- `MPSTensor.duplicateScalarBlocks_no_wordEntryFamily_linearIndependent`
- `MPSTensor.duplicateScalarBlocks_counterexample`

### Docs

- updated the `HorizontalCFData.biCF` docstring in `TNLean/MPS/MPDO/VerticalCF.lean`
  so it describes the current honest constructor surface (`WordTupleSpanTop`,
  `PropBlockInjective`, `wordEntryFamily`) instead of claiming the remaining
  derivation is already available;
- updated the blueprint remark in `blueprint/src/chapter/ch02b_mpdo.tex` to
  mention the `wordEntryFamily` endpoint.

## Why the requested theorem is false on current hypotheses

Take

- `r = 2`,
- `d = 1`,
- `dim k = 1` for both blocks,
- both blocks equal to the same scalar tensor `A_k(0) = 1`,
- nonzero weights `μ 0 = 1`, `μ 1 = 2`.

Then:

1. each block is injective;
2. each block is left-canonical;
3. each weight is nonzero;
4. but for every length `L`, there is only one word `w : Fin L → Fin 1`, and the
   two block-entry functionals in `wordEntryFamily A L` are equal.

Hence `MPSTensor.wordEntryFamily A L` is **never** linearly independent. The new
Lean theorem `duplicateScalarBlocks_no_wordEntryFamily_linearIndependent` records
this formally.

So no theorem of the form

```lean
(∀ k, IsInjective (A k)) →
(∀ k, left_canonical ...) →
∃ L, LinearIndependent ℂ (MPSTensor.wordEntryFamily A L)
```

can be true without an additional separation hypothesis.

## Concrete missing lemma

The real missing input is a finite-length **block-separation** theorem from
separated canonical-form / BNT data, for example from hypotheses of the shape

```lean
HasInjectiveBlocks A
∧ IsLeftCanonicalBlockFamily A
∧ BlocksNotGaugePhaseEquiv A
```

(or an equivalent Proposition-IV.3 selector package), producing a finite length
`L` with

```lean
LinearIndependent ℂ (MPSTensor.wordEntryFamily A L).
```

The explicit paper-faithful bound `L ≤ 3 * D^5` would further require a blocked
mixed-transfer / Wielandt-style quantitative theorem that is not yet present in
`TNLean/Wielandt/` or `TNLean/MPS/BNT/`.

## Most plausible next route

1. define the matrix-inserted word states corresponding to each block entry;
2. prove cross-sector overlap decay using `BlocksNotGaugePhaseEquiv`;
3. prove within-sector Gram convergence to a nondegenerate limit form;
4. apply
   `TNLean.Algebra.GramMatrixLI.eventually_linearIndependent_of_gram_tendsto_nondegenerate`;
5. convert the resulting finite `L` into `WordTupleSpanTop`, then into `HasBiCF`;
6. if the quantitative mixed-transfer theorem is later formalized, sharpen this
   existential witness to the paper bound `L ≤ 3 * D^5`.

## Validation

Commands run in this pass:

- `lake env lean TNLean/MPS/MPDO/BiCFDerivation.lean`
- `lake build TNLean.MPS.MPDO.BiCFDerivation TNLean.MPS.MPDO.VerticalCF`
- `rm -rf .lake/build/ir && lake build`
