# Pass-through declarations that forwarded to `Kraus` (2026-11-16)

Issue #10722, step 0.6 of `docs/many_body_circuit_architecture.md`, asked for
the removal of the TNLean declarations whose whole body applies one
declaration of the `Kraus` namespace to the declaration's own arguments: the
same statement under a second name, left from the extraction of QICLean. No
deprecated alias is kept (`docs/project_conventions.md`).

## Removed declarations and replacements

All in `TNLean/MPS/Core/Blocking.lean`, each replaced by the declaration of the
same name in `QICLean/Kraus/Blocking.lean`:

| Removed | Kind | Replacement |
|---|---|---|
| `MPSTensor.blockPhysDim` | abbreviation | `Kraus.blockPhysDim` |
| `MPSTensor.blockPhysDim_eq_pow` | lemma | `Kraus.blockPhysDim_eq_pow` |
| `MPSTensor.singleBlockEquiv` | abbreviation | `Kraus.singleBlockEquiv` |
| `MPSTensor.decodeBlock` | abbreviation | `Kraus.decodeBlock` |
| `MPSTensor.wordOfBlock` | abbreviation | `Kraus.wordOfBlock` |
| `MPSTensor.length_wordOfBlock` | lemma | `Kraus.length_wordOfBlock` |
| `MPSTensor.decodeBlockEquiv` | abbreviation | `Kraus.decodeBlockEquiv` |
| `MPSTensor.decodeBlockEquiv_apply` | lemma | `Kraus.decodeBlockEquiv_apply` |
| `MPSTensor.decodeBlock_decodeBlockEquiv_symm` | lemma | `Kraus.decodeBlock_decodeBlockEquiv_symm` |
| `MPSTensor.blockTensor` | abbreviation | `Kraus.blockTensor` |
| `MPSTensor.isNBlkInjective_iff_blockTensor_isInjective` | lemma | `Kraus.isNBlkInjective_iff_blockTensor_isInjective` |
| `MPSTensor.flattenBlockedWord` | abbreviation | `Kraus.flattenBlockedWord` |
| `MPSTensor.flattenBlockedWord_nil` | lemma | `Kraus.flattenBlockedWord_nil` |
| `MPSTensor.flattenBlockedWord_cons` | lemma | `Kraus.flattenBlockedWord_cons` |
| `MPSTensor.evalWord_blockTensor` | lemma | `Kraus.evalWord_blockTensor` |
| `MPSTensor.length_flattenBlockedWord` | lemma | `Kraus.length_flattenBlockedWord` |
| `MPSTensor.evalWord_replicate` | lemma | `Kraus.evalWord_replicate` |

In `TNLean/MPS/Preparation/RectangularBlocks.lean`, each replaced by the
declaration of the same name in `QICLean/Kraus/RectangularChain.lean`:

| Removed | Kind | Replacement |
|---|---|---|
| `MPSChainTensor.rectangularEval` | abbreviation | `Kraus.rectangularEval` |
| `MPSChainTensor.rectangularTransfer` | abbreviation | `Kraus.rectangularTransfer` |
| `MPSChainTensor.rectangularTransfer_apply` | theorem | `Kraus.rectangularTransfer_apply` |

`MPSTensor.decodeBlockEquiv_apply` was proved by `rfl`, not by an application
of its target; it is listed because, once the abbreviations are gone, its
statement is `Kraus.decodeBlockEquiv_apply` character for character.

## How the callers were rewritten

* Every qualified use `MPSTensor.x` of a removed name is now `Kraus.x`.
* A file that reached a removed name through `namespace MPSTensor` or
  `open MPSTensor` now has one line `open Kraus (...)` listing exactly the
  removed names it uses unqualified. The selective form opens nothing else of
  `Kraus`, so no other name in the file changes its resolution.
* Inside a namespace that has its own declaration of the same short name
  (`MPSTensor.IsReduction.blockTensor`, `MPSTensor.GaugeEquiv.blockTensor`, and
  the like) the unqualified name no longer reaches past it, and the use is
  written `Kraus.blockTensor`.
* The removed definitions were reducible abbreviations of definitions that are
  not reducible. Where a proof unfolded the abbreviation by name, the unfolding
  step was dropped or replaced by the `Kraus` lemma that states the needed
  equation.

Blueprint tags of `def:blocked_tensor`, `lem:eval_word_block`,
`lem:isNBlkInjective_iff_blockTensor_isInjective`, `def:mpdo_word_of_block`,
`lem:mpdo_length_word_of_block` and `thm:ldp_rectangular_blocking` now cite the
`Kraus` names, as do the two sanctioned-bridge entries of `docs/glossary.md`.

## Candidates examined and kept

A pattern match for "the body starts with one `Kraus` declaration" returns
about sixty declarations. The ones below are not pass-throughs, or are left
for a decision.

Left for a decision:

* `MPSTensor.IsPrimitiveMPS`, an abbreviation of
  `Kraus.HasComplementaryFixedPointGap`. Which of the two names survives is
  open (`docs/audits/2026-11-16_primitivity_one_definition.md`).
* `MPSTensor.IsLeftCanonical`, an abbreviation of `Kraus.IsTP`. It is the
  tensor-network name of the condition and carries about a thousand uses.
* `MPSTensor.exists_rankOne_mem_wordSpan_blockTensor`
  (`TNLean/Wielandt/RankOne/ExtractionFull.lean`). It applies the `Kraus`
  theorem of the same name after restating the hypothesis
  `Kraus.wordSpan A N₀ = ⊤` as `Kraus.IsNBlkInjective A N₀`. The two
  hypotheses are equal by definition, but the statement is spelled differently.

Not pass-throughs:

* Specializations to a tensor obtained from the argument:
  `MPOTensor.IsInjective` (`Kraus.IsInjective K.toMPSTensor`),
  `MPSChainTensor.IsInjective`, `MPOTensor.transferMap_pos`,
  `MPOTensor.faithfulFixedPointSupportAlgebra`, `MPOTensor.blockedTransferMap`,
  `MPSTensor.fnwTransferMap` (the transfer map of the adjoint family) and
  `MPSTensor.fnwTransferMap_eq_traceAdjointMap`.
* Facts about one explicit tensor, proved by one `Kraus` lemma applied to that
  tensor: the non-injectivity statements of the AKLT, even-parity, GHZ, Kitaev
  and Majumdar–Ghosh examples, the channel statements of the refinement
  counterexamples, `evalWord_stateTensor`, and the word-span memberships of
  the AKLT, cluster and cyclic examples.
* Definitions whose body is an expression in `Kraus` definitions rather than
  one of them: the blocked and reindexed example tensors, `blockHead`,
  `blockTail`, `tensorProductBlockEquiv`, `pairWordTuple`, `pairEvalWordTuple`,
  `wallChain`, `fourWallCoeff`, `nestedWallCoeff`, the two-wall transfer maps,
  `IsTransferIdempotent`, `mixedMapLMLeft`, `krausRank`.
* Theorems with a different hypothesis set or conclusion from the lemma they
  call: `physRealize_spec`, `physRealizeLeft_spec`,
  `isIrreducibleMap_mapLM_blocks_conjTranspose`,
  `irreducibleTensor_of_injective`, `isIrreducibleFamily_of_isNormal`,
  `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef`,
  `mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one`,
  `mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP`,
  `gaugePhaseEquiv_of_gauged_intertwining`.
