# Issue #823 progress note — commuting-form local-to-global bridge (v2)

## What this branch adds

This branch introduces a new file
`TNLean/MPS/MPDO/CommutingFormBridge.lean` that formalizes the strongest honest
forward step currently justified on `origin/main` for Appendix C.2,
Proposition C.6:

- `MPOTensor.TranslationInvariantBondData`
- `MPOTensor.EtaLocalStructureData`
- `MPOTensor.hasCommutingForm_of_etaLocalStructure`
- `MPOTensor.isGSNNCH_of_etaLocalStructure`

The central idea is to package the **post-extraction local data** that the
paper obtains from SAL + ZCL: a single positive two-site bond `B` whose
translated copies commute on every periodic chain and realize the MPO at every
finite length. From this interface the global commuting-form / GSNNCH
conclusions are immediate.

## Why this is honest but still partial

The current repository already has the entropy-side local ingredients in
`SimpleLocalStructure.lean`:

- `MPOTensor.EtaStructure`
- `MPOTensor.sal_implies_eta_structure`
- `MPOTensor.sal_zcl_implies_rank_one_T`

However, issue #833 is still open: the project does **not yet** convert the
Hayashi `QuantumMarkovDecomposition` into the explicit neighboring operators
`η_{k,h}` used in Appendix C.2, Lemma C.3 and Proposition C.6.

Therefore this branch does **not** claim that the existing SAL + ZCL lemmas by
themselves already prove `HasCommutingForm`. Instead, it isolates the exact
next bridge object that the future `η_{k,h}` extraction theorem should build.

## Remaining gap after this branch

To obtain the paper-faithful SAL + ZCL statement, one still needs a theorem of
the form

```lean
-- schematic shape
etaLocalStructure_of_sal_zcl :
  -- local SAL / ZCL hypotheses and simple-MPDO inverse-map data
  ... → MPOTensor.EtaLocalStructureData M
```

Once that exists, the already formalized theorem
`MPOTensor.hasCommutingForm_of_etaLocalStructure` immediately yields the global
commuting-form conclusion.

## Files touched

- `TNLean/MPS/MPDO/CommutingFormBridge.lean` (new)
- `TNLean.lean`
- `blueprint/src/chapter/ch02b_mpdo.tex`

## Validation target

The new file should compile on its own and via `TNLean.lean`; blueprint
`checkdecls` should see the new declarations.
