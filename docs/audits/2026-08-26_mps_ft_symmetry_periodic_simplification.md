# Fundamental-theorem, symmetry, and periodic simplification sweep (2026-08-26)

This note records the removals made in the fundamental-theorem, symmetry, and
periodic area under the pass-through exception of
`docs/project_conventions.md` §Style, which requires that every removed
declaration be named here together with its replacement.

Verification for the whole sweep: `lake build` completed successfully with the
package lean options (no new warnings on the touched files),
`rg -n "sorry|axiom"` is clean on all nine touched files, and
`leanblueprint checkdecls` passes after regenerating `blueprint/lean_decls`.

## 1. Superseded positive-weight irreducible-form witness

`TNLean/MPS/Periodic/NormalCanonicalPeriodOne.lean`

| Removed | Replacement |
|---|---|
| `MPSTensor.toIsIrreducibleFormOfWeightPos` | `MPSTensor.toIsIrreducibleFormOfPhaseNormalized` |
| `MPSTensor.toIsIrreducibleFormOfWeightPos_period_eq_one` | `MPSTensor.toIsIrreducibleFormOfPhaseNormalized_period_eq_one` |

The removed pair assumed positive real weights outright; the surviving pair
absorbs the phase of each nonzero weight into its block and then applies the
same argument, so it carries the weaker hypothesis. `rg -w` over `TNLean/`
(excluding `Archive/`), `blueprint/src/`, and `scripts/` found no reference to
either name outside its own defining file. The paper-gap note
`docs/paper-gaps/dccsp17_normal_canonical_irreducible_form_weights.tex` and
the blueprint remark `rem:irr_form_vs_ncf` already cite only the surviving
phase-normalized pair, so no gap or blueprint edit was needed.

## 2. Periodic-tensor alias namespace

`TNLean/MPS/Periodic/Defs.lean`

Every member of the `MPSTensor.PeriodicMPSTensor` namespace forwarded to the
chain-level declaration of the same name, and none had a Lean consumer.

| Removed | Replacement |
|---|---|
| `MPSTensor.PeriodicMPSTensor` | `MPSChainTensor` |
| `MPSTensor.PeriodicMPSTensor.toChain` | none — dead; the inline `fun _ => A` writes it out |
| `MPSTensor.PeriodicMPSTensor.coeff` | `MPSChainTensor.coeff` |
| `MPSTensor.PeriodicMPSTensor.SameState` | `MPSChainTensor.SameState` |
| `MPSTensor.PeriodicMPSTensor.GaugeEquiv` | `MPSChainTensor.GaugeEquiv` |
| `MPSTensor.PeriodicMPSTensor.instEquivalenceSameState` | `MPSChainTensor.instEquivalenceSameState` |
| `MPSTensor.PeriodicMPSTensor.instEquivalenceGaugeEquiv` | `MPSChainTensor.instEquivalenceGaugeEquiv` |

Five blueprint `\lean{...}` tags in `blueprint/src/chapter/ch02_mps.tex` were
redirected to the survivors in the same change (labels
`def:periodic_mps_tensor`, `def:periodic_relations`,
`lem:periodic_relation_equivalences`); all prose, `\uses` edges, and `\leanok`
marks are unchanged, since the surviving declarations state exactly the same
mathematics.

`import TNLean.MPS.Chain.Defs` was deliberately kept in
`TNLean/MPS/Periodic/Defs.lean`: `TNLean/MPS/Periodic/StateVectorDecomposition.lean`
reaches `MPSChainTensor` only transitively through this import.

## 3. Zero-reference declarations

Each of the following had no reference in `TNLean/` (excluding `Archive/`),
`blueprint/src/`, or `scripts/` other than its own definition; the only other
mentions are historical snapshots under `docs/audits/`, left in place.

| Removed | File | Replacement |
|---|---|---|
| `MPSTensor.piTensorProduct_eq_smul_of_cyclic_products` | `MPS/Periodic/Overlap/SectorMatch/CyclicTrace.lean` | none — unreferenced |
| `MPSTensor.sameMPV₂_single_block` | `MPS/FundamentalTheorem/ProductAlgebra.lean` | none — unreferenced |
| `MPSTensor.fundamentalTheorem_singleBlock_fromMPV₂` | `MPS/FundamentalTheorem/ProductAlgebra.lean` | none — unreferenced |
| `MPSTensor.SectorBNT.Examples.signFlipDecomp_weight_unit_per_block` | `MPS/FundamentalTheorem/SectorBNT/Examples.lean` | none — unreferenced |
| `MPSTensor.SectorBNT.Examples.halvedDecomp_weight_unit_per_block` | `MPS/FundamentalTheorem/SectorBNT/Examples.lean` | none — unreferenced |
| `MPSTensor.BasisOfPeriodicTensors` | `MPS/Periodic/Defs.lean` | none — unreferenced |
| `MPSTensor.gaugePhaseEquiv_to_repeatedBlocks_of_leftCanonical_irreducible` | `MPS/Periodic/Overlap/GaugePhase.lean` | none — unreferenced |
| `MPSTensor.cornerProd_single` | `MPS/Periodic/CornerTransition.lean` | none — unreferenced |

`sameMPV₂_single_block` was cited only by `fundamentalTheorem_singleBlock_fromMPV₂`,
which is removed in the same change; the surviving general route through
`fundamentalTheorem_singleBlock` is unaffected. The two
`weight_unit_exists := by ...` structure fields in `Examples.lean` are live
instance fields and were left untouched.

Follow-on: `MPSTensor.sameMPV₂_summed_blocks`
(`TNLean/MPS/FundamentalTheorem/ProductAlgebra.lean`) becomes zero-reference
once `sameMPV₂_single_block` is gone; it is left in place for a separate
review rather than widened into this change.

## 4. Unconsumed prepared-block adapters

`TNLean/MPS/FundamentalTheorem/SectorBNT/Supplier.lean`

Three bundled adapters over `PreparedBNTBlocks` were added without a consumer
and still have none. Each is a one-line application of the corresponding
unbundled supplier in the same file, so the replacement is that supplier
applied to the structure's fields at the use site.

| Removed | Replacement |
|---|---|
| `MPSTensor.PreparedBNTBlocks.isBNTCanonicalForm_collapsed` | `MPSTensor.isBNTCanonicalForm_collapsedBntSectorDecomp_of_tp_primitive_irr_blocks` |
| `MPSTensor.PreparedBNTBlocks.exists_isBNTCanonicalForm` | `MPSTensor.exists_isBNTCanonicalForm_of_tp_primitive_irr_blocks` |
| `MPSTensor.PreparedBNTBlocks.exists_isBNTCanonicalForm_and_totalDim` | `MPSTensor.exists_isBNTCanonicalForm_of_tp_primitive_irr_blocks_and_totalDim` |

The three unbundled suppliers are blueprint-tagged
(`blueprint/src/chapter/ch10_bnt_sector_canonical_form.tex`) and are retained
unchanged, as is
`MPSTensor.PreparedBNTBlocks.exists_isBNTCanonicalForm_exact` in
`TNLean/MPS/FundamentalTheorem/SectorBNT/PreparedReconstruction.lean`, which
remains the one bundled method. The module docstring was reworded to describe
the suppliers this file actually provides and to point at
`PreparedReconstruction` for the bundled method.

Caveat: the candidate that proposed this removal asked for confirmation from
the author of the change that introduced these three members that no follow-up
consumer is imminent. That confirmation was not obtainable in this pass; the
removal rests on the grep-plus-build evidence alone, and the three adapters
are one-line restatements that are trivial to reintroduce if a consumer
appears.

## 5. Mathlib permutation-matrix shadows

`TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean`

| Removed | Replacement |
|---|---|
| `MPSTensor.permMatrix_apply'` | `PEquiv.toMatrix_apply` (Mathlib) |
| `MPSTensor.permMatrix_mul_eq_submatrix` | `PEquiv.toMatrix_toPEquiv_mul` (Mathlib) |
| `MPSTensor.mul_permMatrix_eq_submatrix` | `PEquiv.mul_toMatrix_toPEquiv` (Mathlib) |

All three were private and used only inside `permMatrix_conj_eq_submatrix`.
Since `Equiv.Perm.permMatrix R σ` is by definition `σ.toPEquiv.toMatrix`, the
two multiplication lemmas are exactly the Mathlib statements above; the
conjugation lemma now unfolds the abbreviation and rewrites with them
directly. The statement of `permMatrix_conj_eq_submatrix` is unchanged, so the
blueprint tag at
`blueprint/src/chapter/ch11_fundamental_theorem_coordinates_and_unitaries.tex`
still resolves.
