# PEPS RegionBlock zero-reference deletion

Eight staged lemmas under `TNLean/PEPS/RegionBlock/` had no consumer anywhere
in the production corpus at the audited head: no other declaration, no
Blueprint `\lean{...}` tag, no paper-gap citation. None carries `@[simp]`,
`@[grind]`, or `@[ext]`, and none is an instance. They were the intermediate
steps of routes whose capstone theorems landed without them, so they are
deleted rather than documented.

| Removed declaration | File |
|---|---|
| `TNLean.PEPS.regionInsertedCoeff_applyGauge_eq_innerOuterSum` | `TNLean/PEPS/RegionBlock/GaugeBridgeExpansion.lean` |
| `TNLean.PEPS.sameAwayFromRBBundle_iff_redHostAgrees` | `TNLean/PEPS/RegionBlock/CoarseThreeSite9.lean` |
| `TNLean.PEPS.CoherentCoarseBlockingFrame.legEquivRed_eq_legEquivComplement_on_rc` | `TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean` |
| `TNLean.PEPS.CoherentCoarseBlockingFrame.legEquivBlue_eq_legEquivComplement_on_bc` | `TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean` |
| `TNLean.PEPS.regionBoundaryGaugeInv_mul` | `TNLean/PEPS/RegionBlock/GaugeInjectivity2.lean` |
| `TNLean.PEPS.insertOuterBondProd_congr` | `TNLean/PEPS/RegionBlock/InsertResidual.lean` |
| `TNLean.PEPS.regionInsertionOp_add` | `TNLean/PEPS/RegionBlock/Realization.lean` |
| `TNLean.PEPS.regionInsertionOp_smul` | `TNLean/PEPS/RegionBlock/Realization.lean` |

## Supersession of an earlier replacement column

`docs/audits/2026-07-30_peps_zero_reference_pass_through_audit.md` names
`legEquivRed_eq_legEquivComplement_on_rc` and
`legEquivBlue_eq_legEquivComplement_on_bc` in its "Existing replacement" column,
as the surviving general forms of the two `_single` specializations retired
there. Both are removed here as zero-reference, so those two rows of the older
note are superseded rather than silently falsified: neither the specialization
nor the general form now exists, and the two leg-agreement facts are recovered
from the coherence fields `factor_red_rc` / `factor_compl_rc` and
`factor_blue_bc` / `factor_compl_bc` of `CoherentCoarseBlockingFrame` at the use
site, exactly as the deleted proofs did.

## Follow-on cascade

`regionInsertedCoeff_applyGauge_eq_doubleSum`
(`TNLean/PEPS/RegionBlock/GaugeBridgeExpansion.lean`) had exactly two
references: its own definition and the single use inside the lemma deleted
here. It became zero-reference with that change and was deferred for a separate
look; that look has been taken and it is removed. Its removal in turn leaves
`regionComplProd_gauge_eq` without a call site, referenced only from
module-header prose; that declaration is retained here and tracked separately.

Nothing else in these six files loses its last consumer. `insertOuterBondProd`
survives with sixteen uses in `InsertResidual.lean` and six in
`ScalarExtraction.lean`; `regionInsertionOp_mul` survives with a consumer in
`Recovery3.lean`; `regionInsertedCoeff_add` and `regionInsertedCoeff_smul` are
different declarations, are cited in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, and are untouched.

## Completing the leg-agreement family (2026-08-27)

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.CoherentCoarseBlockingFrame.legEquivRed_eq_legEquivBlue_on_rb` | the coherence fields `factor_red` and `factor_blue_rb`, read at the use site |
| `TNLean.PEPS.CoherentCoarseBlockingFrame.legEquivRed_eq_legEquivBlue_on_rb_single` | `legEquivRed_eq_bondModel_rb` together with `legEquivBlue_eq_bondModel_rb` (`TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean`) |

This completes the three-member leg-agreement family. The note above removed the
r-c and b-c general forms; the r-c and b-c single-configuration twins were removed
in `docs/audits/2026-07-30_peps_zero_reference_pass_through_audit.md`. The r-b pair
was the last surviving member, and the r-b fact remains recoverable from the two
live bond-model read-off lemmas named in the table.

The footnote of `docs/paper-gaps/peps_normal_ft_section3_route.tex` that cited the
`_single` form now closes on the three per-configuration read-off lemmas
`legEquivRed_apply_eq`, `legEquivBlue_apply_eq`, and
`legEquivComplement_apply_eq`, which already backed the sentence. Two module-header
parentheticals in `CoarseThreeSite2.lean` cited `legEquiv_agree_on_crossing`, a name
that never existed in the tree; both now point at the coherence fields instead.

## Local shadow of a Mathlib lemma (2026-08-27)

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.mul_three_ite` | `ite_zero_mul_ite_zero` (`Mathlib/Algebra/Ring/Defs.lean`), applied twice |

The local lemma stated that a product of three zero-defaulted scalar selectors is
the selector of their conjunction. Two applications of the Mathlib binary form give
the same rewrite, up to the associativity of the conjunction, which `and_assoc`
supplies on the residual propositional goal in
`TNLean/PEPS/RegionBlock/CoarseThreeSite4.lean`.
