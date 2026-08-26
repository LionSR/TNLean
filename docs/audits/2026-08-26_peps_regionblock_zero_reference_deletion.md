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
here. It becomes zero-reference with this change and is left for a follow-up
rather than removed in the same pass, since its docstring presents it as a
public expansion of the gauged region-inserted coefficient and deserves a
separate look.

Nothing else in these six files loses its last consumer. `insertOuterBondProd`
survives with sixteen uses in `InsertResidual.lean` and six in
`ScalarExtraction.lean`; `regionInsertionOp_mul` survives with a consumer in
`Recovery3.lean`; `regionInsertedCoeff_add` and `regionInsertedCoeff_smul` are
different declarations, are cited in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, and are untouched.
