# Degenerate readings, wave 1: zero-scalar proportionality and the conditional supplier

This audit records two degenerate readings retired under the rule of
`CLAUDE.md` §Degenerate readings are conventions, not gaps (merged), together
with every public declaration removed and its replacement. Of the five
declarations below, only `NonzeroProportionalMPV₂.toProportionalMPV₂` is
removed under `docs/project_conventions.md` §Style's pass-through exception
(it merely forwards to the surviving predicate); `ProportionalMPV₂` is
removed under the degenerate-readings rule above, and
`PeripheralProportionalCaseRootFromRescaling`,
`peripheralProportionalCase_periodicFT_of_rootFromRescaling`, and
`exists_isBNTCanonicalForm_afterBlocking_pos` are ordinary zero-consumer
dead-code removals, verified to have no remaining consumers. No compatibility
alias is provided for any removed declaration.

## Readings retired

### Proportional MPV families with a vanishing scalar

CPSV16 (arXiv:1606.00608), Theorem `thm1`, lines 1167--1170, assumes that two
tensors "generate MPV that are proportional to each other". The formalization
carried two predicates for this hypothesis: `MPSTensor.ProportionalMPV₂`, in
which the length-$N$ scalar $c_N$ may vanish, and
`MPSTensor.NonzeroProportionalMPV₂`, in which it may not. The relation
$V = 0 \cdot V'$ is not a projective statement, and the source argument never
uses it; `docs/paper-gaps/cpsv16_nonzero_proportionality_reading.tex` records
the nonzero reading as the adopted convention. The vanishing-scalar predicate
had one consumer, the conditional periodic node below, which itself had none.
Both are deleted; `NonzeroProportionalMPV₂` is the only named proportionality
predicate. One inline eventual-proportionality hypothesis with no
nonvanishing condition on the scalar still occurs, outside any named
predicate, in `MPSTensor.mpvOverlap_norm_tendsto_one_of_eventually_proportionalMPV₂`
(`TNLean/MPS/FundamentalTheorem/Proportional.lean`); the scalar's eventual
nonvanishing is derived there from the self-overlap convergence hypotheses
rather than assumed.

### Handing the line-246 weight normalization back to the caller

CPSV16 line 246 fixes the canonical-form weights so that $|\mu_k| \le 1$ with
at least one $|\mu_k| = 1$, "something which we will assume from now on".
The conditional supplier `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos`
returned prepared blocks together with an implication whose premises were the
two normalization clauses, leaving the choice to the caller. The normalized
supplier `exists_isBNTCanonicalForm_afterBlocking_pos_normalized` realizes the
choice by dividing the weights by their largest modulus and records the cost
as the per-site scalar $m^N$. Its single hypothesis, that the positive-length
MPV family is not the zero family, is exactly the input the line-246
convention presupposes (a unit-modulus weight requires a nonempty weight
family). It is therefore the source's standing convention, not a sub-case,
and the `**Scope restriction (nonzero MPV family)**` stamp on the Lean
theorem, the matching blueprint paragraph, and the "separate zero-family
clause" elimination plan in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`
are removed. The hypothesis stays, unstamped.

## Removed declarations

| Declaration | Module | Replacement |
|---|---|---|
| `MPSTensor.ProportionalMPV₂` | `TNLean/MPS/Defs.lean` | `MPSTensor.NonzeroProportionalMPV₂` (same module). |
| `MPSTensor.NonzeroProportionalMPV₂.toProportionalMPV₂` | `TNLean/MPS/Defs.lean` | None needed; the target predicate no longer exists. |
| `MPSTensor.PeripheralProportionalCaseRootFromRescaling` | `TNLean/MPS/Periodic/FundamentalTheorem.lean` | None; the live proportional periodic route is `TNLean/MPS/Periodic/ProportionalOverlap.lean` with `MPSTensor.peripheralProportionalCase_periodicFT_of_sameMPV₂Pos`. |
| `MPSTensor.peripheralProportionalCase_periodicFT_of_rootFromRescaling` | `TNLean/MPS/Periodic/FundamentalTheorem.lean` | None; the live proportional periodic route is `TNLean/MPS/Periodic/ProportionalOverlap.lean`, which takes `NonzeroProportionalMPV₂` hypotheses directly rather than rescaling to `SameMPV₂Pos` first. |
| `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos` | `TNLean/MPS/FundamentalTheorem/SectorBNT/Supplier.lean` | `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos_normalized` (`SupplierNormalized.lean`); the prepared-block family alone is `MPSTensor.exists_prepared_BNT_blocks_afterBlocking_pos`. |

## Removed blueprint nodes

| Label | File | Replacement |
|---|---|---|
| `def:proportional_mpv` | `blueprint/src/chapter/ch02_mps.tex` | `def:nonzero_proportional_mpv`. |
| `thm:peripheral_periodic_ft_proportional_rescaling` | `blueprint/src/chapter/ch22_periodic_ft_overlap_sector_match_and_consequences.tex` | `thm:peripheral_periodic_ft_proportional_same` and the proportional-overlap route of the same chapter. |
| `thm:paperbnt_supplier_after_blocking` | `blueprint/src/appendix/ft_mps/ch10_bnt_block_separation_and_suppliers.tex` | `thm:paperbnt_supplier_after_blocking_normalized` (`ch10_bnt_sector_canonical_form.tex`). |
| `rem:arbitrary_input_reduction_gap` | `blueprint/src/chapter/ch10_bnt_sector_canonical_form.tex` | None; the remark described the conditional premises that the normalized supplier realizes. |

## Prose updated

- `TNLean/MPS/FundamentalTheorem/Proportional.lean`: module and theorem
  docstrings name the surviving predicates.
- `TNLean/MPS/FundamentalTheorem/SectorBNT/SupplierNormalized.lean`: scope
  stamp replaced by one sentence stating the convention.
- `docs/glossary.md`: supplier bridge and caveat repointed to the normalized
  supplier.
- `docs/paper-gaps/cpsv16_nonzero_proportionality_reading.tex`,
  `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`,
  `docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex`: sentences
  referring to the removed declarations rewritten.

Historical audit files under `docs/audits/` and `blueprint/comments/` that
mention the removed names are left as written.

## Statement integrity

No surviving theorem changed its statement or conclusion. The only Lean
changes are deletions and docstring edits.
