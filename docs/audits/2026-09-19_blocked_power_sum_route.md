# Removal of the blocked power-sum route

This audit records the deletion of the blocked stage of the power-sum
coefficient theorem from
`TNLean/MPS/FundamentalTheorem/SectorBNT/PowerSumCoefficients.lean`, together
with the blueprint node that carried it. It is the audit note required by
`docs/project_conventions.md` §Style. No compatibility alias is provided for any
removed declaration.

## What was superseded

The blocked theorem `MPSTensor.exists_blocking_powerSum_coeff` took a tensor
`B` whose periodic vectors lie, at every positive length, in the span of the
periodic vectors of a finite family of pairwise inequivalent normal tensors, and
produced one blocking length `p`, a threshold, and finite multisets of nonzero
complex weights whose power sums are the expansion coefficients at the blocked
lengths `p * m` past the threshold.

`MPSTensor.exists_unblocked_powerSum_coeff`, in
`TNLean/MPS/FundamentalTheorem/SectorBNT/UnblockedPowerSumCoefficients.lean`,
carries exactly the same hypotheses and a strictly stronger conclusion: the
canonical power-sum expansion holds at *every* positive length with no blocking,
the coefficients of any expansion are forced past a positive threshold, and the
multiplicities satisfy the dimension bound `∑ γ, n γ * DM γ ≤ DB`. The blocked
statement is its `p := 1` instance. `MPSTensor.exists_unblocked_powerSum_coeff_unique`
adds uniqueness of the weight multisets. Both are proved through the
trace-reduction route of the source theorem and call none of the blocked-stage
lemmas.

## Removed declarations and their replacements

* `MPSTensor.exists_blocking_powerSum_coeff`, replaced by
  `MPSTensor.exists_unblocked_powerSum_coeff`.
* `MPSTensor.exists_blocking_powerSum_weights`, with no replacement; see below.
* `MPSTensor.exists_matching_data_of_isBNTCanonicalForm`, subsumed by
  `MPSTensor.exists_matching_of_span`.
* `MPSTensor.exists_blocked_representatives_of_isNormal_distinct`, subsumed by
  the normalization step of `MPSTensor.exists_irreducible_expansion`.
* `MPSTensor.exists_eventually_linearIndependent_blockTensor_of_normalTensor_distinct`,
  replaced by the unblocked
  `MPSTensor.exists_eventually_linearIndependent_of_normalTensor_distinct`,
  which is retained.
* `MPSTensor.not_gaugePhaseEquiv_of_exists_eventually_linearIndependent`, with
  no replacement; it was used only inside the removed route.
* `MPSTensor.mpv_span_congr_length`, with no replacement; it was needed only to
  transport a spanning identity from length `1 * m` to length `m`.
* `MPSTensor.exists_fin_weights_of_sum_pow`, replaced by
  `MPSTensor.exists_fin_weights_of_sum_pow_card`, which fixes the index
  cardinality instead of quantifying over it.

`MPSTensor.exists_blocking_powerSum_weights` is the one removal that is not a
special case of a surviving statement. It asserts rigidity of the expansion
coefficients along blocked lengths *without* the spanning hypothesis, whereas the
rigidity clause of the unblocked theorem is derived from the canonical expansion
and therefore needs spanning. It is deleted because nothing uses the
spanning-free form: no Lean consumer outside the removed route, no blueprint
node, and no source statement. The source theorem for this material, in
`Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/t1_unblocked.tex`,
assumes spanning, and so did the blueprint node that has been removed. The
strengthening is therefore dropped as unused rather than migrated.

## What is retained

`PowerSumCoefficients.lean` keeps the file name and the four helper lemmas that
the unblocked development consumes:

* `MPSTensor.exists_leftCanonical_normalTensor_scale_of_isNormal`, cited by path
  from `TNLean/MPS/Periodic/ScaledNormalization.lean`;
* `MPSTensor.gaugePhaseEquiv_of_smul_smul_cast`;
* `MPSTensor.exists_eventually_linearIndependent_of_normalTensor_distinct`;
* `MPSTensor.sum_smul_mpvState_eq_zero`.

Its module docstring now describes these four and points at the unblocked file
for the theorem itself. Five imports and the `Filter`/`Topology` opens became
unused with the removed route and were dropped; the unblocked file and the rest
of the sector-basis layer build without them.

## Blueprint

The node `thm:asym_power_sum_coefficients`, with its section
`sec:asym_power_sums` in
`blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex`, was removed
rather than retagged. The immediately following section already contains
`thm:asym_unblocked_coefficients`, which states the source theorem with the same
hypotheses, the stronger unblocked conclusion, the dimension bound and the
uniqueness clause, and which already carried `\lean{}` tags for both unblocked
theorems and a full proof sketch of the trace-reduction route. Retagging the
blocked node would have duplicated it.

The motivating prose of the removed section — that renormalization fixed points
may have length-dependent structure coefficients, that the constraint is a
power-sum constraint, and that positivity of the weights is not asserted — was
folded into the introduction of the surviving section. The two prose references
to the removed node, in
`blueprint/src/chapter/ch25_asymmetric_examples_oscillating.tex` and
`blueprint/src/chapter/ch25_asymmetric_examples_rfp.tex`, now point at
`thm:asym_unblocked_coefficients`; both sentences describe power sums at every
length, so they read more accurately against the unblocked statement than
against the blocked one.

## What was checked

* Every removed declaration was searched for across `TNLean`, `TNLeanTest`,
  `blueprint/src`, `docs` and `Notes`. The only production references were
  inside the removed route itself and in the removed blueprint node. The
  remaining hits are citations that name the removed declarations on purpose:
  this note, and the ledger entry for the removal, which
  `docs/project_conventions.md` §Style requires to name each removed
  declaration. Neither is a consumer, and both survive the removal by design.
* The unblocked file references none of the removed declarations; its uses of
  `PowerSumCoefficients.lean` are exactly the four retained helpers.
* The edited module, the unblocked module, the sector-basis aggregator, the
  operator-closure consumer and both aggregators above them build clean with the
  package linters.
* Blueprint declaration coverage remains complete.

## What is deferred

Nothing. The removed route has no remaining consumer and no source statement of
its own.

One consequence was handled here rather than deferred: the opening paragraph of
`UnblockedPowerSumCoefficients.lean` described `PowerSumCoefficients.lean` as
proving the blocked stage of the question, which is the theorem this removal
deletes. That paragraph was rewritten to state the unblocked result directly and
to describe the retained file by what it now supplies.
