# Direct Gram rigidity for the two-site BNT sector gauges

Issue: #7775. Source baseline: `00ff0ec405`.

## Source argument

CPSV16 (`Papers/1606.00608/MPDO-22-12-17-2.tex`), Appendix C.4,
lines 2048–2057, matches the one-site and two-site normal sectors by invertible
conjugacies and invokes Proposition 4.13 to obtain unitary conjugacies.
The proof of that proposition, lines 1903–1921, separates the marked tensors,
uses normality to make the Gram matrix scalar, and normalizes the gauge by the
inverse square root of the positive scalar.

`TwoSiteExactSectorGauge.gramDressing_gauge_eq_one` already proves the marked
comparison independently, using one-site and two-site physical prefixes with
the same unblocked tail. The former downstream proof derived a reflected-target
hypothesis from that identity, constructed an identity-marked realization, and
repeated marked-trace separation to recover the identity. This was a redundant
dependency, not a logical circularity.

## Retained argument

The existing mixed-prefix identity now directly supplies the hypothesis of
`Kraus.IsNormal.gram_eq_pos_smul_one_of_gram_conj_eq` in the QICLean dependency.
Normality is transported along the existing sector bond-dimension equality.
The retained scalar-Gram normalization theorem then gives unitary conjugacy,
and pointwise choice assembles the existing `UnitarySectorConjugacy` structure.
Its existing support-completed physical maps prove the RFP conclusion.

The signatures of `gramDressing_gauge_eq_one`, `gauge_gram_eq_pos_smul_one`,
`exists_unitary_sector_conjugacy`, and
`UnitarySectorConjugacy.ofAlgebraTensorClause` are unchanged. The mixed-prefix
Gram proof and the scalar-to-unitary theorem and proof are unchanged. No new
hypothesis is introduced into either RFP implication or the downstream BNT
equivalences.

## Retired declarations

Within `MPOTensor.BNTAlgebraTensorClause.TwoSiteExactSectorGauge`:

- `HasIdentityPositiveTailReflectedTarget`.
- `IdentityMarkedRealization` and its structure projections.
- `IdentityMarkedRealization.ofPositiveTailReflectedTarget`.
- `gramDressing_gauge_eq_one_of_identityMarkedRealization`.
- `gramDressing_gauge_eq_one_of_positive_tail_reflected_target`.
- `gauge_gram_eq_pos_smul_one_of_identityMarkedRealization`.
- `gauge_gram_eq_pos_smul_one_of_positive_tail_reflected_target`.
- `exists_unitary_sector_conjugacy_of_positive_tail_reflected_target`.
- `UnitarySectorConjugacy.ofPositiveTailReflectedTarget`.
- `isRFPViaTS_of_positive_tail_reflected_target`.
- `has_identity_positive_tail_reflected_target`.

The Lean consumer audit found no independent callers outside this conditional
chain and its unconditional replacement. The now-empty conditional Gram and
conditional RFP modules are removed from the generated MPDO aggregator.
The scalar-Gram normalization remains in `BNTAlgebraTensorClauseConditionalUnitary`.

## Preserved mathematics

`BNTAlgebraTensorClauseIdentityPhysicalSpan` is retained, including its separately
cited oblique compression and physical-letter coefficient results.
`BNTAlgebraTensorClauseConditionalPhysicalMaps` is unchanged, including the
trace-restoring completion on discarded complements. The one-site and two-site
corners, mixed-prefix reflection, and nondegenerate obstruction examples are
not retirement targets.

The old conditional Gram Blueprint entry is superseded by the existing
mixed-prefix Gram entry. The scalar-to-unitary entry retains its label for
Chapter 20 dependencies, but states only the scalar-Gram normalization it
actually uses. The paper-gap note continues to record the mixed-prefix local
fix and now identifies the direct Gram-to-unitary proof explicitly.
