# Actual standard-form source cuts for #7020

Source: `Papers/1703.09188/paper_v2.tex:1237–1252`, proof of `PropChiral`,
particularly the blocked standard-form comparison `eq:block-twosites`.

## Delivered algebra

For actual supplied square two-site data `S : TwoSiteStandardFormData W u v`,
with `W` of physical dimension `d*d`, the new module constructs four explicit
matrices factoring the two cuts of `W` itself. Their pair-index intermediate
spaces have cardinality `d*d`. The source-cut identities use only the actual
open contraction; there is no assumed gauge, local certificate, or existence
premise asserting the missing comparison.

The two right factors contract to exactly `staircaseMiddle v * (u ⊗ u)`.
The two left factors contract to exactly `staircaseMiddle v`. Both act on
four original `d`-dimensional spins. Taking source cuts after first blocking
`W` again would act on eight original spins and is not substituted for the
source's four-spin local equation.

## Remaining source steps

These factors are not yet a `SourceFactors W` record. Its intermediate
indices use the actual ranks of the cuts, and its fields require a weighted
first isometry, ordinary second isometry and right inverses. The current
supplied standard-form datum carries the gate unitarities and open
contraction, but not those canonical normalizations of its half factors.
For standard forms constructed from canonical source factors the original
normalizations are available; they must be transported to the displayed
coarse factors, the pair dimension must be identified with the actual ranks,
and the physical-adjoint counterpart must be compared at those same cuts.
Only then may the existing arbitrary supplied-factor Fundamental Theorem
produce the actual local gauges. The paper's even-chain convention must
remain explicit in converting global symmetry to the comparison family.

No literal forward local time-reversal certificate, converse, transposition
criterion or zero-index theorem is claimed here. The exact and admissible
Blueprint propositions remain `notready`; #7020 remains open. The full-support
restriction is already documented in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## Validation

No local Lean build, elaboration, compilation or cache mutation was run,
per user instruction. These proofs remain uncompiled. Pinned source APIs,
generated imports, changed-declaration Blueprint coverage, tactic-pattern
scan, TeX formatting, whitespace/100-column and placeholder scans are
source-only checks. The promoted `Finset.sum_congr₂` helper is reused.
