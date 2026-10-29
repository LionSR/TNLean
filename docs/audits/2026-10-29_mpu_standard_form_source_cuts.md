# Actual standard-form source cuts for #7020

Source: `Papers/1703.09188/paper_v2.tex:1237–1252`, proof of `PropChiral`,
particularly the blocked standard-form comparison `eq:block-twosites`.

## Delivered algebra

For actual supplied two-site data `S : TwoSiteStandardFormData W u v`,
with `W` of physical dimension `d*d`, the new module constructs four explicit
matrices factoring the two cuts of `W` itself. Their pair-index intermediate
spaces have cardinalities `d*r` and `ℓ*d`; no zero-index assumption is needed. The source-cut identities use only the actual
open contraction; there is no assumed gauge, local certificate, or existence
premise asserting the missing comparison.

The two right factors contract to exactly `staircaseMiddle v * (u ⊗ u)`.
The two left factors contract to exactly `staircaseMiddle v`. Both act on
four original `d`-dimensional spins. Taking source cuts after first blocking
`W` again would act on eight original spins and is not substituted for the
source's four-spin local equation.

The actual canonical-source standard form also has both required coarse
left-factor normalizations. The first is `I_d ⊗ X₁`, after regrouping its
physical coordinates, and the second is `X₂ ⊗ I_d`. Their weighted and
ordinary isometries follow by Kronecker multiplication from the original
recorded source-factor fields. The two public canonical corollaries assume
no new normalization witnesses.

The actual rank identifications now follow from existing blocking-rank
saturation and persistence of simplicity. The block-one physical equivalence
is explicit, and the two-site rank calculation passes through the exact
`blockTwo`/direct-block-two coordinate equivalence. No endpoint rank product
is assumed: both are derived from canonical simple-block equivalence.

The new `twoSiteSourceFactors` record retains the original canonical boundary.
Its right factors have full row rank because each actual cut factors through
its pair space and that space has exactly the actual cut rank. Mathlib's
finite-dimensional range and matrix right-inverse theorems then construct the
two right inverses. Thus the whole normalized record is now derived, with no
normalization, inverse, rank or gauge-existence witness added as an input.

The necessary zero-index rank conclusion is also derived, with its input
stated at the even original lengths. Adjoint invariance of `mpo U (2*N)`
compares the direct two-site block of U with its physical adjoint. Existing
same-family canonical FT identifies the ranks; adjunction exchanges them.
The proved growth formulas give `d*r = ℓ*d`; canceling the positive d gives
`r=ℓ`, and simplicity's `r*ℓ=d*d` then gives `r=ℓ=d`. The canonical datum
for the direct block is constructed by the existing blocking theorem and
its adjoint by the existing physical-adjoint theorem; neither is an input
witness. Only one two-site blocking is used, and no odd-length symmetry is
inferred.

## Remaining source steps

The physical-adjoint coarse factors must be constructed in the same actual
cut coordinates and their gates related to these literal four-spin matrices.
Then the existing arbitrary supplied-factor Fundamental Theorem can produce
the local gauges. Its operator-family hypothesis must be obtained while
retaining the paper's even-chain convention. No extra eight-spin blocking
may replace the required four-spin equation.

No literal forward local time-reversal certificate, converse or transposition
criterion is claimed here. The exact and admissible
Blueprint propositions remain `notready`; #7020 remains open. The full-support
restriction is already documented in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## Validation

No local Lean build, elaboration, compilation or cache mutation was run,
per user instruction. These proofs remain uncompiled. Pinned source APIs,
generated imports, changed-declaration Blueprint coverage, tactic-pattern
scan, TeX formatting, whitespace/100-column and placeholder scans are
source-only checks. The promoted `Finset.sum_congr₂` helper is reused.
