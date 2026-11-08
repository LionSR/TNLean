# Supplied standard-form transposition criterion — 2026-10-29

Source: `Papers/1703.09188/paper_v2.tex`, Proposition
`prop:local-char-transposition`, equation `UUtransposetrick` and the
phase-removal paragraph, lines 1258–1288. The actual four-spin gate is
specified by `eq:block-twosites`, lines 1237–1252.

## Delivered

For ANY supplied two-site standard form S in an explicitly reduced CFII
ambient tensor W, transpose symmetry at every even W length N>1 is
proved equivalent to square intermediate dimensions and the literal
four-original-spin equation
`V23*(u⊗u)=c*(x⊗xᵀ)*V23ᵀ`, with x unitary and |c|=1. The local phase is
also given in the literal exponential form exp(i*phi), chosen pointwise.
No normalized supplied half factors, comparison-gauge witness, transformed
factor supplier or additional local equation is supplied as a premise.

The actual source-rank identities r[W]=d*r and ell[W]=ell*d, together
with the even-family transpose comparison, derive r=ell=d. The actual
four-spin comparison with internally selected normalized source factors
gives `A_T=(X⊗Y)A` and `B_T=B(Y†⊗X†)`. Their actual normalized transpose
certificate transports to the supplied one by the unitary
`x=X†*z*conj(Y)`. In reverse, the supplied certificate gives the actual
normalized one with `z=X*x*Yᵀ`; existing even-ring contraction closes it.
Entrywise conjugation of a unitary uses the existing public matrix API.

## Reuse

The existing private square-coordinate source comparison is promoted at
its actual owner as
`TwoSiteStandardFormData.exists_fourSpin_selected_source_gate_gauges_of_square_ranks`.
Both adjoint and transpose directions reuse that single proof. No alias or
parallel choice predicate remains. Physical-pair transpose-certificate
transport is at the existing gate-coordinate owner, and both the old
chosen-source converse and the new supplied converse reuse it. The literal
phase reconstruction uses Mathlib `Circle.exp_arg` directly, including the
two existing chosen-source exponential callers; no local polar wrapper is
introduced.

## Remaining scope

Ambient CFII is an explicit hypothesis. Minimality of the displayed cut
factors does not prove that the ambient virtual space is minimal, and
padded supplied presentations are not identified with canonical ones by
these results. This is therefore not the unrestricted source proposition;
see `docs/paper-gaps/mpu_canonical_form_full_support.tex`. The exact even-W
length convention is retained; no all-length statement or extra gate-level
blocking is inserted. See `docs/paper-gaps/mpu_standard_form_parity_gap.tex`.
The existing actual supplied-factor phase-removal path consumes the derived
pointwise exponential certificate without any continuous factor or argument
selection. No new path supplier is assumed.

## Dependencies and verification

Isolated child of #10360 at3ee5c09ac plus #10329 atffb7df3b4. The only
merge conflict was the proof-pattern ledger; both sets of independent
entries were retained. The inherited normalized transpose necessity repair
awaits hosted acceptance. New proofs are source-written and uncompiled.
New source and auxiliary Blueprint entries remain notready; #7020 stays open.

Pinned Mathlib/QIC and literal-paper source inspection, source arithmetic
and transpose/conjugation orientations, import generation/check, new
public-declaration Blueprint coverage, tactic scan, reader prose, changed
TeX formatting, width/whitespace and proof-integrity checks are used.
No local Lean build, elaboration, compilation or cache mutation was run.
