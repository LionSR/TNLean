# Actual four-half-block output geometry — 2026-10-29

Source: `Papers/1703.09188/paper_v2.tex`, StandardForm/SF lines 603–622,
finite conjugation eq:appendix-1 lines 2300–2306, and the four-site
output in the Appendix index comparison lines 2313–2334.

## Delivered

The existing original-site output window is on 6k sites and its actual
coordinate map pairs `(e1,c1)`, `(c2,c3)`, `(c4,e2)`. The new coordinate
proof decodes these as six consecutive k-site words in precisely that
order. Its middle interval [k,5k) reads the actual four-half-block output
configuration; equality outside is exactly equality of the two exterior
half-block coordinates.

`TwoSiteMiddleOutput.lean` identifies the existing output matrix with the
existing `chainWindowOperator (3*(2*k)) k` of the actual two-link output,
reindexed only by the displayed four-half-block decoding equivalence.
Its [k,5k) supported-operator membership follows. No support conclusion,
gate factorization, normalization, MPU symmetry or unitarity is supplied
as an extra hypothesis: these are identities of the actual gate operation
for arbitrary matrices u,v,A and positive k. The result is the precise
four-output-block geometry needed by the actual supplied-S index caller;
that global blocked-pair image is assembled separately.

## Reuse and scope

The two-site physical decoding lemma is at its existing
`TwoSiteStandardForm.lean` owner and uses the actual inverse physical
identification and existing iterated-block word theorem. The new output
coordinate equivalence is used directly by the original output definition;
its private original three-block decoder is reused. One private half-word
coordinate lemma serves both the middle and exterior calculations.

No new support predicate, source supplier or tensor-factor certificate is
introduced. This does not prove a new bare-MPU or ambient-canonicality
criterion. It is an exact finite output identity for the already existing
supplied-gate operation.

## Verification

Independent source/math/API review by the finite-factor owner found no
concrete mismatch in the inverse physical cast, half-block ordering,
middle/exterior index cases, or equality-indicator contraction. Pinned
Mathlib/QIC source inspections, import generation, new declaration Blueprint
coverage, reader prose, tactic-pattern scan, formatted changed TeX, source
width/whitespace and proof-integrity checks are used. New entries remain
notready pending hosted acceptance. No local Lean build, elaboration,
compilation or cache mutation was run.

The index owner corrected the six inherited role-policy mismatches in
`ch28_qca_index.tex` and `ch28_qca_support_factors.tex` while integrating
this geometry. The combined branch passes the global role-policy check;
all new statements remain supporting lemmas and notready.
