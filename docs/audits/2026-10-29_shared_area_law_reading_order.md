# Shared finite-site lemmas before the chain area law

The chain area-law chapter cited sheet swaps, the information reset, and product
ground states from later two-dimensional chapters. These statements concern
arbitrary finite tensor products. They now appear together in
`ch35_finite_site_reset.tex`, before the chain chapters and both two-dimensional
area-law developments. The two-dimensional sections retain the specialized
geometry and constants.

The move preserves all 22 shared statements and their proofs, every preexisting
label, every Lean anchor, and every readiness marker. The order and commutant
lemma for site expectation moves separately to immediately after the circuit
chapter's expectation properties, before the supported relative evolution that
uses it. No mathematical hypotheses or conclusions change.

The file called `ch24_peps_area_law_intro.tex` is the heading of the main
area-law chapter, whose section files follow it. It introduces that chapter,
not the preceding constraints, geometry, and amplification chapters. It stays
with those sections; moving it before the preparatory chapters would change
their chapter nesting.

A recursive expansion of literal inputs in `content.tex` on baseline
`3af48c1843059427e4ab3eb84caf9539ac4efa91` counted references and dependency
citations whose targets occur later. The same count falls from 2,924 to 2,883,
with unique forward targets falling from 1,377 to 1,362. This is a comparison
of this exact checkout, not a continuation of an earlier audit's different
baseline. All of the chain's references to the moved shared results now point
backward. The overall count still includes intentional forward references in
introductions and statements of main results.

Verification: statement/proof text was compared modulo whitespace; the global
multisets of labels and Lean anchors were compared before and after, allowing
only the new shared chapter label; Blueprint declaration synchronization finds
no missing anchors; repository ChkTeX checks and LaTeX formatting pass. No Lean
compilation or PDF/web build was run locally.

## Main integration on 2026-10-29

Merged `origin/main` at `55b8f9d56d909a1d32d58dad3a2b25ed967128c6`.
The shared finite-site chapter remains first in the area-law part, before
both chain and two-dimensional consumers; all new main chapter inputs are
retained. The expectation order/commutant result still follows expectation
properties and precedes the supported-approximant comparison. The current
role updater was applied after resolving the moved-statement conflicts.

All 22 moved statement/proof blocks match current main modulo role names,
reference words and whitespace. Global labels, Lean anchors, dependencies,
readiness and proof counts are conserved, allowing only the new shared
chapter label. Role checks and all eight role tests, recursive literal-input
reading-order checks, reader prose, ChkTeX, changed-file TeX formatting and
whitespace checks pass. The historical reference totals above retain their
explicit original baseline. No local Lean or PDF/web build was run.
