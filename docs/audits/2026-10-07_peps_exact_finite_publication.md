# Exact finite-size PEPS package

This snapshot consolidates the checked exact tree/square representation, its
native approximation-model corollaries, and removal of finitely many exceptional
sizes for issue #8773. The mathematical source is the September 24, 2026
polynomial-PEPS manuscript at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-assembly.tex`, lines 203–214.

The result preserves the native quantifiers: for fixed `q, J, Δ`, choose
`C, c > 0` and a threshold `L₀` before `L, H, E₀, Ω`. A uniform approximation
for every `L ≥ max 2 L₀` extends to every `L ≥ 2`, with the same exponent and
one enlarged prefactor. The large-size assertion is an explicit unproved input.
This package does not prove the manuscript's main approximation theorem.

## Dependency and authored scope

The publication base is the existing model PR #8788, branch
`feat/area-law-peps-models`, commit
`158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2`. Its 161-line
`TNLean/PEPS/Approximation/Basic.lean` is inherited unchanged, with SHA-256
`16c669175f00af22a6e8e274d8210423356ed6b0e88e99f1b1b38d6775a8854c`.
No model source is copied into this PR's incremental diff or attributed to it.
The model PR's full dependency contribution also remains owned by #8788.

The incremental production contribution is 798 lines in five modules:

- Tree representation, square connectivity and square bounds: 655 lines and
  40 ordinary named declarations, plus two generated structure projections.
- Native small-size approximation: 62 lines and two theorems.
- Finite-exception assembly: 81 lines and three theorems.

All 45 ordinary declarations are independently authored from manuscript
mathematics. No upstream OpenAI Lean proof text is copied or adapted. Reuse of
the existing TNLean/Mathlib/QICLean APIs is by import. The checked production
proof and statement bytes are unchanged; provenance comments already present
in the 655-line tree package are retained.

## Review boundaries

The retained component reports describe the local stage when they were written.
Their earlier publication holds and unregistered-chapter statements are
historical; this consolidation supplies the registrations and draft snapshot.
It does not retroactively claim that earlier checks ran on the combined tree.
Full exact-head CI, full-book compiled declaration checks and current-main
integration must be assessed from the draft PR's actual run. At preparation,
#8788 was still unmerged and conflicted with main
`141e7d8403558a34b2cc663388f1994e3264826b`; this draft inherits that dependency
integration requirement.

The 40-declaration source ledger remains unchanged. Its pinned local validator
was originally run in the isolated tree package; a whole-repository provenance
scan on this stacked tree also needs #8788's ledger. The five downstream
theorems have exact source/hash, consumer and axiom evidence in the component
audits, but are not claimed as new entries in that 40-declaration ledger.
Full repository source-policy integration remains review work.

Assistance: OpenAI Codex (GPT-6) produced the formalization, documentation,
validation preparation and consolidation under the LionSR account. Human
mathematical review is pending.
