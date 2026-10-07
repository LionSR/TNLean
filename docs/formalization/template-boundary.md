# Ambient template boundary slice

This separate draft is stacked on the unchanged row-proof PR #8798 at
`06cfc12e5ce3bc1c7e16553af44ded6da1e71223`. It owns only the newly claimed
ambient-boundary part of #8754. The source is Lemma 9.4 of the September 24,
2026 manuscript at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/08-scanner.tex`.
All new production proofs are original; no upstream Lean text is reused.

The theorem `template_boundary_card_le` states the actual unordered ambient
nearest-neighbor boundary bound `4*n` for every `0 ≤ j ≤ s₀` when `Ctpl ≥ 24`.
`template_shell_boundary_card_le` gives `8*n` for `T_j \ T`.
Both production modules, the full library build, strict actual-model
regressions, all 18 axiom audits, style lint, compiled declarations, the
full blueprint job, and compilation-time checks passed at
`e2c3c2111922ebebf7c665db52d8e382e4318ba1` in
[PR CI run 37629687127](https://github.com/LionSR/TNLean/actions/runs/37629687127).
All exports use only the standard axioms; `latticeNeighbors` uses `propext`
and `Quot.sound`, and the other 17 use those plus `Classical.choice`.
The observed outputs are now guarded in the regression file.
Evidence is preserved in [the build log](../provenance/evidence/8754-boundary-build.log),
[the axiom output](../provenance/evidence/8754-boundary-axioms.log), and
[the blueprint log](../provenance/evidence/8754-boundary-blueprint.log).
All 18 provenance entries record the verified revision and evidence hashes.

`ambientBoundary S` uses the existing `edgeBoundary` and `domainGraph` on
`ambientDilation S 1`, then maps subtype endpoints back with `Sym2.map`.
The exact crossing characterization proves that every ambient edge is present.
Injectivity preserves the cardinality of unordered edges, and the crossing
orientation is unique. This avoids counting a directed incidence twice.

A finite set meeting every crossing edge contributes at most four edges per
point. At positive radius, the inside endpoint lies in `T_j \ T_(j−1)`:
otherwise its outside neighbor would lie in `T_j`. At radius zero use outside
endpoints in `T₁ \ T`; the actual Template has `s₀ ≥ 1`. No layer estimate
at `s₀+1` is required. The shell estimate follows from the general inclusion
`∂(S \ U) ⊆ ∂S ∪ ∂U`.

Regressions cover four unordered edges of a singleton, reversed orientation,
negative coordinates, exclusion of diagonal and internal edges, and a complete
actual thin-real-polygon Template at radii zero and `s₀`. Its private fixture
is preserved from the original #8798 regression without changing that PR.
All 18 exports have exact axiom guards. Blueprint completion marks and
provenance verification reflect the passing checks.

Local prebuilt Mathlib retrieval again returned HTTP 403. No local Mathlib
proof-source rebuild was started; normal PR CI is the validation fallback.
Physical `A ∩ T_j` clearance, repaired-family geometry (#8758), and entropy
remain separate. This does not close the full #8754 or the physical area law.
OpenAI Codex (GPT-6) assisted the original proofs and documentation.
