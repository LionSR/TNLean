# Published graph-foundations validation

All 15 targeted checks pass at published source
[`c369460bb80b17abb974108f843befeed40f48f5`](https://github.com/LionSR/TNLean/commit/c369460bb80b17abb974108f843befeed40f48f5):

- One native `TNLean.PEPS.AreaLaw` build
- Eight production checks with explicit package options, standard linters and warnings as errors
- Five consumer checks: 46 examples and 49 permanent axiom guards
- One raw audit covering all 50 public declarations

The package has 45 public theorems, five public definitions and five private
helpers. All public axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`, or no axioms. The diamond definition is covered by the raw audit;
the other 49 declarations also have permanent guards. Full CI is pending.

The [source and declaration inventory](2026-10-07_area_law_graph_foundations_native_validation.json),
[execution records](../provenance/evidence/8745/validation.json) and
[50-row provenance ledger](../provenance/openai-math.d/8745.json) identify this
same published revision. Earlier local revisions do not serve as current
verification evidence.

## Source identity and scope

The published source tree is `07f82c04c9c926b81ce1f7e1eaefa63a4135b0eb`, identical
to the locally prepared source tree. The
[19-file manifest](../provenance/evidence/8745/source-manifest.json) records exact
Git blobs and SHA-256 hashes: eight production modules, five consumers, two
aggregators, two chapter files, the chapter router and bibliography. This
follow-up evidence commit changes none of those files.

Pins remain Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, and QICLean
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

The checked mathematics establishes graph walks through overlapping supports,
the exact lattice-diamond count, original-support weight and norm budgets,
target-chain exclusion beyond `(n+1)R`, and the actual exponential generating
function with weights `(2|t|)^n/n!`. For exact finite distance `D` and `mu >= 0`,
it proves summability and the bound
`exp(mu R - mu D) exp(2|t| v b exp(mu R))`. At infinite graph distance the series
is exactly zero, including for signed interaction weights.

This does not prove or assume the physical commutator recursion. Its
identification with physical dynamics, remainder control, localization and full
Lemma 4.1 remain open. No area-law or PEPS-approximation headline theorem is
claimed. Separate QICLean interaction-picture work is outside this TNLean ledger.

## Provenance and retained history

Every ledger row is `original`, `ported`, and `declared`, with `upstream: null`
and `no_upstream_proof_text_reused: true`. Here `ported` means an implemented,
verified declaration under the schema; it does not assert copied code or a
completed paper theorem. The source-authored team used OpenAI Codex, GPT-6.
No OpenAI Lean source or proof text was copied or adapted. Human contributor
review remains required.

The [focused validator result](../provenance/evidence/8745/provenance-validation.json)
uses the hardened policy at `a05ef8f8db19f28e987bf3ce599c5f284f96921f` without
installing or modifying shared policy. It checks all 50 current-source rows,
source bytes, notices, exact named axiom reports and evidence hashes. Four
private diamond helpers and one private exponential-factor helper remain
private and are separately inventoried. They compile with their modules; public
axiom reports inspect transitive dependencies. No fictitious public helper names
are introduced.

The [compact chronology](../provenance/evidence/8745/history.json) preserves the
meaningful failed proof, consumer and style attempts, including the earlier
27-declaration and 46-declaration stages. Its
[sanitized diagnostic log](../provenance/evidence/8745/historical-failures.log)
does not replace or erase original raw artifacts, which remain preserved locally.
Historical failures are not presented as passing runs.

Current logs record each original raw SHA-256, sanitized output SHA-256 and
committed log SHA-256. Commands use working repository-relative paths. The
[committed axiom query](../provenance/evidence/8745/axioms.lean) is byte-identical
to the executed query; its absolute execution location is replaced by this
portable path. No executor directory, credentials or unrelated notes are
included. Successful compiler output is preserved apart from trailing whitespace
normalization and the addition of a public result header.

## Focused blueprint checks and reproduction

[Focused render evidence](../provenance/evidence/8745/render-validation.json)
records eight PDF pages, 22 mathematical entries, 17 proof sketches, 39 checked
markers and 50 declaration links in each PDF/HTML output. Local references,
unique ownership and source equality pass. The published-source rerender's
page images are byte-identical to the eight previously visually inspected
pages. No clipping, missing glyphs or unresolved final references were found.
Inherited font-map and vector-imager warnings are retained in the render summary.

The portable scripts accept explicit paths and do not run Lean:

```sh
python3 docs/provenance/evidence/8745/check_provenance.py --root .
python3 docs/provenance/evidence/8745/prepare_render.py --root . --out build/8745
python3 docs/provenance/evidence/8745/verify_render.py --root . --out build/8745
```

The provenance check requires a Git checkout containing the pinned policy
commit and `jsonschema` 4.26.0. The render preparation requires `leanblueprint`
0.0.20, `plasTeX` 3.1 and `texra-blueprint` 0.3.8. Between preparation and
verification, compile the prepared `print.tex` with XeLaTeX/BibTeX, generate
`web.bbl`, run plasTeX, and extract PDF text/page images as documented in the
[render commands](../provenance/evidence/8745/render-commands.txt).

These are targeted native/strict and focused PDF/static HTML checks. Full
repository CI, full-book generation, live-browser/MathJax runtime and mobile
checks are not claimed. Publishing this evidence does not authorize or imply a merge.
