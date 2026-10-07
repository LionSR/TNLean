# Uniform PEPS approximation after finitely many exceptional sizes

## Scope and mathematical conclusion

The local continuation adds
`TNLean/PEPS/Approximation/ExactFiniteException.lean` on top of the checked
exact small-size construction. It proves these statements against the unchanged
native `HasPEPSApproximation` and `PolynomialPEPSApproximation` definitions:

1. `HasPEPSApproximation.mono_prefactor`: increasing `C` keeps the same tensor,
   phase, exponent, and normalized error bound. This uses only the nonnegativity
   of the real power of a natural number; neither a positive exponent nor a
   positive side length is required.
2. `exists_uniform_approximation_of_sufficiently_large`: for fixed positive `q`,
   arbitrary real `J, Δ, C`, nonnegative real `c`, and natural threshold `L₀`,
   an approximation for every `L ≥ 2` with `L₀ ≤ L` gives a single positive
   `C' ≥ C` valid for every `L ≥ 2`. The exponent remains exactly `c`.
3. `polynomialPEPSApproximation_iff_sufficiently_large`: the native target is
   equivalent to its sufficiently-large-size assertion with quantifier order
   `∀ q ≥ 2, ∀ J, Δ > 0, ∃ C, c > 0, ∃ L₀, ∀ L ≥ 2, L₀ ≤ L →
   ∀ H, ∀ E₀, ∀ Ω, IsGappedGroundState → HasPEPSApproximation`.

The constants and threshold are chosen before the side length, Hamiltonian,
energy, and ground vector. No Hamiltonian-dependent or vector-dependent
constant is introduced. Both directions preserve the Hamiltonian convention,
unit norm, full-system gap condition, original graph, positive bond dimensions,
nonzero contraction, real phase, and normalized global error `L⁻¹`.

The sufficiently-large-size existence statement is an explicit unresolved
dependency. The equivalence does not supply that assertion, nor does it prove
the manuscript's main theorem. There is no new target predicate, assumed
conclusion theorem, axiom, placeholder proof, or change to elaboration budgets.

## Direct mathematical proof

For fixed `q, L₀, C, c`, the checked finite-range theorem chooses
`C' = max C (q ^ (L₀ * L₀))`. Since `q > 0`, this is positive and at least `C`.
That choice precedes every `L, H, E₀, Ω`.

- If `L < L₀`, use the exact spanning-tree representation of the unit vector.
  Its normalized error is zero, and its original-edge bond dimensions satisfy
  the bound with this same `C'`.
- Otherwise `L₀ ≤ L`. Use the assumed approximation with prefactor `C`, then
  apply prefactor monotonicity. The tensor and phase do not change.

For the equivalence, the all-size assertion supplies the large-size assertion
with `L₀ = 0`. In the reverse direction, fix only `q, J, Δ`, obtain the uniform
`C, c, L₀`, and apply the preceding argument. The resulting positive `C'` and
the original positive `c` witness the all-size assertion.

## Immutable source and local dependency

The mathematical source is
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/07-assembly.tex`,
lines 203–214. Those exact lines were retrieved read-only on 2026-10-07;
the source file blob is `94dc6bfdb49e83dd23316c0fdf3ffd1798bba5ef`.
They describe the exact spanning-tree construction with common configuration
index, one-dimensional non-tree bonds, Hamiltonian-independent finite-size
bound, and one enlarged prefactor for `2 ≤ L < L₀`.

Source URL:
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/07-assembly.tex#L203-L214>.

The local base is `e9e35bf68d6d11763940b2100a8021a4ffd1ed5e`. It contains the
unchanged `Basic.lean` dependency from TNLean #8788 head
`158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2`, with blob
`df2002c0ec0defb72188220cc03c4fa3ad1a7797`. The dependency was not modified.
See `docs/provenance/evidence/8773-8788-local-dependency.md` for its ownership
and publication boundary. No original OpenAI Lean proof text was copied or
adapted; only the mathematical source was used.

## Source revision and consumers

The initial source revision is
`38ca555c8152093bfa06f066a84e5e98d4a02f3e`.

| File | SHA-256 |
| --- | --- |
| `TNLean/PEPS/Approximation/Basic.lean` (unchanged dependency) | `16c669175f00af22a6e8e274d8210423356ed6b0e88e99f1b1b38d6775a8854c` |
| `TNLean/PEPS/Approximation/ExactFiniteException.lean` | `374479c54f16f5fd71b2309a16c0f612fc994131b2822cd04fa06fbfdfef57a8` |
| `TNLeanTest/PEPS/Approximation/ExactFiniteException.lean` | `68dd1f17cc636dede5ed6ba5f30485021d9da2f142a43a398f644ca35d9951fc` |
| `docs/provenance/evidence/8773/ExactFiniteExceptionAxioms.lean` | `937ae5799e16cd66e0ff648c7288714ad85dd6ecdab4e1f7d327a7b686c3f565` |

The regression source has consumers for general prefactor enlargement,
uniform extension while retaining the fixed exponent, and each direction of
the equivalence with the full quantifier order written out. It includes
guarded axiom queries for all three declarations. The separate evidence file
prints their raw axiom closures.

## Checked evidence

The parent compiler checked source revision
`38ca555c8152093bfa06f066a84e5e98d4a02f3e`. The native
`TNLean.PEPS.Approximation.ExactFiniteException` target succeeded with 2819
jobs. All three strict checks used the package's strict implicit-variable
settings, `maxSynthPendingDepth=3`, standard Mathlib linters, and
`warningAsError=true`. They returned exit code zero:

| Check | Seconds | Result |
| --- | ---: | --- |
| Production source | 2.824 | PASS |
| Four consumers and three guarded axiom queries | 2.649 | PASS |
| Three raw axiom queries | 2.600 | PASS |

Every theorem's axiom closure is exactly `propext`, `Classical.choice`, and
`Quot.sound`. The source hashes in the parent strict manifest were independently
matched against the three files in this branch before retaining the evidence.
Production source has not changed since the checked revision.

The bounded evidence is in `docs/provenance/evidence/8773/finite-exception/`:

| Artifact | Retained SHA-256 |
| --- | --- |
| `finite-exception-strict-first.json` | `5a484f80a2355ee56638cad4dfc57ec2349808030f29d17639cba71b9557c1c5` |
| `finite-exception-first.log` | `b45cfd2d6e2bbb95a74d942c9d9f2e8207fdd2db751fece793a966e5f8983fb3` |
| `TNLean_PEPS_Approximation_ExactFiniteException.lean-finite-exception-strict-first.log` | `5a5e9019f5779af5470ccd7f626fcfb18a769f6eab51846213a24013ce222a00` |
| `TNLeanTest_PEPS_Approximation_ExactFiniteException.lean-finite-exception-strict-first.log` | `8c078929d6c6abd2369a2ff3cb7ab7b53b83c97175a05ca992dba7ff9d2fd26f` |
| `docs_provenance_evidence_8773_ExactFiniteExceptionAxioms.lean-finite-exception-strict-first.log` | `7cc89c0958f86a1749cf3f0cdfee1eee7648ea7280109de7061acfc3eb743114` |

`normalization.json` records every original and retained SHA-256. The four log
files are byte-identical to the parent originals. Only the manifest's three
`log` fields were shortened from executor-local paths to file basenames;
commands, source hashes, elapsed times, and exit codes are unchanged. Its raw
original SHA-256 is
`d428847e1576f75c2f3b7ebcff956ea2b0b3dd2d06b39a389bd0db5e1ece4a59`.
The raw originals remain in the parent-owned local validation directory.

The source/provenance worker did not run Lean, Lake, or mutate build caches.
Static checks also passed for whitespace, forbidden proof shortcuts, unchanged
elaboration budgets, and all three blueprint declaration links.

## Blueprint and publication boundary

The direct mathematical blueprint is
`blueprint/src/chapter/ch34_peps_exact_finite_exception.tex`. Its three theorem
and proof entries carry `leanok` after the local native checks above. These
marks certify the equivalence and its two auxiliary results against the pinned
interface; they do not certify the open sufficiently-large-size assertion.

The chapter is formatted with repository-pinned `latexindent` 3.24.7 and
`blueprint/latexindent.yaml`; a second pass leaves it byte-identical. The
formatter's SHA-256 is
`14a3f56807f9bdfa8b7b654bbfd054a59be79ddb959b57b691edcf39b2dc65e5`.
The original `blueprint-formatting.json` records the pre-anchor-repair source
at `17f7ba237e476c1ed833acbe8170675d4deb20e4`; it is retained unchanged as
historical evidence. The final render record below confirms the same pinned
formatter is idempotent after the label-only repair.

### Focused PDF and static HTML verification

The focused fixture combines three exact source leaves; it is not a render
of a single branch checkout:

| Source leaf | Origin commit | SHA-256 |
| --- | --- | --- |
| `ch34_peps_exact_tree.tex` (held native40) | `f7b46ce60c2469ffce1d8c0f56766a0cb6d30732` | `392d66b232ba779c8996d9f6044b104ca6cb23668e5f2f91ba22c708a8a5a035` |
| `ch34_peps_exact_small_size_approximation.tex` | `17f7ba237e476c1ed833acbe8170675d4deb20e4` | `38bb4cde695f9b6cc895c285403887f5529cf6072abaed997566638aeea5a7af` |
| `ch34_peps_exact_finite_exception.tex` | `a8e6abd11dca1e865f7520750aae3f23e5f142f2` | `0bd738c2003b56cd0b09aaa9a34d98ad78b120db93fe80ce4d97b1809b59a7d8` |

All paths are under `blueprint/src/chapter/`. Each leaf's hash was matched
independently to both its listed commit and the rendered fixture. The last
leaf was rendered while its label correction was staged above `17f7ba237`;
the byte-identical correction was subsequently committed at `a8e6abd11`.
The held native40 source was read for the fixture and was not changed.

The seven-page PDF and static HTML builds both returned zero. All seven PDF
pages were visually inspected. All five new declaration links (two small-size
and three finite-exception) and all 45 total declaration links were matched in
both PDF and main-chapter HTML. The final output has no missing static anchors,
duplicate HTML IDs, PDF reference/layout warnings, or strict web-renderer
errors. Declaration names match the source exactly. All three leaves pass
the pinned formatter unchanged.

The initial static HTML had five references targeting three absent equation
anchors: `eq:peps_finite_ground`, `eq:peps_finite_uniform`, and
`eq:peps_finite_large`. Commit `a8e6abd11` moved those labels to the first
numbered rows and suppressed numbering on the final rows. The rerender
resolves all five links. Mathematical and prose tokens are unchanged, and
the Lean sources retain their checked hashes. The complete original failing
report is preserved with only executor-local path prefixes normalized.

The compact final report and original-failure report are retained beside the
Lean evidence, with their transformations recorded in `render-normalization.json`:

| Record | Original SHA-256 | Retained SHA-256 |
| --- | --- | --- |
| `render-before-anchor-fix.json` | `fdf943d55b1b570535c578036cf58a6f71a8b29273b25741561352e7221ad73c` | `cb60f400515185df857595efe4e93460ec56cec79889163ab0e076f2ca4d6d3f` |
| `render-verification.json` | `c89a9003c0087d4b63d67401617b5bfa66defb7ffc95f5f1fc9fdae4f52ef8b3` | `c49722a348db65e136ed395ca55f0658be4e025fd1f88490febec87d36326648` |

The final PDF hash is
`ff54ec535cfc90ab0679ef80b12ec949a3f487197deca24c87182698e01c619f`.
The source, output, page-image, and raw build-log hashes remain in the retained
reports; the raw original reports and initial failing outputs remain unchanged
in the parent-owned render archive.

Live browser verification stopped at Chromium's socket `EPERM` failure, without
a bypass. The byte-identical `render-browser-block.log` has SHA-256
`a816421c050f927972d41940890035968452025f74e5ae55b657e28248511a69`.
Live MathJax behavior remains unverified. The renderer used the supported
Tenkz PDF-to-SVG fallback because `dvisvgm` is absent; inherited font-map,
title-page destination, and bibliography sorting warnings are preserved in
the report. The inspected PDF pages have no clipping, overlaps, or missing
glyphs. This does not assert that every tool log is warning-free.

The chapter remains deliberately unregistered in `content.tex`, and aggregate
imports are unchanged while the owned model dependency remains unmerged.
Full-book builds, integrated declaration checks, remote declaration publication
checks, and CI were not run. The focused render did not run Lean or Lake.
These are local checks, not a claim of main-branch availability.

This follow-on is separate from the publication-held #8773 native40 evidence
package. The existing exact-tree, small-size, and native40 sources, logs, and
evidence records are unchanged. TNLean #8773 and QIC publication holds remain
in force. No push, pull-request edit, issue comment, publication, merge, or
other external write was made.
