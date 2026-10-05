# Inhomogeneous preparation import boundary

Continuation of [#8637](https://github.com/LionSR/TNLean/issues/8637), after
[#8651](https://github.com/LionSR/TNLean/pull/8651) extracted the pair and
block-circuit algebra and [#8669](https://github.com/LionSR/TNLean/pull/8669)
extracted the physical-matrix interface. This change does not repeat either
extraction or claim another mathematical result.

Baseline: `680b30da6fec94f5b269c3753ab4b8c86da79936`.
Both sides use Lean/Mathlib `v4.35.0-rc3` and QICLean
`2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`.

## Smallest remaining dependency

`InhomogeneousPreparation` still imported `DepthUpperBound`, although its
construction uses the generic circuit declarations already extracted to
`BlockStatePreparation`. `ShortChainPreparation`, also used by the exact
inhomogeneous preparation theorem, had the same import. Its additional needs
were `MPSTensor.normalizedMPVState` and `MPSTensor.norm_normalizedMPVState`,
which were defined in the convergence-heavy `ApproximationError` module.

The two normalization declarations now live beside `mpvState` in the existing
`MPS.Overlap.Basic`. Their declaration text, docstrings and proof are unchanged;
`ApproximationError` still exports the same names through its imports. Both
consumers import `BlockStatePreparation` directly. There is no new production
module, alias, assumption, or matrix API. QICLean ownership is unchanged. The
four production files have a net increase of two lines for the local variable
context, with no increase in proof text.

The fixed-point and approximation-convergence declarations remain in
`FixedPointPairs` and `ApproximatingState`. They genuinely use the higher theory;
removing it from those modules is not the goal. The generic circuit route no
longer imports either module.

## Source-import evidence

Closures include the named root and count TNLean, QICLean and Gametheory modules,
excluding Mathlib. Traversal removes nested Lean block comments and line comments
before reading imports. All reached QICLean source files were compared against
the pinned revision. No import cycle was found.

| Root | Before | After |
| --- | ---: | ---: |
| `BlockIsometryState` | 91 = 23 TNLean + 68 QICLean | 91 = 23 TNLean + 68 QICLean |
| `PartialIsometryPreparation` | 360 = 138 TNLean + 219 QICLean + 3 Gametheory | 120 = 52 TNLean + 68 QICLean |
| `InhomogeneousExactPreparation` | 363 = 141 TNLean + 219 QICLean + 3 Gametheory | 123 = 55 TNLean + 68 QICLean |

The last row is an actual noninjective, inhomogeneous physical preparation
endpoint, `exists_isPreparedInDepth_normalizedChainState`, rather than a new
intermediate interface. Its hypotheses and conclusion are unchanged.

## Validation and timing scope

The regression `TNLeanTest/PreparationAlgebraBoundary.lean` imports the exact
inhomogeneous endpoint, exercises zero and nonzero periodic-state normalization,
and checks the compiled environment for the absence of normal-gauge construction,
normal-state convergence, and every Gametheory module.

The focused checks use one Lean thread, the package's four Lean/linter options,
prebuilt Mathlib artifacts, and isolated output directories. Cached dependencies
are reused only when their source and dependency closure match; cached TNLean
source hashes are checked against their Lake build traces. No Mathlib or
Gametheory source build is run.

All 24 affected modules in the 55-module TNLean closure passed with no diagnostics.
The strict regression passed with `autoImplicit=false`, the standard linter set,
and warnings treated as errors. Integrity, generated-import, numbered-file,
oversized-file, workflow-YAML, whitespace and added-prose checks passed.

Single-thread elapsed observations, including source elaboration and writing the
module artifact (the regression does not write an artifact):

| Check | Baseline seconds | Candidate seconds |
| --- | ---: | ---: |
| `BlockIsometryState` | 3.35 | 3.55 |
| `PartialIsometryPreparation` | Not measured | 3.26 |
| `InhomogeneousExactPreparation` | Not measured | 2.87 |
| Strict import-boundary regression | New test | 2.62 |

These runs use the same pins and cache-reuse protocol, but are single observations
under variable machine contention. They are not a speedup benchmark. In particular,
one prerequisite fluctuated from about 12 to 193 seconds between runs before the
later module timings returned to their usual range.

Controlled before/after timings for the two broad baseline consumers are still
unavailable. Their baseline requires 48 uncached TNLean and 22 uncached QICLean
modules even before the exact capstone; warming that route solely for a benchmark
was deliberately deferred. Structural reductions are not a speedup claim, and
this acceptance item in #8637 remains open.

The source Blueprint checker produces the identical report on baseline and
candidate (523 existing unresolved references in this checkout without the
companion-library source setup). The two moved declarations retain their existing
Blueprint tags. This is not a clean compiled declaration check; full-root and
compiled declaration checks remain required on the exact published commit.

## Concurrent work

The global-rate and canonical-fixed-point work retain the same normalization
names and signatures. All four open PR file lists were checked before publication;
none overlapped the four changed production files. The PEPS ground-state PR also
edits the CI workflow, but in disjoint steps; the new preparation regression does
not replace any existing test loop. The canonical-fixed-point regression is also
planned as its own separate CI step.
