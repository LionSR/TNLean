# QICLean Poisson-growth dependency compatibility

## Exact revisions and scope

TNLean base: `a82c6c82a9e509673f51e5bfa0bfab13be29eca6`, including
[#8960](https://github.com/LionSR/TNLean/pull/8960).
The QICLean pin advances from
`eb12c672aafdb0d536253feec158edf00f69fb54` to
`7224037adaee0efa1314f299970bc35db9cdf78b`, the merge of
[QICLean #705](https://github.com/LionSR/QICLean/pull/705).
The target also includes [#698](https://github.com/LionSR/QICLean/pull/698)
and [#699](https://github.com/LionSR/QICLean/pull/699), needed by the physical
Poisson-word consumers under [TNLean #8757](https://github.com/LionSR/TNLean/issues/8757).
This is an exact commit pin, not a moving branch reference.

Only QICLean's revision changes in `lakefile.toml`, `lake-manifest.json`, and
`docbuild/lake-manifest.json`. Lean remains `v4.35.0-rc3`; Mathlib remains
`c55e6e786f49471c72fbddbec5415808896aec1e`. Every other dependency record and
package option is unchanged. QICLean's own `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json` are identical at the two revisions.

The complete QICLean delta contains 341 changed files. The production Lean
portion is 121 files under `QICLean/`: 109 added and 12 modified, with 19,528
insertions and 73 deletions. The other 220 paths concern tests, documentation,
validation material, scripts, and repository configuration. No production
Lean file is deleted or renamed. This audit does not import or copy OpenAI
upstream Lean source.

## Existing APIs and new consumers

The nine pre-existing `QICLean/Probability/PoissonWord*.lean` modules are
unchanged. Nine further Poisson-word modules provide insertion weights,
marked insertion, retained-prefix occupation, real occupation, bounded signed
jumps, weighted growth, spatial growth, and actual stretched-shell growth.
Their analysis prerequisites include `ExponentialDistanceProfile`,
`MetricBallKernel`, `StretchedBallKernel`, and
`StretchedExponentialSummability`.

Of the 12 modified production files, six are import aggregators.
`LogClipping` and `OrthogonalResolution` add declarations without changing
existing declarations. The remaining four modules refine entropy estimates:
`FilterConjugation`, `FilterEnergy`, `FilterChainEnergy`, and
`SupportedMarginalTails`. Their old public statements remain under the same
names and with the same source signatures; the sharper results use new
`_sharp` or `_inner` names. In particular, the old full-support, factor-four
bounds remain available. The changed proof of `card_innerConfig_le` also
retains its original statement. No removed public declaration or changed
existing source signature was found in this comparison.

A comment-aware lexical comparison of explicit declarations and namespaces
against current TNLean found one new collision. The active physical source
modules on the weighted-row, event-kernel, propagation, actual-family,
lattice-family, and channel-word branches were also scanned; no additional
collision with the new QICLean names was found. These modules use their own
`TNLean.PEPS.AreaLaw` and `QuantumCircuit` namespaces. This is a source scan,
not an elaborated-environment or generated-declaration audit.

## Removed local declaration and upstream replacement

| Removed TNLean declaration | Replacement |
|---|---|
| `Matrix.l2_opNorm_mul_le_one` in `TNLean/Algebra/MatrixL2Contraction.lean` | QICLean's declaration of the same name in `QICLean/Analysis/RectangularTraceNorm.lean` |

Both statements bound the product of arbitrary rectangular complex
contractions by one. QICLean takes its two matrices as explicit arguments;
TNLean previously made them implicit. `MatrixL2Contraction` now imports the
upstream module and removes its duplicate declaration. All 12 applications
across `MatrixL2Contraction`, `OwnershipMonomials`, `TwoSheetExchange`,
`HomogeneousOwnership`, and `PatchRewrite` supply the two arguments. The
mathematical statements of these consumers do not change. No compatibility
wrapper is retained, and no blueprint declaration tag names the removed
local declaration.

The earlier rectangular identity-Kronecker repair remains intact:
`Matrix.l2_opNorm_one_kronecker_rect_le` and its consumers still use the
name introduced in #8960. The corresponding
[rename audit](2026-10-08_one_kronecker_norm_rename.md) remains valid.

## Validation status

Passed before compilation:

- Exact old-to-new QIC revision substitution in all three dependency files;
  parsed root/docbuild manifests agree on all 12 shared packages.
- `python3 scripts/check_docbuild_manifest.py`.
- `python3 scripts/generate_import_aggregators.py --check`.
- `python3 scripts/check_reader_facing_prose.py --root . --diff-base a82c6c82 --ci`.
- `git diff --check` and source scans of the changed Lean files for prohibited
  proof escapes.

The production candidate `6c53694c35a230686bf2499cfca3ad3544aba6be` passed
linter-bearing native builds of all five changed modules,
`TNLean.PEPS.AreaLaw.Amplification`, and
`QICLean.Probability.PoissonWordSpatialGrowth` (3,499 jobs, 234.8 seconds).
Strict elaboration of the five changed modules plus the existing
`GraphChannelWeightedRow`, `GraphChannelEventKernel`, and
`LocalRootChannelsAxioms` consumers passed with no diagnostics. These commands
set `autoImplicit=false`, `relaxedAutoImplicit=false`, `pp.unicode.fun=true`,
`maxSynthPendingDepth=3`, `linter.mathlibStandardSet=true`, and
`warningAsError=true` explicitly.

`TNLeanTest/QICPoissonCompatibility.lean` preserves the combined-import check
for Amplification, TwoSheetExchange, and the spatial Poisson module. Fully
applied examples check arbitrary rectangular types with separate universes,
a `2 × 3` by `3 × 5` product, and empty row, intermediate, and column types.
The upstream theorem has no `Nonempty` assumptions and needs decidable
equality only on the intermediate and column types. Exact `#guard_msgs`
checks require the axiom closure `[propext, Classical.choice, Quot.sound]` for
the upstream contraction theorem, the local compression and finite-product
consumers, and the spatial Poisson growth theorem. This regression passed
strictly at `9a76fdc08eb71da30160c632aabeadf7e8795ec2`; its production sources
are unchanged from the native-build candidate. CI runs the regression in the
existing QIC import-compatibility step, after explicitly building the new
spatial Poisson prerequisite. It preserves the existing conjugator regression.

Official Mathlib cache retrieval succeeded, and
`lake --no-build build +Mathlib:leanArts` passed before the native builds.
All 12 dependency checkouts were clean at their exact manifest revisions.
No Mathlib source was rebuilt; existing artifacts were reused through Lake's
normal trace invalidation, with no artifact copies or trace rewriting.

These are focused compatibility checks, not a full `lake build TNLean`.
The production delta is broader than the Poisson additions. The full hosted
root build, blueprint declaration checking, and normal CI checks remain
required before merge; later physical-consumer revisions also need their
own validation against this exact pin.

OpenAI Codex (GPT-6) prepared the dependency edits, local compatibility
adaptation, and this audit. No mathematical completion is asserted here.
