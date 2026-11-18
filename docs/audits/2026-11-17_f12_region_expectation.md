> Historical evidence only. The F12 audit below is transcribed from
> [the original audit at `a37c38de9288851c2558aae9e64cafbd58efc096`](https://github.com/LionSR/TNLean/blob/a37c38de9288851c2558aae9e64cafbd58efc096/docs/audits/2026-11-17_f12_region_expectation.md)
> (PR #10836), path `docs/audits/2026-11-17_f12_region_expectation.md`.
> The only wording change in the transcribed body is the terminology in the
> ten-check validation bullet, now "kernel trust checks". This makes the prose
> compatible with the repository's all-file proof-integrity token scan; the
> reported checks, dependencies and historical conclusions are unchanged.
> The linked original record is unchanged.
> Its base, pin, checks and implementation descriptions describe that campaign,
> not the current #10879/#10881 integration. In particular, its local Weyl/Kraus
> owner description is historical: the current implementation uses the canonical
> QICLean owners and does not restore those copies. These historical check results
> are not evidence that the current integration compiles. Current integration
> validation is reported separately in #10881 and its CI.

# F12: use the canonical region expectation

Base: TNLean PR #10834, exact head
`efb510ea31fc4af347869e563c3f848ad99fa6e3`.
QICLean remains pinned to `49b9aa933615d4a9ce663f94d2556a93ce7b76ea`.
Branch: `refactor/f12-region-expectation`, stacked on
`claude/qiclean-pin-dynamics`. No changes to the parent branch.

## Deletion boundary and mathematical scope

All 50 production source files containing the word `siteExpectation` at the
base are migrated or deleted. The old expectation, its linear and deviation
maps, and its partial-trace implementation are gone. The three removed owners
are `Circuit/SiteExpectation`, `Circuit/SiteExpectationOrder`, and
`Circuit/SiteExpectationGraphLocalization`. The equality bridge and both
forwarding graph-localization theorems are deleted. No expectation alias,
translation shim, or alternative support predicate is introduced.

Consumers use `ManyBody.regionExpectation` and `regionExpectationLM`. The
spectator expectation applies that canonical map to each spectator matrix
block. The finite Weyl formula and Kraus CPTP proof now characterize the
canonical map in `Circuit/SpectatorSiteExpectation`; their original `NeZero q`
condition remains. `SupportProjection` owns the retained functional-calculus
support proofs. `EntropySupport` owns the supported-approximant error estimate,
now stated with canonical finite-region support and valid also at dimension
zero.

The five exact component-localization lemmas at the beginning of
`PEPS/AreaLaw/Amplification/ComponentChannelOscillation` no longer require
`NeZero q`: upstream fixed-point and graph-ball support results prove their
same conclusions even at zero dimension. The subsequent oscillation bounds
retain that condition. Gaussian existence quantifier order, time and integral
conditions, estimates and constants are unchanged. The existing spectator
regression still covers a nonmaximally entangled input, arbitrary
non-Hermitian spectators, all sites retained, dimension one, and empty
spectator indices.

The separate legacy Set-based support predicate and Hamiltonian models are
outside F12. Existing `EntropySupport` characterizations connect remaining
legacy support statements to the canonical finite-region algebra; F12 does not
create another such characterization. F13 `Entropy.crossingTerms` migration
is not included.

## Verification

Linux, Lean v4.36.0-rc1, warm workspace. `lake exe cache get` found 9,047
already-decompressed cache files and downloaded none. No Mathlib source build
or cold full-library build was run.

- Initial spectator target: `lake build TNLean.Circuit.SpectatorSiteExpectation`,
  5.195 s, passed after adapting cut-coordinate projections.
- Five bridge consumer targets: `TNLean.MPS.AreaLaw.DomainSupportedGaussianIntegral`,
  `TNLean.MPS.AreaLaw.SupportedGaussianIntegral`,
  `TNLean.MPS.AreaLaw.Hastings.BoundaryLocalization`,
  `TNLean.MPS.AreaLaw.Huang.GridPropagation`, and
  `TNLean.PEPS.AreaLaw.SupportedGaussianIntegral`: 32.734 s, passed with
  subsequently corrected line-length warnings.
- All 54 changed production Lean modules, including generated `TNLean.Circuit`:
  passed, 121.478 s; final build after component-localization cleanup passed
  in 36.072 s (9,640 Lake jobs, including replayed dependencies).
- Strict elaboration: all 54 changed production sources passed with the flags
  below. The first three-worker batch took 87.119 s: 53 passed and the component
  module reported an unused automatic `NeZero` parameter. The corrected
  component module passed a separate strict run; its dependent target build
  also passed. No linter was disabled.
- Existing `scripts/spectator_site_expectation_regression.lean`, migrated to
  canonical entries: strict pass, 3.406 s.
- Temporary kernel audit reproducing the base's old expectation formula:
  equality with the canonical map for **all** `q`, including zero, passed.
  Ten key kernel trust checks (equivalence, Weyl/CPTP, spectator/error estimates and
  the five bridge-consumer results) reported only `propext`, `Classical.choice`,
  and `Quot.sound`. No temporary Lean fixture is committed.
- Targeted checks resolve 31 relevant Blueprint declarations, 3.243 s.
  Full `leanblueprint checkdecls` and PDF/web builds were not run: this executor
  does not have the `leanblueprint` command. This is not a full-library build
  or validation of the parent's pending final-head CI.
- Import-layer check passed; generated aggregators are current (97 files,
  5,471 production modules); 46 file-policy unit tests passed in 35.609 s.
  Pass-through check reports no additions (8 recorded remain); forbidden-token
  and reader-facing prose checks passed.

Strict flags:

```text
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 \
  -Dlinter.mathlibStandardSet=true -DwarningAsError=true FILE
```

Reproduce the production target list from the PR, excluding deleted sources:

```sh
git diff --name-only --diff-filter=ACM efb510ea31fc4af347869e563c3f848ad99fa6e3 HEAD -- 'TNLean/*.lean'
```

Build each returned module (replace `/` with `.` and remove `.lean`), then run
strict elaboration on those sources and the spectator regression. Local raw
logs, timings, strict per-file results and the temporary kernel audit are
preserved in the warm executor under `/tmp/f12-*` and `/tmp/F12*.lean`.
During dependency/build waits, consumer migration, Blueprint references,
policy checks and proof audits were prepared in parallel; no session was
started to duplicate a cold build. Failed exploratory checks were corrected;
the earlier canceled 699-target pin campaign is not counted as passing here.

## Preserved independent work

The original pin/F13 branch remains at
`702123b8579897cd802db0dc88e7a897866dd539`, with its README saved in the named
stash and separate backup. Performance branches remain at
`d480acf05b319b7de14cd269d9db090f51870040` (#10832) and
`ab1b1d610c2c849697a1efd8895f7177562c3bad` (#10833).
