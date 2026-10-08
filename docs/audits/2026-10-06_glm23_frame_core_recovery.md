# Recovery of the combined joint frame and core package

The recovery base is published commit `0c025f08eeb1ad50fb41a282488882114254d3bc`,
with tree `545b8e8f4a678dd25059766fa7239a9d05ad908b`, stacked on checked
boundary-package head `785006b9f7241cf0a7ef9dea17be44b38d64613f`.
It contains both frame/core packages, their separate audits and blueprints,
and additive production imports and strict regression registrations.

## Recovered changes

The generic `IsometricConjugationGap.lean` source is byte-identical to the
published endpoint-swap checkpoint `18fe4919ac69bfbf670245dcf6c9d0fe02808b47`.
Its five APIs transport intertwining, kernels, their orthogonal complements,
and arbitrary real norm gaps under an isometric conjugacy. The normalized
core comparison now calls this public theorem instead of duplicating its
private proof. No core hypothesis or conclusion changes.

The two new frame/core regressions scope `linter.hashCommand false` to their
final `AxiomChecks` sections. Their examples retain the default linter.
The inherited dependent-spectator regression is unchanged.

One shared mathematical entry in the existing chapter 13 martingale leaf
owns all five generic helper declarations. Its label is
`thm:martingale_isometric_conjugation_gap`. The core and endpoint-swap routes
can cite this entry without either route depending on the other.

## Historical validation before recovery

Before the workspace disappeared, individual strict native checks succeeded
for the generic helper (8.869 seconds), the updated core consumer
(25.451 seconds), the scoped core regression (6.708 seconds, five guards),
and the scoped frame regression (15.093 seconds, four guards).
Each used the pinned compiler, one thread, the package strictness and linter
settings, warnings as errors, and a sixty-second external wall bound.
The expected guard foundations were exactly `propext`, `Classical.choice`,
and `Quot.sound`. No failed output was promoted and no canonical cache changed.

The original shared worktree, artifacts, logs, and per-module source-hash
records became inaccessible at approximately 10:59 UTC. Successful tool
results remain recorded in the session. The production and test changes were
reconstructed deterministically from the published recovery base and the
published helper source, using the same edits that produced those observed
successful checks. The companion JSON records the recovered source hashes,
recovery-script hashes, and exact scope of the observations.

No compiler or setup command was rerun during recovery. The shared chapter 13
owner placement was first applied after recovery and is not represented as
having been rendered before the workspace loss. Historical render and native
records in the two package audits retain their original scope.

The historical isolated `SpectatorTransport` check reached the sixty-second
wall bound with an empty log. It lay outside the checked core target closure.
That observation remains part of the recovery record; the later successful
full build below resolves the re-export uncertainty.

## Public CI on the recovered source tree

The published draft #8725 head is
`d18d1a360223039dc366e1dc0c5ba43402065888`; its tree
`843e233eb40d2c59e080e57e64315301fe1ec857` matches the locally authored recovery
commit `3b4ff7c1fe616fcb9be7325675e66e1635246ec4` and the tested merge
`3eee7cf359b6cfd1fbe62e585b02a8bccb1fc7ad`.
[Run 37468535974](https://github.com/LionSR/TNLean/actions/runs/37468535974)
passed all six jobs, verified on 2026-10-06 at 13:42 UTC.

The [build job](https://github.com/LionSR/TNLean/actions/runs/37468535974/job/112286081510)
passed the full Lean build, all registered regressions, text style, changed-module
timing checks, and compiled blueprint and paper-gap declaration checks.
`SpectatorTransport` compiled in 32 seconds and the core Hamiltonian module in
18 seconds. The re-export receives the ordinary 25-second timing warning,
below the 50-second failure threshold; it is no longer an inconclusive check.
The strict mixed-endpoint regression step includes the five core guards,
four frame guards, and two existing dependent-spectator guards, each expecting
exactly `propext`, `Classical.choice`, and `Quot.sound`.

The [blueprint job](https://github.com/LionSR/TNLean/actions/runs/37468535974/job/112286081508)
also passed. Its successful steps include the full web build, generated-page
checks, native tenkz lint and render checks, reader-facing prose, LaTeX
formatting, source synchronization, and changed-declaration reverse coverage.
This job does not establish a full-book PDF build.

The core leaf now has 12 checked statements and seven checked proofs. The
generic conjugacy owner already had its statement and proof checked; its
source is unchanged and byte-identical to the owner in the periodic-swap
branch. The frame leaf retains its 12 checked markers. These marker changes
and audit updates follow the CI run; they do not change Lean sources, tests,
imports, or workflows. The companion JSON distinguishes the tested tree from
the subsequently rendered documentation sources.

## Focused documentation checks after CI

The restored documentation environment rendered the final core leaf, the
unchanged frame leaf, the full shared conjugacy statement and proof, and their
referenced statements. The PDF has 11 pages; physical pages 3–7 were visually
inspected, including the full-frame contraction diagram and both checked
conjugacy markers. No overflow or unresolved-reference warnings remain. A
sentence in the edge-regrouping definition was split to fit the new checked
badge; its two coordinate maps are unchanged.

The focused HTML resolves all 28 target labels and 87 declaration links, with
no missing local anchors, duplicate IDs, or rendering sentinels. Global source
synchronization passes using the manifest-matching QICLean sources. All 105
public declarations in the eight added production modules have exactly one
blueprint owner; this count includes the moved spectator declarations.
The pinned latexindent 3.24.7 byte comparison, changed reader-facing prose
check, and whitespace check pass.

All three tensor pictures use tenkz. Their event sweep reports zero hard
findings and zero advisories across two units. The one equation display uses
the source equality for an advisory boundary comparison; it does not declare
a hard equation-group scope. The diagram was visually inspected in the PDF.
Browser visual inspection and a local full-book render were not repeated.
No local Lean or Lake command was run for these documentation checks.

The actual phase-cropped first/last edge and full physical-chain
identification remain separate mathematical obligations. This package proves
the normalized operator identities and full two-site frame reduction. No
physical endpoint uniform-gap conclusion is claimed here.
