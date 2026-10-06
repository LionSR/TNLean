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

## Validation provenance

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

The heavy `SpectatorTransport` re-export remains inconclusive: its separate
native check reached the sixty-second wall bound with an empty log. It is
outside the validated core target closure. Full-package compilation and public
CI are separate checks, and the actual phase-cropped first/last edge and full
physical-chain identification remain mathematical obligations for the next
leaf. No physical uniform-gap conclusion is claimed here.
