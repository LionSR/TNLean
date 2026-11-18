# Isolated placement-pin integration: review candidate

Preserved backup: db55866689688dab942d646a38f91fe4f2b3c53d on
backup/10881-pre-new-pin-evidence. Recovery found no active build, a clean
9a440ee87474b5564ed26c297c7f63e0ab81aeac tree, and 4.6 GiB free. Its old-pin
15-target queue had five build/strict passes, one failed target and nine not
started. These results are historical, not evidence for the new pin.

Main: 75fc22288234ef66239cb4c2fa0b22914cfa5c6b.
PR 10905: 8a040ee527c3a4861ab2a5c1369bf9a9c9d611fd (still open when read).
QICLean: 729428582b78ab7529b3796099193649f947354a.
Main's b5ad5f5aa (#10903) supplies all four canonical interval opens: the three
local edits merged identically and the fourth came from main. No duplicate
opens or repeated cherry-picks were introduced. Formatting patch 5f9d620b was
absent both ancestrally and textually and was applied exactly once (012eb9cc6).

## Conflict and scope assessment

Both sequential merges were text-clean. There are eleven direct overlap paths
(overlap11.txt): five PEPS Lean files and six documentation files. Zero textual
conflicts is not mathematical or compilation clearance.

The five Lean overlaps preserve the reviewed scope corrections while adopting
10905's direct global configuration coordinates. RangeNestedPatchEnergy still
requires normalization and canonical eigenspace membership, not singleton
span; positive-gap callers still obtain gap/span through the explicit bridge.
NestedPatchApproximation retains the projector-PSD and membership inputs when
constructing its square-state evidence. RangeNestedPatchApproximation keeps
the hDelta-positive conversion; adaptive supply and marginal closeness adopt
the new global coordinates consistently. The stale range-energy docstring
claiming a one-dimensional eigenspace is corrected; proof and signature are
unchanged by that local edit.

Geometry, LocalCircuit, Channel/Layer, SitePermutation, both spectator owners,
Basic, BoundaryTheorem and BoxEntropySupremum remain byte-identical to e06a33e5.
All fixtures and arbitrary Aux/bond/site/control and nonpositive-gap repairs
are retained. Deleted local lift definitions are not reintroduced. The only
remaining dependentRegionOperatorLift_sum name is a private HoleEncoder lemma
whose statement and proof directly use ManyBody.place, not a second placement
implementation. F12 historical descriptions, F4 dedup follow-up and new F12c
placement record coexist. The new place owner is QICLean/ManyBody/Sites/Placement.

## Validation boundary and next targets

Static checks passed: import layers, 84 selector tests, 12 timing tests,
22 immutable-snapshot tests, roles and whitespace. Blueprint sync initially
failed for two unavailable Mathlib source declarations; only unchanged,
revision-matched dependency links were then installed and sync rerun successfully.
The separate QIC checkout has no imported old QIC/TN build products.
Any placement-owner build result is recorded separately; it does not validate
the five combined TN consumers or the regression fixtures.

impact.json records 113 directly changed TN files relative to 012eb9cc6
(119 relative to e06a33e5), 29 changed QIC modules, 1668 existing affected
TNLean/ modules and 11 affected fixtures. The removed local lift path is excluded.
MergeRounds is an additional delta relative to e06a33e5 outside this closure. Old-pin
passes cannot be relabelled as new-pin success. Prioritize the five overlap
consumers, the retained zero-gap and arbitrary-label fixtures, then the full
recorded affected set after independent review. The unrelated old-pin consumer
queue remains assigned to its original worker; it was not restarted here.

No external author branch, shared PR head/base, or issue body was modified.
This candidate is for independent review, not merge approval.

## Completed narrow new-pin check

QICLean.ManyBody.Sites.Placement built successfully in 21.80 seconds and
passed repository strict flags in 6.20 seconds from a separate new-pin QIC
checkout. Only revision-identical Mathlib/other dependency caches were reused;
no old QIC or TN build artifacts were reused. This proves neither the combined
TN consumers nor the eleven fixtures at this pin. validation.json records the
exact command and boundary. All four DG sources now match 75fc2228 exactly,
with one canonical interval open each; the formatting file matches 5f9d620b.

## Shared history and partition checkpoint

Candidate 6b7fb2e27dbc6856091e593e4226d350403beb8a merges the complete
shared history through 70db80c3928565d8b9741aa2b7400c293cdd9211. The only
new shared commit adds the Edge open already supplied by main; its duplicate
automatic insertion was removed. Both this merge and b63e6f6c have tree
b535ccb984038d4b8f8d47bb874bc17035ab5f03. Subsequent partition files are
audit-only and do not change production sources or dependencies.

partition.json records sorted UTF-8 LF manifests and SHA256 hashes: MPS 864,
PEPS 591, other 213; their disjoint union contains 1668 existing paths.
The five overlap consumers are reserved here, not yet certified at this checkpoint.
MergeRounds is separately assigned to the MPS worker as an extra delta.

The repository provides export_coherent_qic_prerequisites.py and
export_coherent_tn_prerequisites.py. They verify exact dependency pins, toolchain
and clean source provenance; the TN exporter additionally requires its recorded
baseline configuration and source closure. These are bounded prerequisite sets,
not full-closure caches. No cross-environment cache transfer is assumed or done.

## Completed sixteen-target validation

All five overlap consumers passed build and strict; all eleven listed fixtures
passed full strict at pin 729428582. target16-ledger.json contains exact commands,
exit codes and separate elapsed build/strict times; production editing time is zero.
Raw logs include the first CZX strict failure (missing direct-import olean), its
narrow dependency build and successful retry. No proof or implementation was edited.
The audited production snapshot is 6b7fb2e27; subsequent commits only change audits.
This does not certify the remaining 1668-module reverse closure.

Bounded cache exporter probes: QIC refused a missing ZModCyclicSums artifact;
TN refused its historical baseline toolchain mismatch. Neither check was bypassed
and no transfer or extra cache build was started. Workers must validate their
own exact-pin source/artifact provenance.

HoneycombCluster additionally passed new-pin build (7.51s) and strict (4.28s).
This is separate evidence for the owner of the historical root-PEPS failure;
it does not retroactively certify the old-pin closure or the root aggregator.
PEPS queue excludes the five overlap consumers and HoneycombCluster: 585 remain.
The root TNLean.PEPS check belongs to the other shard after prerequisites are ready.
