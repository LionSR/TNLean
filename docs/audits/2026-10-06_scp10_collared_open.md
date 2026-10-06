# Collared rectangular open-boundary verification

Stacked base: `bf075954ea2b893453bb3319cd5e1e5bb895fc1e` (validated draft #8726).
Branch: `codex/scp10-collared-open`; draft [#8729](https://github.com/LionSR/TNLean/pull/8729).
The base PR, other-dot GLM23 code, and MPU-gauging code are unchanged.

## Checked result and scope

The independently defined open coefficient sums every region incidence label,
constrains region-side crossing incidences to boundary data, and multiplies site
coefficients and arbitrary matrices on internal labelled bonds. The generic
`network_deltaCompletedTensor` theorem proves its exact equality to a closed
network with PUnit physical indices, delta tensors outside, and identity
matrices on noninternal bonds. A chosen label fixes exterior incidences not
opposite the region. There is exactly one exterior assignment and no scalar.

`labelledNetwork_eq_torusBondNetwork` and
`torusBondNetwork_deltaCompletedTensor` transfer this result to the native
four-leg coordinates. Direction and endpoint polarity remain separate labels,
including parallel bonds and both incidences of self bonds. No simple-graph or
regular-representation adapter occurs.

`TorusDualCollar` states `cols + 1 < width` and `rows + 1 < height`. Its region
has lifted coordinates zero through the patch side length plus one, while the
swept support has coordinates one through the patch side lengths. The collar
is nonempty and embedded. Every native neighbor of a swept site lies in it;
therefore both endpoints of every noninternal bond lie outside the sweep.

The gauge is derived from the patch homotopy and `exists_fluxGauge`. The collar
makes it identity on noninternal bond endpoints, so internal flux matrices
extended by identity obey the same gauge equation. Closed gauge cancellation
on the delta-completed tensors and the exact bridge prove
`TorusDualCollar.openCoefficient_eq`. Summing against any joint boundary tensor
gives `TorusDualCollar.correlatedBoundary_eq`, with no factorization premise.
The group and representation are arbitrary. Physical indices are fixed only
on the region. The final theorem has no `Nonempty V` premise: an empty alphabet
makes the incidence-assignment type empty because the collar contains a site.

This is a collared rectangular specialization of SCP10 arXiv:1001.3807v3,
Lemma 6.14 (local source `Papers/1001.3807/paper_v3.tex`, lines 2199–2214).
The unrestricted source gap, arbitrary-region avoidance, cross-winding equality,
and vacuum reduced-density conclusions remain open.

## Strict validation and axioms

The focused check passed at `1e39277a1257ac051ac105c50746bd90df36409d` in
[run 37508551005](https://github.com/LionSR/TNLean/actions/runs/37508551005),
build job `112423801211`, step `Check labelled open coefficients early`.
It rebuilt the complete import closure with Lake after cache provenance pruning
and the explicit prebuilt Mathlib guard, then strictly elaborated all four new
production modules and the regression. Options included `autoImplicit=false`,
`relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`,
`linter.mathlibStandardSet=true`, and `warningAsError=true`.
Final whole-repository CI status is recorded in the draft PR.

Eight printed axiom lists are required and checked by
`scripts/check_collared_open_axioms.py`. The collar neighbor theorem uses
`[propext, Quot.sound]`. The generic bridge, native reindexing, native bridge,
derived internal gauge, open equality, correlated boundary equality, and
empty-alphabet coefficient theorem use
`[propext, Classical.choice, Quot.sound]`. No `sorryAx` or other axiom is allowed.
The physical-alphabet binder explicitly names the torus dimensions; the guard
also protects against synthetic elaboration holes in theorem types.

Regressions cover a translated seam-crossing collar, self-edge incidence counts,
a self-bond bridge with arbitrary matrices, the strict full-period exclusion,
and a nonvacuous empty-alphabet example: the zero-size patch on a two-by-two
torus has a full collar and an explicitly constructed empty-boundary assignment.
The axiom guard rejects missing audits, `sorryAx`, and unknown axioms in its
negative tests. All 29 cache-policy tests pass; blueprint declaration coverage,
import generation, source integrity scanning, and `git diff --check` pass.

Local official cache downloads remain blocked by the previously observed proxy
403. No mirror retries, network-setting changes, dependency updates, or Mathlib
source rebuilds were used. Proof validation used the authorized normal GitHub CI.
No merge or deployment was performed.

## Checked source hashes (SHA-256)

- `TNLean/PEPS/LabelledOpenCoefficient.lean`: `d3d8729292b158fda7861d98891b9aac83d33b1d59943cf67b97f01a68e1cd6b`
- `TNLean/PEPS/TorusLabelledOpenCoefficient.lean`: `70711b61eb5921d9bf5ce2e2910715a973f472320c3fefc9b10c10c8e6a31339`
- `TNLean/PEPS/TorusDualCollar.lean`: `bf26ea6ddb6bca38ab525a166526228558236fc92c0061926712233d3d6c4e28`
- `TNLean/PEPS/TorusDualOpenDeformation.lean`: `da4cd63e9a8bc0bb4b0c12def243016941b93eac2560fb1cf50c2e41b779556d`
- `TNLeanTest/LabelledOpenCoefficient.lean`: `cf2f84cf9b400a320f4020277403bd7d1439f8abf30c5572a0a398177c86aaed`
