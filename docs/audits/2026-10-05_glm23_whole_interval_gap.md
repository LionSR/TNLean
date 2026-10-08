# GLM23 whole-interval gap: source and validation checkpoint

Initial checkpoint: 5 October 2026. Historical compiler checkpoints below
are retained without upgrading their evidence. The full proof checkpoint
on 6 October is recorded next; this is not a full-paper completion claim.

## Latest proof checkpoint: 6 October 2026, 01:36 UTC

Head `0c51478b87ef711dc7e339cfa5a166456f0a20c5` passes the full Lean
build, both new strict regression files, all three standard-axiom guards,
style and declaration checks. The final uniform-path module compiled in
9.0 seconds. The unchanged timing gate passed; six 25-second advisories
remain, with maximum changed-module time 48 seconds below the 50-second
failure threshold. No claim of zero advisory warnings is made.

Run [37398080332](https://github.com/LionSR/TNLean/actions/runs/37398080332),
build job `112058990825`, checked merge
`5a364cfc2b717793730e9c3e81f0ab53f97fbcf3`. Its tree
`b97968d93c0233f1e5c23194b247004d806f5f7d` exactly equals the proof
head and local commit `0497edf559d6e508baae6b80e3f3224f047f172a`.
The exact source/pin hashes are preserved in
`2026-10-06_glm23_whole_interval_checked.json`.

The guarded results allow only `propext`, `Classical.choice`, and
`Quot.sound`. They cover the uniform closed-interval periodic gap, both
endpoint open gaps, and continuous periodic kernel projection. The two
strict regression files also check the theorem signatures without adding
finite-window, supplied-gap, or kernel-continuity hypotheses.

The full blueprint/browser job is still running at this proof checkpoint.
Checked-marker documentation changes require fresh exact-head validation;
the successful proof tree is kept distinct from that later final tree.

## Source assumptions and conclusion

Source context: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`Papers/2203.12563/REsubmission.tex`, Section 5, lines 1687–1692;
the finite-window compactness argument follows arXiv:1010.3732, Appendix A.

The declaration
`MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_periodic_path_gap`
takes positive natural bond dimensions D₀,D₁ and the actual given tensors
Aₚ : MPSTensor (Dₚ * Dₚ) Dₚ, each one-site injective. Its conclusion is one
δ>0 such that δ‖v‖≤‖H′γ,N v‖ on the actual periodic kernel complement,
for every γ∈[0,1] and every N≥2. The constant may depend on the endpoints.
The square physical alphabets are assumptions, not an unstated reduction
from arbitrary original alphabets. No fixed-point, supplied gap, kernel
identity, or projector-continuity premise is added.

The proof derives endpoint open gaps by bounded changes at the two boundary
sites and free-exterior-register comparison. Strict windows persist locally;
Knabe is used only in the injective interior, with m+1 sites and N≥2m.
Separate endpoint periodic bounds cover the ends. Compactness gives a
uniform large-volume bound, and the continuous actual periodic ground line
handles the finitely many shorter rings. Full MPO covariance along the path
and the resulting symmetric-phase classification remain separate.

## Immutable compiler checkpoint

Of 26 additional production modules, the following eight exact repaired
versions have local canonical targeted-build passes. The other 18, including
`MixedEndpointUniformPathGap`, and both new strict regression files remain
pending at this checkpoint. Earlier frozen or warning-bearing versions do
not inherit the passes below. Later CI results must identify their own tree
and bytes rather than retrospectively changing this checkpoint.

| Module | Checked SHA-256 |
| --- | --- |
| `SquarePhysicalCoordinates` | `4bc2d69d57bfad4df4b506573347d7c30bcba9e2dec702ba61ab22d5811b6ddd` |
| `MixedEndpointBoundaryFactors` | `27434b4dccd7fda6d432bcd3d6564e1b5a01afaacc3e86e698f7abbf13b7a582` |
| `MixedEndpointBoundaryCoordinates` | `7fc0e92d26f6f6323bb709be2d7fd0b2d3a3bcf7f6c4d984b285664b4c11c2f6` |
| `BoundedCongruenceGap` | `81bb3e0de99f02a78e3bff75f24aec74975fed68aad791e1cdfb150567192fcd` |
| `LocalEquivalenceBounds` | `e88204615c1b2f56ee327338f0a8bf9320383e4b5c463194b1f4855d5353ab58` |
| `MixedEndpointOpenSectors` | `a17c56a7b281421019ad9146ea2de8d84d08c1b736d110ebc0ea447d2773eb6d` |
| `BoundedProjectionDeformation` | `e3bcc360a3e46c1a74568277709792806aaa105986e94496013749104c45db99` |
| `MixedEndpointActiveBoundaryTransport` | `9dc053fbf4f0e9180b5eab15af24d656e0b22ba6851ec389d9b07cd5ac93a88e` |

The final assembly source under review has SHA-256
`aa71b0ea4c35a480230ec594525a5225063494ee8b72feacff9a901d138fe1ed`.
It has no compiler pass credited here. `TNLeanTest/MixedEndpointOpenGap.lean`
and `TNLeanTest/MixedEndpointUniformPathGap.lean`, including their guarded
axiom expectations, have not passed the new strict-regression checkpoint.
Expected guard messages are not observed axiom-audit results.

## Review and documentation evidence

Independent mathematical review of the exact assembly and separate review
of its continuity prerequisites found no mathematical or hypothesis leak.
Earlier endpoint-chain reviews checked the boundary deformation directions,
volume-independent norm bounds, exact local projections, and spectator
comparison. These are source reviews, not Lean elaboration evidence.

The two continuation leaves now uniquely own all 378 named top-level public
declarations in the 26-module cone. Their original 369 owners and labels
are preserved; seven coordinate aliases and two edge-index types fill the
nine missing owners. Both leaves remain without `leanok` markers.

The actual pinned texra-blueprint 0.3.8 strict web CLI passes with exit 0.
Generated-source/HTML checks, all references, 378 main declaration links,
and pinned latexindent idempotence pass. A 28-page focused PDF includes the
two leaves and exact supporting excerpts. All affected main-text pages were
visually inspected; the final log has no warnings or overflow. A preview-only
2em emergency line-stretch setting fixes an unchanged appendix heading;
no shared preamble changed. Interactive browser checks are not claimed.

Frozen leaf hashes:

- `ch30_mpo_mixed_open_gap.tex`:
  `fdc36ddd9413c6eb51ef78def0ada97131fedff035162020912efc7cfae548ca`
- `ch30_mpo_mixed_uniform_path_gap.tex`:
  `c4557da78356973dbedf047baa15ad9500bd3b2069d9f7edb2518d6f0de6634e`

This documentation work adds no compiler credit and changes no Lean source,
router, workflow, dependency, or verification marker. Publication of a draft
does not establish the pending theorem cone or the full phase classification.

## Publication structure

The publication snapshot separates the active-edge coordinate/placement
results from the boundary-normalization and deformed-sum identities.
`MixedEndpointActiveEdgePlacement` now imports only the prerequisites for
its 457-line coordinate development; the new 664-line
`MixedEndpointActiveEdgeNormalization` imports it and owns the normalization
results. The two consumers import the latter module. Declaration names and
proof bodies are preserved, and all 378 public owners remain unchanged.
The draft therefore has 27 production modules: the eight checked hashes
above and nineteen modules still requiring validation. No compilation
credit is inferred from this source-only structural split.

## Subsequent compiler checkpoint: 2026-10-05 22:36 UTC

The published `7d39eed` head's workflow did not reach Lean compilation:
its starting job was cancelled during the GitHub Actions incident. Those
cancellations are not evidence of a mathematical or compiler failure.

Local validation subsequently compiled the repaired
`MixedEndpointActiveEdgePlacement` (SHA-256
`faf560f28f995057a24521a7a527c0e25df5c75c2a16133aa05e935d7392af31`),
plus `MixedEndpointRightComparison` and `RingEndpointRightComparison`.
The first full check of `MixedEndpointActiveEdgeNormalization` found
coordinate-projection argument, definitional-coercion, and explicit-argument
errors. This batch repairs those proof terms without changing its theorem
statements. Its strict follow-up check lost the executor connection without
a terminal result; no compilation pass is credited to that repair.
The final normalization hash under review is
`548d6e29cf4de5e0f28e7596c5b5fe322b9daf4be3e2920585254c132bd0079d`.
The downstream open-gap and whole-path conclusions remain unverified until
fresh exact-head CI succeeds, including both guarded regression files.

This batch also narrows the imports of `PhysicalGibbsEmbedding` to its
actual algebraic dependencies and makes `TopologicalPhysicalGibbs` import
its domain-specific prerequisite explicitly. The former's unchanged body
passed a strict check and a targeted build. The exposed scalar-inner-product
proof in `BondProductSpectralGap` is repaired using explicit inner-product
identities; its statement is unchanged and its strict check and targeted
build passed. No toolchain or dependency pin changes are included.

## Exact-head follow-up: 2026-10-05 23:12 UTC

CI build job `112012180762` checked head
`20a4a5d9c5ba4c90a7797ae4493cf2fc27ec5e01`. The repaired placement,
periodic-state continuity, and all but four normalization proof sites
compiled. Those four sites incorrectly treated the placement evaluation
identity as definitional equality. This follow-up applies the proved
placement identity explicitly through each boundary coordinate map before
normalizing the concrete fibers; the statements are unchanged. Its source
hash is `5e169cf157c81e9473af9383b7cb7238f388250d35e213b1ee5f05d7be18bf24`.
A focused strict local check is pending; only a fresh complete CI pass can
credit the downstream gap and guarded regressions.

The same CI exposed a missing direct import in
`ExactMPSPhaseGaugeInvariance`: its two uses of `GaugeEquiv.blockTensor`
previously inherited `CPSVBlocking` through the wider physical-Gibbs import
cone. That module now imports the owning declaration file explicitly.
No theorem body or statement changes there. The full local check lacks the
cached `ExactMPSGappedPhase` prerequisite, so it is not reported as passed.
The exact-head full blueprint/browser job `112012180709` did succeed.

At 23:22 UTC, the strict focused prefix containing all four revised
commutation proofs and their helpers passed with no diagnostics. A separate
strict declaration-import check of `GaugeEquiv.blockTensor` also passed.
These focused checks do not replace full-file, downstream, or guarded
regression validation on the next published head.

## Spectator-comparison follow-up: 2026-10-05 23:47 UTC

Build job `112026796959` on `c566b343` compiled the complete repaired
boundary-normalization module in 9.7 seconds. It then reached
`MixedEndpointCoreHamiltonianSpectators`, exposing explicit-coordinate,
singleton-universe, sum-evaluation and orthogonal-membership API errors.
The next repair keeps every public statement unchanged and uses the proved
fiber-placement identities with explicit Euclidean domains. Two analogous
explicit-argument uses in the downstream open-gap files are fixed in the
same batch, using the pinned Mathlib declaration signatures.

The full local spectator check cannot start until its normalization import
artifact is available. No spectator, open-gap, whole-path or guarded-test
pass is claimed at this checkpoint. Fresh exact-head CI remains required.

## Residual spectator repair: 2026-10-06 00:30 UTC

Head `7309a124` reduced the spectator module to four errors in two private
helpers. Their singleton core now has the intended explicit universe, and
the proof evaluates the original conjugation equality directly instead of
introducing a redundant coercion comparison. Both exact helpers pass a
strict focused check with no diagnostics. The public statements are unchanged;
full-file and downstream checks remain pending.

Both standalone gap fixtures also explicitly permit their intentional
guarded `#print` commands, following the repository test convention. All
mathematical examples and expected axiom lists are unchanged, and every other
strict linter/check remains enabled. This avoids a command-style diagnostic
being mistaken for an axiom-report mismatch; it does not weaken axiom guards.

### 2026-10-06 00:50 UTC: final compactness binder

Exact-head CI at `5843332b48c82258a4077205d114d8dc2f258394` compiled
`MixedEndpointCoreHamiltonianSpectators` (35 s), `MixedEndpointOpenGap`
(13 s), and `MixedEndpointRightOpenGap` (7.9 s). The remaining reported
production errors were both consequences of one private eventual-gap
statement: Lean inferred the untyped parameter over the real line rather
than the intended closed interval. The binder is now explicitly
`unitInterval`, matching its proof and the subsequent compactness lemma.
This changes no public theorem statement or hypotheses. The new open-gap
`letI` style warning is also repaired using the prescribed `let`.

The final uniform-path theorem and its strict regression/axiom guards
remain pending a fresh exact-head run; these intermediate compilation
results are not a full-build pass.

### 2026-10-06 01:10 UTC: Knabe threshold coercion

At head `c2d4e74c1141edd13ea93d0406a95c7c1f7e66de`, the interval binder
correction compiled. The remaining production diagnostic is the explicit
natural-to-real cast of the interaction range in the Knabe threshold:
`((2 : ℕ) : ℝ)` was not reduced by the deliberately restricted simplifier.
The threshold proof now includes `Nat.cast_ofNat`, matching the subsequent
Knabe-constant simplification. No theorem statement, premise, bound, or
verification gate changes. Full capstone and guarded-regression success
remain pending the next exact-head run.

An isolated exact threshold example passed the strict Lean options with
exit zero. Its legacy Mathlib import emitted a deprecation warning; the
production file's imports are unchanged. This checks the arithmetic
coercion repair only, not the complete uniform-path module.

### 2026-10-06 01:46 UTC: checked blueprint integration

All eight engineering checks on the proof head `0c51478b` are now green,
including complete blueprint/web/browser job `112058990789`. The two
mathematical leaves now carry six checked statement markers and six checked
proof markers, covering all 378 unique declaration references. No Lean
source or hypothesis changes accompany these markers.

Pinned formatting, all 49 reference/dependency occurrences, strict focused
web and generated HTML checks pass. The marked 28-page PDF was rerendered;
every changed page and all five Tenkz diagrams were visually inspected.
There are no unresolved references, missing glyphs or overfull boxes. One
readable, unclipped underfull proof line remains, with badness 1038.
Local browser execution and a full-volume book PDF are not claimed.

The checked-marker head requires a fresh full CI run. The green proof-head
evidence above does not preempt that final-head validation.

### 2026-10-06 02:30 UTC: boundary-map elaboration performance

Documentation head `4ec52abefce52a00260da9db53f8af7e50a90d5e` passed the
full Lean build, strict regressions/guards and full blueprint/browser. Its
separate unchanged timing gate failed because `MixedEndpointActiveBoundaryTransport`
reached exactly 50 seconds (the previous proof checkpoint was 48 seconds).
Two other modules remained 48-second advisories. This is not recorded as
an all-green final head, and no threshold is changed.

Profiling identified unresolved tuple-projection metavariables in the
linearity proofs of `activeFirstBoundaryMap` and `activeLastBoundaryMap`.
Six explicit tuple-type annotations remove that elaboration work while
preserving every public signature, computational `toFun` body, hypothesis,
import and resource cap. The entire candidate module passes the strict
one-thread warning-as-error check without output artifacts.

Under the same detailed local profiler, the two declarations fell below
its 250-millisecond reporting threshold; the unmodified profile recorded
16.76 and 17.36 seconds, with the latter exhausting the unchanged heartbeat
cap under tracing. That diagnostic failure is kept distinct from the
successful baseline CI build. Candidate imports took 88.1 seconds and total
wall time was 102.871 seconds; these local totals are not CI benchmarks.

Candidate source SHA-256:
`880f1cb33cbbddd4adb6158f34fe243a873b2645cdfaee23a2f45daed2f625b2`.
Source-equivalence, module policies and timing-checker tests pass. The exact
new head still requires full CI, including the unchanged 50-second gate.
The earlier JSON source manifest remains the immutable proof-head inventory.
