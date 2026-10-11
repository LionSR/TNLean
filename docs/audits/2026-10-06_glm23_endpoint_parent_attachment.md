# GLM23 canonical-parent attachment audit

## Source and scope

Source: `Papers/2203.12563/REsubmission.tex`, arXiv:2203.12563v3.
The definition labelled `defphase` at lines 1255–1265 requires a continuous,
gapped periodic Hamiltonian path and a fixed injective MPO representation
with the prescribed restrictions and fusion properties. Lines 1328–1331
explain affine comparison with an exact-MPS parent. Lines 1584–1601 construct
the occupied-support mixed tensor; lines 1690–1692 distinguish the extended
limiting support from the canonical support at a singular endpoint.

This package addresses only the attachment to the two canonical parents.
Original physical dimensions remain arbitrary; endpoint tensors are one-site
injective and bond dimensions are positive. No MPO symmetry conclusion or
classification statement is asserted. The degenerate, block-injective case
is outside this package.

The base is local commit `908e7dd0028a93bab88ac8bfbe99f614f93f7eb5`, whose
corresponding arbitrary-physical package passed all eight remote checks at
`0d6654d1`, including its repaired regression and nine guards, as verified in run 37407799655. That validates the base, not the new attachment source.

## Current validation status

The complete production build passed in [CI run 37424899108, build job
112142631279](https://github.com/LionSR/TNLean/actions/runs/37424899108/job/112142631279)
for public head `210e1d8300d2bf585a34511fc4eb2bf6a394ee1b`, tested as merge
`98c696deae14aaa7330203aabc9bde8f2a7a2728`. Both have tree
`7f4498ab78ff201416e31d63b97945f32fe86896`. The attachment production module
built in 11 seconds at 2026-10-06 06:55:40 UTC, without production errors.
Its checked Git blob is `91babeaf7722ef8710c8a88c5ebe0add99355ab9` and SHA-256
is `9c4a67d14d8a8d4400a6e49c94ec70db5d67fd24271c3ad442476f8a8de691e8`.
The author worktree's production file matches both hashes exactly and is
unchanged by the present test/documentation checkpoint.

The strict regression run failed only at its two deprecated conditional
lemmas: `if_false` on line 66 and `if_true` on line 76, reported at
2026-10-06 07:01:36 UTC. All eight guarded axiom commands were processed
without reported guard errors; their expectations remain exactly
`propext`, `Classical.choice`, and `Quot.sound`. This is not a successful
whole-file regression pass. The present repair changes only those two
lemma names to the compiler-recommended `ite_false` and `ite_true`.
A strict pass of the repaired file remains pending.

The 15 production declaration owners in the isolated attachment blueprint
now carry checked statement markers, and both production-backed proof
blocks carry checked proof markers. This promotion records the successful
production build, not success of the repaired regression.
The local canonical warmup of the earlier head is not used as pass evidence.

## Dependency and coverage findings

1. `MixedEndpointProjectorComparison` proves local order at zero by padding
   each endpoint boundary into the corresponding virtual corner.
   `MixedEndpointRightComparison` proves the order at one by sector exchange.
2. `ArbitraryPhysicalMixedInterpolation` identifies the polar-support
   inclusions with the full isometric embeddings of the original tensors.
   Neither endpoint tensor is assumed to have square physical dimension.
3. `IsometricParentInteraction` transports local order and identifies the
   canonical parent after physical embedding, including the unused-space
   unit penalty.
4. `ArbitraryPhysicalMixedPathGap` supplies positivity, the exact nonzero
   periodic MPS line, and one positive uniform gap for the actual mixed path.
5. `CanonicalInjectiveGroundPath` identifies the true embedded canonical
   parent's periodic ground line. The exact endpoint-vector identities give
   the common kernel; this is proved, not supplied as a hypothesis.
6. `CommonPhysicalCanonicalGroundPath` and QICLean `PositiveGapTransfer`
   preserve that kernel and norm gap under ordered affine interpolation.

The proposed theorem chain therefore proves both actual local inequalities,
continuous affine attachments with exact end values, positivity, norm at most
one, exact original embedded MPS ground lines, one-dimensional kernels, and
one shared positive gap for all attachment parameters and all periodic lengths
at least two. The gap is inherited without an additional numerical loss.

There is no identification of the limiting local projector with the canonical
projector. Their local support dimensions may differ. The equality used in
the gap argument concerns the full periodic kernels.

## Scouting and proof reuse

Read the repository instructions, shared Lean conventions, local addenda,
blueprint style rules, cache policy, and promoted tactic ledger. Inspected
Mathlib's positive matrix/linear-map equivalence and C-star operator-norm
monotonicity, along with the existing kernel interpolation and QICLean gap
transfer. The new generic norm-gap comparison reuses these results; it does
not repeat an eigenvector or quadratic-form argument. The two polar endpoint
rewrites are recorded below the promotion threshold in the tactic ledger.

## Original recovery validation record

- `TNLeanTest/ArbitraryPhysicalEndpointAttachment.lean` covers both exact
  local endpoint matrices, both attachment ends, continuity, positivity,
  operator norm, the smallest two-site ring, exact first/second original
  embedded MPS vectors, and a gap uniform in both endpoint choice and length.
- Eight guarded axiom audits are specified, with exactly the standard
  `propext`, `Classical.choice`, and `Quot.sound` expectations.
- `git diff --check` and the proof-integrity source scan passed.
- The repository tactic-pattern scan ran; no new fourth repetition was
  introduced. No custom tactic is needed.
- The isolated mathematical blueprint leaf rendered as a two-page XeLaTeX
  PDF with no overfull/underfull boxes or warnings on its second pass. Both
  pages were visually inspected. This algebraic proof adds no tensor diagram.
- New Lean module compilation, regression guards, compiler-based declaration
  synchronization, full blueprint validation, and remote CI are pending.
  Source-level synchronization found every changed declaration covered and
  every new reference resolved; 523 repository-wide references lacked the pinned QICLean source
  during that earlier check. The new leaf carries no checked markers.
- An independent read-only mathematical/source review found no mathematical
  blocker or definite dependency-signature mismatch. It requested the citation
  and blueprint-style corrections included with this recovery.
- An exact-body generic-only probe was started in the authorized serial slot,
  but the executor was replaced before any terminal result was obtained. No
  probe success is claimed. The new module and its eight guards have not run.
- A source-preserving local probe would initially require 47 production
  bodies (10,679 lines) because existing imported modules lack local artifacts.
  No canonical cache was written. Exact-head CI is preferred to a giant inlined probe.

Two inherited comments in `ch30_mpo_isometric_gap_transport.tex` were corrected
after its exact-head validation: they no longer describe its already
checked 38 declaration owners as source-only. No inherited mathematical body,
shared router, workflow, MPU, or PEPS file was changed.

## Original recovery remaining work

The source was committed as `d29dc992da0709879655769b97eed657ac6fdbc7` in the
previous executor. That Git object is unavailable after executor replacement.
The two new Lean files were recovered from exact authoring payloads and match
their previously recorded SHA256 digests. The blueprint and audit were
replayed from their exact authoring payloads; original PDF bytes and probe
logs were not recovered. The current corrected blueprint has not yet been
rendered. Register the new production import, regression in the explicit CI
loop, and isolated blueprint leaf during integration.

Validate the new source in separate module boundaries with the pinned Lean
and Mathlib versions, strict package options, and all eight guards. Then
promote only successfully checked blueprint owners. The fixed-MPO covariance,
fusion representation, and degenerate-ground-space extension remain separate
mathematical requirements, regardless of the attachment validation outcome.

## Recovered draft integration

The hash-verified source has been restored against public parent commit
`0d6654d1ce36244365bef972d456eba2f9eb696d`. The production change since recovery
is a source-citation correction; the mathematical body is unchanged. The
regression retains its original pre-loss SHA-256. Generated imports, the
existing strict regression loop and the chapter router now include the new
package. The exact pinned QICLean source was restored for global reference
checking; global and reverse blueprint synchronization pass. Source/prose and
whitespace checks pass. No local compiler or post-recovery PDF/browser pass is
claimed. The draft is checkpointed before further long validation; full
separate-module CI and the eight strict guards remain required.

## First draft CI repair

Head `226de1565e7185cc690acd521db61fb03b9670e0` reached the full production
build and reported two endpoint-choice rewrite errors plus a finrank
elaboration timeout. Rewriting a Boolean equality changed a dependent
Decidable argument; the candidate instead uses the definitionally reduced endpoint
goal before applying the already-proved canonical kernel identity. The
finrank argument now uses the derived equality of submodules through
`congrArg`, with an explicit unit-interval coercion equality, rather than a
large dependent goal rewrite. Statements, assumptions and resource limits
are unchanged. The blueprint failure was pinned-formatting drift and is
also repaired. Full exact-head validation is required for this batch; no
new local production pass is claimed.

A small generic Mathlib check confirmed the typed finrank transport through
`congrArg`. Its initial closed-Boolean simp test reported no progress because
the expression was already definitionally reduced; the actual endpoint proof
therefore uses explicit reduced goals with `change`. This targeted check is
not a compilation of the full repaired attachment module.


## Endpoint tensor and coercion repair

The subsequent CI diagnostics for PR #8718 identified three remaining
elaboration failures in `ArbitraryPhysicalEndpointAttachment`: the two
canonical-kernel rewrites inferred tensors as expanded Kraus sums instead of
`rotatePhysical`, and the finrank coercion rewrite did not match the
coercion of the Boolean-selected unit-interval endpoint.

The endpoint branches now first establish injectivity with the exact
`rotatePhysical` tensor type. Each canonical ground-space theorem is then
instantiated with that tensor explicitly, and the resulting equalities are
composed by transitivity. This avoids relying on the rewrite tactic to
unfold the tensor constructor while finding a kernel expression.

The finrank proof still transports dimension through the already-derived
kernel equality. Its final, typed dimension consequence is established by
splitting the Boolean endpoint choice, so there is no conditional-coercion
rewrite. The public theorem statements, hypotheses, regression file, eight
axiom guards, and resource limits are unchanged.

At this checkpoint only source inspection, statement/test preservation,
proof-integrity scanning and whitespace checking have been performed for
this repair. No Lean or Lake process was started by this worker while the
root's canonical warmup was active. A separate-module production build and
the unchanged strict regression with all eight guards remain required;
no successful compilation or CI outcome is claimed for this repair yet.

A follow-up source review removed the closed-Boolean simp lists from both
kernel branches, including the deprecated `if_true` lemma. Each selected
ground-line equality is instead reduced definitionally with an explicit
`change` to the real endpoint zero or one before the endpoint-vector
identity is used. This adds no hypotheses or resource overrides, and the
compilation status remains pending.


## Explicit MPV transport repair after the next CI run

The next CI diagnostics on public head `decaced` reported that simp still
failed to reconcile the embedded tensor's injectivity statement, and that
the endpoint-MPV simplification left the chain length unconstrained and the
Hilbert-space conversion mismatched. The finrank repair passed this stage.

Embedded injectivity is now supplied by direct application of the existing
Kraus-isometry theorem, matching the already-elaborating later ground-space
proof. Both endpoint MPV identities explicitly specify the current chain
length `N`. Their equalities are transported through the typed map
`v ↦ span {WithLp.toLp 2 v}` by `congrArg`, then composed with the two
explicitly typed ground-line equalities. Neither branch relies on a nested
simp rewrite of a periodic vector. The two single-goal tactic combinators
in the local-norm proof were replaced by sequential tactics.

All public signatures, the previously passing finrank proof, regression
statements, eight axiom guards and resource limits are unchanged. Static
signature/test preservation, proof-integrity and whitespace checks pass.
This worker has not run Lean or Lake while the root's canonical build is
warming; compilation and the unchanged guarded regression remain pending
for this latest repair. No passing result for this commit is claimed.


## Production-backed checkpoint and strict-regression correction

The production theorem statements and proof bodies are byte-identical to
the CI-validated file. The only Lean-file changes in this checkpoint are
the two deprecated simp-lemma names in the regression. The regression's
mathematical statements, all eight guard commands and expectations, and
all resource limits are unchanged. No new axioms or proof placeholders
are introduced. The earlier pending-compilation paragraphs above are
historical checkpoints, superseded by the exact production evidence in
“Current validation status”.

No Lean or Lake process was started by this worker while the root's
canonical endpoint warmup remained active. The repaired strict regression
must still pass as a whole before that gate can be reported successful.


The exact current blueprint leaf was formatted with pinned latexindent
3.24.7 and rendered in isolation using the repository's common/print macros
and bibliography under XeLaTeX. The final render has two content pages and
one bibliography page; all three page images were inspected. There are no
final-pass LaTeX/BibTeX warnings, overfull/underfull boxes or missing-glyph
reports, and no clipping or illegible formulas was observed. Rendering
required the existing writable TeX cache and explicit installed TeX/font
search paths; no Lean cache was touched.

The pinned single-leaf formatting check passed. The source-level global
blueprint/Lean synchronization and reverse coverage check also passed with
no missing, stale or unresolved declaration references. This is a source
checker result, not a new Lean compiler or repaired-regression pass.
