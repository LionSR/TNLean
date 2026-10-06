# Noncommuting periodic gap transport under a physical isometry

## Scope and assumptions

Let `E : Matrix (Fin m) (Fin d) ℂ` satisfy `Eᴴ * E = 1`, let `A` be an
arbitrary positive semidefinite two-site interaction, and let `N ≥ 2`.
Write `W = E^{⊗N}`, `T = E^{⊗2}`, and

- `A' = T A Tᴴ + I − T Tᴴ`;
- `H` and `H'` for the corresponding periodic sums.

The new source proves

1. `ker H' = W (ker H)`;
2. a lower norm or quadratic-form gap `δ` for `H` gives the lower bound
   `min δ 1` for `H'`;
3. spectral separation above zero transfers with the same lower bound.

The local interaction need not be a projection, and neither family of
translated interaction terms is assumed to commute. No injectivity,
frustration-freeness, nonzero ground vector, or nonempty physical alphabet is
assumed. The spectral statement therefore does not assert that zero occurs
in the spectrum. The norm-gap version assumes `0 ≤ δ`; the quadratic and
spectral versions need no sign assumption on `δ`.

These are physical-space enlargement lemmas for arXiv:2203.12563, Section 5,
and arXiv:1010.3732, Section II.F.2. They do not complete common MPO covariance
or symmetric-phase classification.

## Mathematical argument

The auxiliary interaction `B = I − T Tᴴ` is the extension of the zero
interaction. Its translates are complementary products of the same one-site
range projection `E Eᴴ`. They commute because, at every position, the two
one-site factors are either that same matrix or the identity. The proof uses
the existing finite Kronecker formula for each translated tensor-square
operator, including the two-site ring.

The existing commuting-projection kernel theorem is applied only to `B`.
The original zero Hamiltonian has the whole space as kernel, so the auxiliary
penalty Hamiltonian `P = Σ B_i` has `ker P = ran W`. Its commuting-projection
gap is at least one. Consequently `⟨P y,y⟩ ≥ ‖y‖²` whenever `y ⟂ ran W`.
Positivity of `A` gives `B ≤ A'` and hence `P ≤ H'`. This derives
`⟨H' y,y⟩ ≥ ‖y‖²` off the included chain, without any commutation claim for
`A'`.

The existing whole-chain identity `H' W = W H` handles the included space.
The new abstract isometry lemma decomposes `v = U U†v + (v − U U†v)`.
The second summand is orthogonal to the image. The strict inactive bound
excludes additional zero modes. Symmetry makes the two energy cross terms
zero, and the Pythagorean identity combines the two lower bounds with their
minimum. For positive operators the existing norm-to-energy gap theorem
supplies the active quadratic bound; Cauchy–Schwarz returns a norm bound.

## Source map

- `TNLean/Algebra/IsometricGapTransfer.lean`: reusable exact kernel,
  quadratic-form and norm-gap transport for an isometric intertwiner.
- `TNLean/MPS/MPDO/PhysicalSupportProductTransport.lean`:
  `embed_twoSiteSectorProjection_commute` proves the auxiliary support
  commutation without projection or Hermiticity assumptions.
- `TNLean/MPS/Symmetry/PhysicalIsometricGapTransport.lean`: derives all
  physical hypotheses and gives the noncommuting transport theorems.
- `TNLeanTest/PhysicalIsometricGapTransport.lean`: arbitrary-positive
  interaction, two-site-ring, uniform-in-length and spectral regressions;
  standard axiom guards for the principal statements.

The generated Algebra and Symmetry import aggregators include the new
modules. Existing public theorem statements remain unchanged.

## Validation status

This is a source-only implementation, based on
`f07abae7b3ad91f78ef636423a0b6dc87fb1ca87` in an isolated worktree.

Completed source checks:

- `git diff --check`;
- import aggregator generation and `--check`;
- tactic-pattern scan;
- scan of the new proof modules for prohibited proof-integrity tokens;
- line-length check of the new modules and regression.

No Lean elaboration, Lake build, cache operation, or axiom-guard execution has
been performed by this worker. The axiom guards are expectations until the
owning task validates them. Blueprint coverage and CI routing are deferred
until the source has passed that validation. No remote publication or merge
has been performed.

## Arbitrary physical alphabets: actual mixed-path extension

Three additional source modules remove the square-physical-alphabet restriction
from the concrete GLM mixed-path gap, using only one-site injectivity of
`Aₚ : MPSTensor dₚ Dₚ` and positive `Dₚ`:

- `InteractionMatrixRepresentation` identifies general Euclidean periodic sums
  with the existing embedded-matrix sums, without projection or commutation inputs.
- `ArbitraryPhysicalMixedInterpolation` sets `Bₚ = polarPosTensor Aₚ`, derives
  injectivity from exact polar reconstruction, and includes the actual mixed
  tensor through `J = commonFixedPointInclusion`. Its periodic endpoint vectors
  are exactly those of `Eₚ Aₚ`; `E₀`, `E₁` are the existing full isometries with
  orthogonal images. The endpoint letters can retain absorbing off-diagonal
  blocks, so no equality of raw tensors of different bond dimensions is asserted.
- `ArbitraryPhysicalMixedPathGap` derives the continuous positive enlarged
  interaction, its exact nonzero MPS ground line, and one lower norm-gap bound
  `min(δ,1) > 0`, uniform over the closed interval and every `N ≥ 2`. The support
  gap comes from `MixedEndpointUniformPathGap`; it is not a capstone hypothesis.

The construction follows `REsubmission.tex`, lines 1584–1601 and 1687–1692.
Canonical-parent equality is asserted only for interior parameters. At the
endpoints the actual limiting interaction uses the extended support; the known
periodic comparison is `H′ ≤ K ≤ 3 H′`, not equality. Canonical endpoint caps,
common MPO covariance, and degenerate phase classification remain outside this
extension. Existing helpers, proof modules, blueprint, routers and workflows
were not edited by the capstone worker.

`TNLeanTest/ArbitraryPhysicalMixedPathGap.lean` states strict arbitrary-alphabet,
continuity, exact endpoint, nonzero ground-line, two-site-ring and uniform-gap
regressions, with standard axiom guards. Only source-level checks were run for
this extension. Its elaboration, upstream whole-path validation and execution
of these axiom guards remain the owning task's responsibility.

## Import isolation and checked algebra

A separate mathematical review found no unresolved signature-level flaw in the
five production modules. The source anchors for MPS injectivity and the interior
support identity have been corrected to lines 1691 and 1692, respectively.
This review is not a compiler or axiom-audit claim.

The generic physical-window algebra no longer imports the domain-specific
`TopologicalGibbsHamiltonian` module. `PhysicalGibbsEmbedding` instead imports
`CommutingForm`, `SitewisePhysicalMatrix`, and Mathlib's matrix exponential API.
Its unchanged body passed strict standalone elaboration and the targeted Lake
build. `TopologicalPhysicalGibbs` now imports its topological dependency directly.
A read-only audit of all ten direct consumers found no other missing domain
import; the full downstream build remains required.

The reduced import graph exposed a fragile broad simplification in
`BondProductSpectralGap.spectrum_separated_of_quadratic_gap`. The proof now
expands the three complex inner-product scalar factors explicitly before its
final scalar simplification. Its statement is unchanged, and the exact revised
file passes strict standalone elaboration. This avoids relying on unrelated
transitive simplification rules.

Static TNLean-only reachability for `PhysicalIsometricGapTransport` decreases
from 360 modules to 266. These counts are not timing measurements. No dependency
revision, toolchain, mathematical hypothesis, or theorem statement is changed
by this import cleanup.

## Bridge elaboration repair, 2026-10-05 22:40 UTC

The first targeted check compiled the public prerequisites and found seven
elaboration errors in `PhysicalIsometricGapTransport`. A completed strict
follow-up eliminated those errors and exposed three private-helper instance
conversion mismatches. The current candidate supplies the caller's
`DecidableEq` instance to that helper instead of creating a separate
classical instance. All nine public theorem signatures remain unchanged.
Its SHA-256 is
`f281cad9d08d06d7274cca4a26bed02e36a62ef29940bc2ded7af2ff5c66fee2`.
The subsequent probe lost its executor connection without a terminal result;
a fresh no-artifact check is pending. No final bridge or regression pass is
claimed from the empty interrupted log.

## Checked physical bridge: 2026-10-06 00:07 UTC

The corrected `PhysicalIsometricGapTransport` source passed its full strict
check and subsequent targeted artifact build. `InteractionMatrixRepresentation`
also compiled, alongside the previously checked `IsometricGapTransfer`.
The standalone physical-isometry regression then passed with all three
standard-axiom guards unchanged. Its only fixture adjustment documents that
this test intentionally uses guarded `#print` commands and disables only
that command-style warning; every mathematical example, expected axiom list,
and other strict option is retained. The checked regression SHA-256 is
`031a0aaf937070bd5fa9ed44ca7e803e7a84f5bb8d0f8b7ab4cb5f69b8809108`.
The analogous arbitrary-path fixture receives the same command-style setting.

Three of the five new production modules are now compiled. The actual
arbitrary-physical interpolation and final path-gap wrapper still await the
whole-gap dependency chain and their own complete checks. No full-package
or full-classification claim follows from this bridge checkpoint.

## Draft integration: 2026-10-06 01:53 UTC

The draft is based on PR #8699 documentation head
`4ec52abefce52a00260da9db53f8af7e50a90d5e`. Its Lean sources are identical
to proof head `0c51478b87ef711dc7e339cfa5a166456f0a20c5`, which passed
all eight engineering checks, including the full uniform-path proof and
three guarded axioms. The latest documentation head has its own fresh
CI run; the prior proof pass is kept separate.

This extension has five new production modules (947 lines), two strict
regression files and thirty-eight blueprint declaration owners. Three
production modules and the physical-isometry regression's three guards
passed exact local checks. `ArbitraryPhysicalMixedInterpolation` and
`ArbitraryPhysicalMixedPathGap`, together with the latter regression's six
guards, remain pending. Independent source/API review found no mathematical
blocker, including exact endpoint vectors and the two-site ring; it is not
a replacement for elaboration. No new checked markers are added.

Before publication, the combined chapter browser expectation was reconciled
to include both two-picture rows: the inherited mixed-state interpolation
and the new isometry transport. The native isometry test is also added to
the existing blueprint workflow. All existing browser failure gates and
unrelated workflow contents are preserved. No full-paper classification
or common MPO covariance conclusion is asserted.
