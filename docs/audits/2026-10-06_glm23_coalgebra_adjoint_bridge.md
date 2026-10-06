# GLM23 star-coalgebra adjoint bridge

## Source and scope

GLM23, arXiv:2203.12563v3, `REsubmission.tex` lines 1236–1320, works with
representations of C*-weak Hopf algebras. Its cited construction is Molnár et
al., [arXiv:2204.05940v1](https://arxiv.org/pdf/2204.05940v1), Section 4 and
Section 5.5. Definition 5.8 requires a conjugate-linear involution satisfying

\[
\Delta(x^*)=(*\otimes*)\Delta(x).
\]

This coproduct law preserves the order of the factors. Proposition 5.4 and
the discussion following it identify physical adjoints of represented MPOs;
the text on page 37 explicitly extends the identity to arbitrary boundaries.
The dual C*-algebra involution in equation (5.38) also uses the antipode. The
intrinsic involution used below is a different operation and is not claimed
to be that dual C*-algebra involution.

The bridge isolates exactly the standard coalgebra, star-module and
representation data needed for arbitrary-boundary adjoints. It does not
construct a C*-weak Hopf algebra or assume that one has already been built in
TNLean. It does not supply a realization of a particular mixed tensor.
Examples without the required physical star data do not contradict the
paper's C*-weak-Hopf statement.

The representation conventions are explicit in Section 4: a multiplicative
map that does not send the unit to the identity is not a representation
(page 14, preceding Definition 4.2), and the MPO construction chooses an
injective representation of the dual (immediately following Definition
4.2). Thus injectivity and unitality of the virtual representation here are
source hypotheses, including the unit law used for the empty-chain result.

## Mathematical construction

Let `H` be a complex coalgebra with a conjugate-linear involution satisfying
the displayed coproduct law. Let

\[
\phi:H\longrightarrow M_d(\mathbb C),\qquad
\psi:H^*\longrightarrow M_D(\mathbb C)
\]

be a star-preserving linear map and an injective unital algebra
representation of the convolution dual, respectively. For the physical
coefficients `fᵢⱼ(x) = φ(x)ᵢⱼ`, define the actual tensor by `Tᵢⱼ = ψ(fᵢⱼ)`.
No multiplicativity or injectivity of the physical map is required by this
step; those additional properties are available in the source construction.

1. Define `κ(f)(x) = conj(f(x*))` using Mathlib's intrinsic star on
   `WithConv (H →ₗ[ℂ] ℂ)`. Tensor induction and the coproduct law show that
   `κ(fg) = κ(f)κ(g)` in the same order. Involutivity supplies a multiplicative
   equivalence, which preserves the convolution unit. Thus the unit law is
   derived without adding a counit-star premise.
2. Physical star compatibility gives `κ(fᵢⱼ) = fⱼᵢ`. Ordered products of these
   coefficients therefore swap their physical indices without reversing the
   spatial order.
3. For a virtual boundary `X`, the functional
   `ℓₓ(f) = conj(tr(X ψ(κ(f))))` is complex linear. Injectivity of `ψ` lets it
   extend to a linear functional `θ` on all virtual matrices. Nondegeneracy of
   the matrix trace pairing supplies a matrix `Y` with `θ(M) = tr(YM)`.
4. Consequently `tr(Y ψ(f)) = conj(tr(X ψ(κ(f))))` for every dual element `f`.
   Apply this to each ordered coefficient product. The same `Y` gives
   `(Oⁿₓ)† = Oⁿᵧ` simultaneously at all lengths `n ≥ 0`.

The choice of `Y` occurs before the length quantifier. In the empty-word
case, preservation of the unit gives `tr(Y) = conj(tr(X))`.

## Implemented declarations

- `Coalgebra.dualStar_mul`
- `Coalgebra.dualStarMulEquiv`
- `Coalgebra.dualStar_one`
- `MPOTensor.dualCoefficient`
- `MPOTensor.ofDualRepresentation`
- `MPOTensor.star_dualCoefficient`
- `MPOTensor.evalWord_ofDualRepresentation`
- `MPOTensor.star_dualCoefficient_prod`
- `MPOTensor.exists_boundary_trace_dualStar`
- `MPOTensor.exists_adjointBoundary_of_dualRepresentation`
- `MPOTensor.isBoundaryAdjointClosed_of_dualRepresentation`
- `MPOTensor.IsBoundaryCompatible.parentInteractionES_commute_of_dualRepresentation`
- `MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_of_dualRepresentation`

The existing `MPOTensor.IsBoundaryAdjointClosed` definition has been moved
unchanged into `MPS/MPDO/BoundaryAdjointClosed.lean`, so neither sufficient
criterion needs to import the other. Its former defining module imports the
new foundation and retains all its other declarations.

The local canonical-parent corollary uses arbitrary-boundary compatibility
and derived adjoint closure. The periodic corollary additionally retains
`commutingBoundaryAlgebra`, needed for cyclic windows crossing the boundary.
Neither conclusion assumes parent commutation.

## Remaining work outside this bridge

- Construct the full source C*-weak-Hopf representation package.
- Prove that the specific mixed MPO tensor is realized by that package.
- Construct and normalize the canonical integral and its averaging operation.
- Relate the weak-Hopf average to the canonical ambient complementary
  projection, with the support-unit distinction retained.

No assertion here removes these remaining gaps or proves nonzeroness of the
uncompleted weak-Hopf average.

## Verification status

The complete exact-source package passed a one-thread, no-output-artifact
Lean check on 2026-10-06 with `autoImplicit=false`,
`relaxedAutoImplicit=false`, the package's Mathlib linter options,
`maxSynthPendingDepth=3`, and `warningAsError=true`. This included every new
production declaration and the strict regression file. The five logical-dependency
guards passed: the same-order product theorem uses only `propext` and
`Quot.sound`; the guarded unit, boundary, closure, and periodic-parent
results use only the standard trio `propext`, `Classical.choice`, and
`Quot.sound`.

The passing combined check took 77.589 seconds, with 68.4 seconds attributed
to imports and 1.37 seconds to elaboration. Its source SHA256 is
`f4bc38fd66193beb5d0daf72b0976cf0ae7102c36c4c4cb7a1e60ee431da02ef`.
These are local measurements, not CI benchmarks.

The previous combined check elaborated all substantive proofs but failed
strict checking on two automatically included, unused instance groups, one
unused simplifier argument, and an expected list of logical dependencies that unnecessarily
included `Classical.choice`. Those issues were corrected without weakening
any conclusion or adding assumptions, and the clean check reran the entire
package. The earlier isolated helper checks also caught a namespace
resolution issue and a deprecated tensor-induction API; neither remains.

An independent source-only review found no mathematical or
source-faithfulness blocker in the orientation, functional extension,
quantifier order, empty-length case, or periodic centralizer. Its API review
identified the existing `Matrix.exists_trace_representation` helper, which
supplies the nondegenerate trace-pairing step directly.

The existing adjoint-closure predicate was checked source-equivalent after
making its previously section-bound physical dimension explicit. The
forbidden-token, numbered-file, oversized-file, and whitespace checks passed.
No new proof holes, axioms, native evaluation, or conclusion premises occur.

Separate-module builds and exact-head CI were integration checks at this
checkpoint; their subsequent success is recorded below.
The local import and documentation integration is recorded below. No remote publication or shared cache mutation
was performed by this package.

## Local integration and documentation checks

The package is integrated through four generated imports in the algebra,
operator-tensor, and symmetry aggregators, one additive chapter-30 include,
and one entry in the existing strict boundary-parent regression loop.
The loop retains its original linter and warning-as-error flags.
All production and test files retain the exact bytes of the passing combined
check. Moving `MPOTensor.IsBoundaryAdjointClosed` preserves its fully qualified
name, implicit physical and bond dimensions, predicate body, and existing
blueprint owner. No consuming declaration is renamed.

The five new blueprint entries own thirteen new public declarations exactly
once. Their statements and proofs are now checked on the exact-tree CI evidence
recorded below. The relocated predicate retains its single existing owner.
The new text distinguishes the same-order involution from the antipode-bearing
dual involution and cites the precise local and periodic parent criteria;
the periodic tensor-letter centralizer is retained explicitly.

The official [version-1 PDF](https://arxiv.org/pdf/2204.05940v1) was independently
checked during integration: page 14 states the unital representation convention
and chooses an injective virtual representation; page 37 gives Definition 5.8,
the antipode-dependent equation (5.38), and the arbitrary-boundary adjoint
statement following Proposition 5.4.

Passed local checks:

- Generated import consistency and its nine regression tests.
- Full blueprint/source synchronization, including pinned QICLean source,
  with no missing references or duplicate owners; reverse coverage of the
  changed production declarations; declaration-scanner regressions.
- Reader-facing prose, forbidden-token, numbered-file, oversized-file, and
  whitespace checks; pinned latexindent 3.24.7 is idempotent on the new leaf
  and leaves the modified chapter router unchanged.
- Strict texra-blueprint 0.3.8 focused web generation, using the unchanged
  production renderer and local copies of its supporting files.
- An eight-page focused PDF containing the new leaf and twenty exact
  reference-closed statement excerpts. All pages were visually inspected;
  the final TeX log has no warnings, unresolved references, or over/underfull
  boxes. The four inherited context diagrams pass the source-linked native
  Tenkz audit with no hard errors or advisories. The new leaf adds no diagram.

Generated HTML source checks also pass, with thirteen new declaration links
and four inherited Tenkz SVGs. Browser/MathJax validation is **not passed**:
the first invocation ended in an automatic permission-review timeout; its
single ordinary retry failed before launch because the expected Playwright
Chromium headless-shell executable was absent. The production assertions and
fail-closed CI browser gate are unchanged. No browser installation or
sandbox/network workaround was attempted.

Separate-module builds, browser validation, and exact-head CI were
outstanding at this local checkpoint. The subsequent exact-tree CI passed
all engineering checks, including the unchanged fail-closed browser gate. The integration performed no Lean build, elaboration, shared
Lean-cache mutation, or remote publication.

## Exact-tree CI validation and checked owners, 2026-10-06

[PR #8717](https://github.com/LionSR/TNLean/pull/8717) passed all engineering
checks at head `71f35e3724b284ef41994485b3f9874c88db181e`. Its tested merge
`8a0cd3e22aa0faec53b6a6e9f6615b00b0f33a90` has the same tree,
`0d21b41da4bae0090e8f1d76a38bd3b11430d456`. The immutable
[CI run](https://github.com/LionSR/TNLean/actions/runs/37410841184) includes
the passing [build](https://github.com/LionSR/TNLean/actions/runs/37410841184/job/112098728483),
[blueprint](https://github.com/LionSR/TNLean/actions/runs/37410841184/job/112098728486),
and [timing](https://github.com/LionSR/TNLean/actions/runs/37410841184/job/112102251514)
jobs. It validates all four new modules (336 lines, including the relocated
predicate) and all five regression guards. The four new module times were
2.5, 3.2, 5.8, and 4.1 seconds.

On that evidence, the five new statements and their four proofs now carry
checked markers, covering all thirteen new declaration owners. Every
production and regression byte is preserved. The same-order involution,
length-independent boundary, empty-chain identity, and periodic centralizer
condition retain their precise scopes. No full weak-Hopf package, mixed
realization, integral, or classification conclusion is added. Fresh local
rendering is recorded separately; the earlier local browser limitations
remain historical local limitations and are not reported as local passes.

## Checked-marker rendering verification, 2026-10-06

The exact changed leaves were copied into a focused, reference-closed fixture
with the unchanged production macros and renderer. Tool versions were
texra-blueprint 0.3.8 (commit `65434add8b88bc6a22c701521baa3abec2369341`),
plasTeX 3.1, and the pinned Tenkz commit
`08a6493f3605dcf2ca5b512823ccb2698dfc027b`. TeX formats were regenerated
from installed official sources in a separate workspace tree; no Lean
build, elaboration, or Lean-cache mutation was performed.

The eight-page XeLaTeX PDF includes the new leaf and twenty exact context
excerpts. All mathematical pages and diagrams were visually inspected;
the new leaf has no clipping or box warnings, and all references resolve.
An unchanged context excerpt, the word-evaluation definition, has one
3.25276pt overfull line in this fixture. Strict web generation and
generated-source checks pass: six HTML files, thirteen new declaration
links, five checked statements, four checked proofs, and four inherited
SVGs. The source-linked native audit of those four context pictures has
zero hard or advisory findings. The new leaf adds no diagram.

Full blueprint/source synchronization with the pinned QICLean source has
no missing references, stale declaration-list entries, or duplicate owners.
Reverse coverage, reader-facing prose, and whitespace checks pass. All
production, regression, workflow, router, and dependency bytes are unchanged
from the exact tested public head.

The web renderer used its existing XeLaTeX/PDF/pdftocairo fallback because
`dvisvgm` is absent. Local browser layout validation is **not passed**: the
ordinary Playwright launch failed because its Chromium headless-shell
executable is absent. No browser/security workaround or weakening of the
fail-closed CI checks was made. LuaLaTeX was also unavailable locally because
the installed tree lacks `luaotfload-main`; the successful PDF route was
XeLaTeX. These focused local results do not claim a fresh full-volume build
or a fresh exact-head CI run for the documentation-only commit.

Artifact SHA-256 values:

- Focused PDF: `0473c3284b37ad2c4cd7e76c81b8e50ebb8fd50e283a28e296424945366346a0`.
- Generated chapter HTML: `cd5cf6bf7bbc9a3c50b71919b1fbb201ed8be6786c30e26e852b176ceec4b3ee`.
- `ch30_mpo_coalgebra_adjoint_boundary.tex`: `5d8f8bd6c5bd4cd333d0d6d1cb745ebbe487834c8aa66fcc823753979f348b03`.
