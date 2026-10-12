# Joint ordered-pair core operator identification

Source: GLM23v3, `Papers/2203.12563/REsubmission.tex`, lines 1695–1777.
Base: public #8724 head `7b6bbfab322bb2dbd2571606d4f4f11db060ceac`.
This leaf begins after the actual cropped-edge normalization package.

## Coverage audit and dependency plan

The base proves exact normalization onto the ranges of the explicit maps
`jointEndpointFirstEdgeCoreMap` and `jointEndpointLastEdgeCoreMap`, for arbitrary
exterior dimensions. It does not prove an operator identity for a chain sum.
The existing `DependentSpectatorGapEquivalence` theorem accepts an arbitrary
common core family but does not supply that family or the physical operator
identification. The single-block `MixedEndpointCoreHamiltonianSpectators`
contains the analogous coordinate argument, but fixes the physical alphabet
and omits the dependent label fibers; it cannot provide the joint claim.

This package uses those dependencies in this order:

1. Orthogonal-projection uniqueness derives dependent spectator projection
   identities from actual kernel fibers.
2. Explicit original-tensor coefficient maps derive the first and last core
   support fibers of the existing Φ_L and Φ_R ranges.
3. Explicit chain permutations retain every ordered pair `(x,y)` and separate
   the exterior registers from `Fin (D₀ x) × Cfg d₀ (n+1) × Fin (D₀ y)`.
4. First and last terms place the existing Φ_L and Φ_R support-complement
   projectors. The bulk places the original joint canonical open parent
   Hamiltonian on all `n+1` middle physical sites.
5. Termwise evaluation derives the normalized sum's isometric equality with
   the dependent spectator extension of the explicit common core family.
6. The proved isometric conjugacies and the existing dependent spectator
   equivalence identify the same nonnegative norm gaps for the canonical and
   enlarged normalized sums, when the first endpoint bond dimensions are positive.

## Mathematical scope

The chain has `n+1` middle sites and total length `n+3`. Its first and last
edges are therefore distinct. At `n=0`, an explicit theorem proves that the
middle term vanishes, leaving exactly the two edges of a three-site chain.
No definition or theorem applies this split to a two-site chain.

The arbitrary exterior dimensions `E_x,F_y` specialize to canonical
`D₀ x,D₀ y` and enlarged `D₀ x+D₁ x,D₀ y+D₁ y`. The same core operator is
used in both cases. The operator identity requires no positivity of these
dimensions, no injectivity, and no nonempty label set. All ordered pairs are
retained, including distinct labels. The separate existing gap equivalence
requires nonempty exterior fibers when transferring a bound in both
directions; this package does not silently strengthen the identity to impose
that assumption.

The core left support is the range of `u ↦ ((A₀ x i) *ᵥ u) b`. The reflected
right support is the range of `u ↦ (u ᵥ* (A₀ y i)) c`. Their orthogonal
complement projections supply the two core edge terms. The bulk is literally
`openParentHamiltonianES (toTensorFromBlocks (fun _ ↦ 1) A₀) 2 (n+1)`.
This preserves the original joint interaction and the entire physical
alphabet, including unused directions. It is never replaced by an interaction
for one boundary block, by a minimum of individual block gaps, or by
normalization of interior tensors.

## Remaining physical obligations

`jointEndpointNormalizedSum` is the sum of the normalized support constraints
specified above. It is not defined as the desired dependent operator, and
its equality to that operator is proved from actual range fibers.

Identifying this sum with a boundary-only deformation of the compressed
actual physical Hamiltonian still requires the separately owned reducing
range and compressed-kernel bridge. Extending the active estimate to all
physical sectors still requires the inactive-sector lower bound and
boundary norm estimates. None is assumed or claimed here. No uniform-gap
claim is made.

## Historical isolated validation

The checks and focused render in this section precede the recovery and public
CI described below. Their original source hashes and limitations are retained
in the companion JSON.

Fourteen isolated individual module/regression checks pass with the pinned
Lean binary, exact module roots, one thread, all package strictness and linter
options, warnings as errors, and a sixty-second bound per module. This includes
all three new production leaves, the moved generic spectator leaf, both gap
leaves, the joint specialization, all five exact edge prerequisites, and both
regression files. All five new foundation guards and both existing dependent
gap guards pass, expecting exactly `propext`, `Classical.choice`, `Quot.sound`.

The modified heavy `SpectatorTransport` re-export module alone reached the
wall bound in 60.6 seconds with no diagnostic. That isolated check was
inconclusive; no output was promoted. It was absent from the checked core
target closure. Blueprint markers were withheld at this stage pending the
modified consumer and coherent package checks. This historical validation
did not establish a whole-package or public CI pass.

The validation directory has real directories and per-file read-only symlinks
to unchanged canonical artifacts. Every rebuilt module and the stale old
`SpectatorTransport` artifact are excluded. Compiler outputs go to temporary
paths and are atomically promoted only after exit zero. Source hashes,
manifest/toolchain/compiler hashes, direct imports and command flags are
recorded per module. The complete checked target closure has 4,650 modules
and contains neither the stale re-export artifact nor `C3Threshold`. No Lake,
Mathlib rebuild, canonical cache write, or publication was performed here.

The regression file includes physically overlapping scalar labels in a
three-letter alphabet, an off-diagonal `(0,1)` core, different left/right
exterior multiplicities, empty labels, zero exterior fibers, zero virtual
cores, a zero physical alphabet, and the three-site lower threshold.
It also applies the derived gap-equivalence theorem directly to the two
concrete normalized sums. Five guards check the standard three foundations.

Static checks pass for forbidden proof tokens, generated imports, changed
noncomment line lengths, file size, reader-facing prose, and the pinned
latexindent 3.24.7 byte comparison. The global blueprint/source checker uses
manifest-identical QICLean sources from the canonical validation checkout,
without creating a source-worktree Lake cache. It finds all 48 new public
declarations, with no missing reverse coverage or duplicate owners.

The focused PDF has seven pages. The three pages containing this new leaf
(physical pages 3–5) were visually inspected after the final equation-anchor
and line-wrap repairs; the target leaf has no overflow or missing-reference
warnings. A separately extracted, unchanged contextual definition has one
7.55-point overfull line, recorded in the validation report; no claim of a
warning-free whole-book build is made. The focused HTML contains all 16
new labels, with no broken local anchors, duplicate IDs, or rendering
sentinels. Browser visual inspection and a whole-book build were not run.
The coordinate and operator formulas carry this leaf; no new tensor diagram
was needed. The companion JSON records source hashes and validation scope.

## Subsequent checked package

[CI run 37468535974](https://github.com/LionSR/TNLean/actions/runs/37468535974)
passed on tested merge `3eee7cf359b6cfd1fbe62e585b02a8bccb1fc7ad`, whose tree
`843e233eb40d2c59e080e57e64315301fe1ec857` is identical to public draft #8725
head `d18d1a360223039dc366e1dc0c5ba43402065888` and the recovered authored
commit `3b4ff7c1fe616fcb9be7325675e66e1635246ec4`.
The full build, strict registered regressions, compiled declaration checks,
formatting, timing, and complete blueprint web checks pass. In particular,
the heavy re-export compiled in 32 seconds, resolving the earlier uncertainty,
and the core Hamiltonian module compiled in 18 seconds.

The core blueprint now marks its 12 statements and seven proofs checked.
The already checked generic conjugacy owner remains unchanged and matches
the periodic-swap branch exactly. The source restrictions above are unchanged:
the normalized chain and full two-site frame results do not prove the actual
cropped-chain identification or a physical endpoint uniform gap.

## Narrow spectator dependency extraction

The first bounded probe and its import-only diagnostic did not reach new
proof diagnostics within sixty seconds. Inspection of the actual artifact
import graph found that the dependent gap leaf loaded 10,932 modules, compared
with 4,612 for the checked boundary-column dependency. The generic spectator
maps were housed in `SpectatorTransport`, which also imported the C3/FNW and
strong-irreducibility applications.

The complete existing `ContinuousLinearMap` section, 297 lines, is moved
unchanged to `SpectatorMaps.lean`. Its exact section SHA-256 remains
`9e243261ee1a926ea253acbb23b6385f5fc6b0caa81806f0039537e24b3d284c`.
No public name or proof body changes. `SpectatorTransport` imports the new
leaf and retains its application-specific mathematics. `SpectatorGapEquivalence`
imports only the light leaf, and `JointMixedEndpointSpectatorGap` imports
`Overlap.Basic` explicitly for the configuration abbreviation.
This is a dependency extraction, not new mathematical coverage.

The source bundles include the complete real moved leaf and both unchanged
gap proof bodies, avoiding stale heavy imported artifacts. Mixing the new
`SpectatorMaps` artifact with an old `SpectatorTransport` artifact would
duplicate the moved declarations, so native validation must rebuild the
re-exporting module before checking consumers that import both routes.

Using the same artifact-graph traversal with only the changed source imports
overridden, the dependent gap closure decreases from 10,932 to 3,822 modules
(7,111 removed, one new leaf). The joint specialization decreases from
10,933 to 4,170 modules (6,764 removed, one new leaf). Neither new closure
contains `SpectatorTransport` or `C3Threshold`. Counts are dependency-graph
results, not timing or native-module validation claims.

The move exposed six existing generic helpers without prior blueprint tags.
They are now linked to the existing right-spectator extension and kernel
projection entries. Their proof text and mathematical statements are unchanged;
these ownership links do not count as new results. Global synchronization and
reverse coverage pass for both moved and newly authored declarations.

The initial two whole-import probes and a concatenated complete edge bundle
hit the sixty-second wall bound without diagnostics. Those attempts were
inconclusive. Isolated module checks subsequently validated the new results
and their actual imports; their source hashes supersede the early bundle
snapshots. Native elaboration found two argument-inference issues and one
coercion-wrapper issue. Explicit fiber vectors, explicit regression
parameters and an explicit conjugated target resolved them without changing
a statement, assumption or resource limit.
