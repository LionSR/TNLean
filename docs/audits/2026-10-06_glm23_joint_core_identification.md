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

## Validation

Source-only development: no Lean, Lake, cache writes, or publication have
been performed by this worker. Native elaboration and strict guards are
pending coordinated read-only probes and later individual module checks.
The blueprint has no `leanok` markers until the required native checks pass.
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
