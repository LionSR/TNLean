# Tag and zero-reset encoding for one hole

This development isolates the finite-dimensional encoder prerequisite of
issue #8770. The source is the September 24, 2026 manuscript *Polynomial PEPS
approximation of gapped square-grid ground states*,
[`05-frames.tex`, lines 13–97](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/05-frames.tex#L13-L97),
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The relevant source labels are `eq:hole-projector`, `eq:hole-encoder`, and
`eq:encoder-contraction`, together with the empty-outer identity convention.
The source file's Git blob is `e5aace5b02cf32814272e3e7405be5c7b1ad3dc9`.
It was checked against the local pinned source with `git hash-object`.

The source comparison separates the following passages:

| Source lines | Content | Scope here |
| --- | --- | --- |
| 13–19 | Physical coordinates and sheets with owners | Existing physical coordinates only; no sheet ownership |
| 26–48 | Square geometry, cylinder projector, approximation and polynomial rank input | Arbitrary nested regions and inside spaces; geometric and approximation inputs remain separate |
| 50–59 | Tag register and exact reset formula | Actual finite tag and full raw-coordinate matrix |
| 60–64 | Product reset vector and exact Gram/contraction identity | Normalized coordinate resets, derived Gram identity and Hilbert contraction |
| 65–69 | Raw-register retention, adaptive regions, and empty-outer identity | Full output configuration, branch-specific region, and separate singleton-tag identity |
| 71–97 | Frames, ownership, disjoint holes and frame norm estimate | Outside this module |

## Exact scope

The new module is `TNLean/PEPS/Approximation/HoleEncoder.lean`. It uses the
unchanged cylinder and nested-cylinder orthogonalization development to
construct an actual rectangular matrix on the existing dependent physical
configurations. Its rows carry both a finite tag and a full raw configuration;
its columns carry a full raw input configuration.

The encoder is constructed from arbitrary nested finite regions and arbitrary
inside subspaces. This is the linear-algebra step in the source construction.
It does not construct the source's square samples, spectral filters, accuracy
estimate, or polynomial bound in the lattice scale. In particular, the tag
dimension bound is the sum of the supplied inside dimensions. Obtaining the
source's fixed power of the lattice scale requires the separate inside-rank
estimates.

No sheet or party ownership assignment is defined or changed. The multi-hole
commutation and frame norm estimate, noncommutative telescoping, filtering,
and the full source Lemma 6.3 remain outside this module.

## Configurations, projected images, and tags

For finite sites `V` and finite local coordinate types `A v`, fix a global
configuration `z : (v : V) → A v`. This explicitly chooses the distinguished
zero coordinate at every site. Its restriction to `R` indexes the product
coordinate vector `|0_R⟩`. Each site's zero vector is normalized because it
is a coordinate basis vector; it is not the zero vector of its Hilbert space.
Choosing `z` requires a coordinate at each site, as does the manuscript's
fixed one-site unit vector. No implicit choice of a coordinate is made.

For a monotone family `R₀ ⊆ ⋯ ⊆ R_(n−1)` and inside subspaces `Sⱼ`, retain
the existing projected images

`S̃ⱼ = (I − P_(Wⱼ)) Sⱼ`,

where `Wⱼ` is the earlier span expressed in the current inside coordinates.
Choose an orthonormal basis `v_(j,ℓ)` of the Euclidean-space realization of
`S̃ⱼ`. The tag type is the dependent sum over `j` of
`Fin (finrank ℂ (coordinateSubspaceES S̃ⱼ))`.
Consequently its cardinality is exactly `Σⱼ dim S̃ⱼ`, and the previously
proved image-dimension bounds give `Σⱼ dim S̃ⱼ ≤ Σⱼ dim Sⱼ`.
These are inside dimensions, with no multiplication or cancellation by an
outside dimension.

## Exact matrix coefficients

For a tag `(j,ℓ)`, output configuration `x`, and input configuration `y`,
the matrix entry is

`K[((j,ℓ),x),y] = conj(v_(j,ℓ)(y|Rⱼ))`

when both `x|Rⱼ = z|Rⱼ` and `x|(V\Rⱼ) = y|(V\Rⱼ)` hold, and is zero
otherwise. Equivalently,

`K = Σ_(j,ℓ) |j,ℓ⟩ ⊗ (|0_(Rⱼ)⟩⟨v_(j,ℓ)| ⊗ I_(V\Rⱼ))`.

Every summand has the same full raw output space. The tag chooses its own
region `Rⱼ`, so the construction does not replace the adaptive radii by
one common reset region. The complement is preserved coefficient by
coefficient, not only up to an abstract Hilbert-space isomorphism.

Orthogonality of tags eliminates cross terms in `K†K`. Normalization of
the reset ket removes its Gram factor. The orthonormal-basis sum inside
each branch gives `P_(S̃ⱼ)`, and the unchanged orthogonalization theorem gives

`K†K = Σⱼ P_(S̃ⱼ) ⊗ I_(V\Rⱼ) = P_E`,

where `E = Σⱼ Cylinder(Rⱼ,Sⱼ)`. It follows that
`‖Kψ‖ = ‖P_E ψ‖ ≤ ‖ψ‖`. These claims concern the Euclidean Hilbert norms,
not a maximum-entry matrix norm or the supremum norm on ordinary functions.

## Empty cases

- A projected image of dimension zero contributes no tags and no summands.
- An empty innovation family has an empty tag set and gives the zero map.
  Its Gram operator is the projector onto the empty sum, hence zero.
- An empty region has one empty configuration and inside Hilbert space
  `ℂ`. Resetting it is automatic; the complement is the whole system.
- The source's empty outer physical sample is a separate convention:
  `identityHoleEncoder` appends a singleton `PUnit` tag and keeps the entire
  raw configuration. It is not obtained by setting the number of innovation
  branches to zero.

## Blueprint and diagram

`blueprint/src/chapter/ch24_peps_hole_encoder.tex` states the local
construction, inside-dimension bound, Gram identity, projected norm, and
identity convention after the existing nested-cylinder section. The
chapter router is `blueprint/src/chapter/ch24_peps_regions.tex`.

The native tenkz diagram represents one fixed-tag summand, with four factors:
the inside covector, the inside reset ket, the tag ket, and the complement
identity. It contains no internal contractions and has five open physical
bundles: two inputs and three outputs. The two raw output bundles combine
into the full raw configuration. There are no virtual legs or ownership
labels, and the tag sum remains in the adjacent equation.

## Verification boundary

The [declaration ledger](../provenance/openai-math.d/hole-encoder8770.json)
has one independently written-proof row for each of the twenty-two public
declarations. Its current verification identifies the unchanged source at
public commit `d92310cca4f63cf1c2b0c91936e538f80288b48c`; the actual integrated
checks ran at `8602b340cfe0b3b73bad634a06b75f9dd6b20049`. The
[current identity record](../provenance/evidence/8770-hole-encoder/current-verification/identity.json)
verifies production, consumer, guard, and raw-audit byte equality between
these revisions and the original author checkpoint. The original ledger and
logs for `4fa931f810ac576e0142fa955af5fcbd71b2615a` remain unchanged in the
[historical archive](../provenance/evidence/8770-hole-encoder/historical).

The [original local evidence packet](../provenance/evidence/8770-hole-encoder/README.md)
records successful strict source elaboration, thirteen consumer examples,
twenty-two axiom guards and twenty-two unguarded axiom reports. Every public
declaration reports exactly `propext`, `Classical.choice` and `Quot.sound`.
Earlier failed checks and a native build with warnings are retained separately
from the successful strict runs, with original-to-normalized SHA256 mappings.

The [focused rendering report](../provenance/evidence/8770-hole-encoder/render/final-verification.json)
records all twenty-two declaration links, all seven equation anchors of the
new leaf, inspection of all eight PDF pages and both diagram rasters, and
idempotence under pinned latexindent 3.24.7. The exact inherited #8809
nested-cylinder leaf retains six static-anchor gaps, listed separately in the
report; its PDF labels resolve. Generated documents and images are not part
of the source-tree evidence packet.

These are local individual-module and focused-render checks. No full-root or
import-aggregator build, full-book rendering, live-browser/MathJax execution,
remote declaration availability, CI, publication, provenance ownership, or
completion of issue #8770 is asserted. Import and CI registration remain
separate work.
