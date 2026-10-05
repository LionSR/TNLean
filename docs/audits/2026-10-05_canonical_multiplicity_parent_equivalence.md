# Exact canonical parent equivalence under multiplicity restoration

## Result and hypotheses

`map_ker_regionParentHamiltonian_multiplicity_eq` proves exact transport of
**the entire canonical parent-Hamiltonian kernel**, not merely one closed
state or its inserted-state span.

The input consists of a finite simple graph, positive block dimensions dᵢ,
finite-group matrix representations Dᵢ, and physical enumerations of the
incident endpoint coordinates. The source tensor is the actual dressed
averaging tensor for ⊕ᵢDᵢ with fourth-root weights dᵢ^(1/4). The target is the
actual averaging tensor for ⊕ᵢDᵢ⊗I_{dᵢ}. The parent regions must contain both
endpoints of every graph edge. The interactions on each side may be any
positive matrices whose kernels are the genuine open-region ranges.

The supplied physical map is the actual product of the Section 7 supported
bond maps, expressed in numbered vertex coordinates. Its restriction is
`canonicalMultiplicityParentEquiv`. Thus the common parent-space dimensions
are equal, as stated in `finrank_regionParentGroundSpace_multiplicity_eq`.
No closure-spanning assumption, equality of parent kernels, or equality of
local ranges is a hypothesis.

## Crossing-boundary proof

1. `SemiRegularBondSparseAction` proves the sparse coefficient formula for
   the existing full endpoint-pair map and its product. An output coefficient
   is an equal-copy indicator, multiplied by the reciprocal square root of
   the copy dimension, times the input coefficient at the original labels.
2. `SemiRegularBoundaryTransport` proves both oriented boundary identities
   and their adjoints. It keeps the single-endpoint fourth-root weights and
   absorbs the remaining scalar into the virtual boundary coefficient.
3. `GraphOpenMultiplicityTransport` proves actual open-generator formulas.
   The regional map sends each weighted generator to an explicit sum of
   repeated generators. Its adjoint sends each repeated generator to a
   scalar multiple of a weighted generator.
4. `SemiRegularCanonicalLocalTransport` identifies those bond-coordinate
   spaces with the existing genuine numbered `regionGroundSpace`, using the
   original open contractions. Both local-range inclusions therefore concern
   the actual canonical parents.
5. `GraphBondRegionBlocks` factors each block of the literal global bond
   matrix into an exterior scalar and the regional transformation just
   analyzed. `RegionOperatorBlocks` lifts those derived block inclusions to
   the full common regional conditions in both directions.
6. Source product matching-sector support was already derived from the
   actual canonical parent constraints. `GraphRepeatedParentSupport` now
   derives target product-image support from the target's actual open
   contractions and edge coverage. Neither support is assumed.
7. `SemiRegularBondRetraction` supplies the product partial-isometry
   identities. On these two supported parent spaces, the global map and
   its adjoint are exact inverses. This gives the equivalence and the full
   parent-kernel identity.

## Source fidelity and remaining scope

Source: SCP10, arXiv:1001.3807v3, Theorem 5.7 and Section 7,
local source lines 2977–3019. Site averages use the established |G|⁻¹
normalization on both sides. All physical endpoint orientations are those
of the actual ordered-edge graph contraction.

The result does not require the supplied blocks to be irreducible; it is
an algebraic canonical-parent equivalence for any positive block dimensions.
For the paper's minimal construction, the existing finite-group factory
provides the distinct irreducible blocks and identifies the repeated
representation with the regular one in Fourier coordinates. Completing that
identification for parent spaces requires the all-boundary coordinate
transport; a closed-state coordinate identity is insufficient.

This packet does **not** claim the full arbitrary-semi-regular form of
Theorems 5.7/5.9. An arbitrary semi-regular representation can have
multiplicities mᵢ other than one or dᵢ. Its weighted-target extension uses
(dᵢ/mᵢ)^(1/4), and the representation/block factory and fixed-representation
physical comparison must be composed explicitly. The existing unitary
character-block decomposition already derives positive dᵢ,mᵢ for arbitrary
unitary representations, but that fact alone is not a parent-family theorem.
No spectral-gap or equality-of-excited-spectra assertion is made.

## Validation

The full new dependency closure compiles with the repository's Lean options,
using isolated outputs and read-only prebuilt package artifacts. QICLean is
at the manifest pin `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. No Mathlib
source rebuild was used, and no root import regeneration is included.

`TNLeanTest/SemiRegularCanonicalParentTransport.lean` checks an actual
physical dimension change from two to four at each vertex of a two-vertex
graph, annihilation of unequal copy registers, and the empty graph with
zero physical alphabet on one side. The generic product-range helper was
also checked on empty site/input/output types.

Axiom inspections of the full kernel identity, the parent equivalence,
both open-generator transport formulas, and target global support report
only `propext`, `Classical.choice`, and `Quot.sound`. New modules and
regression checks emit no linter warnings.
