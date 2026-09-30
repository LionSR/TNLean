# Fixed-point ingredients for the one-dimensional SPT classification

This audit concerns issues #2147 and #2661 and the argument in
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Sections II.D.2 and II.F.
The source-labelled classification theorem remains unformalized. Equality
of virtual cocycle classes is not, by definition alone, an equivalence by
symmetric gapped Hamiltonian paths.

## Realization and alignment of virtual representations

For a finite group, every multiplicative complex cocycle class has a
unitary projective realization on a virtual space of dimension equal to
the order of the group. The associated matrix-unit tensor is injective
and has a unitary physical symmetry. The physical representation is
chosen from the cocycle; it is not prescribed in advance. The theorem is
`MPSTensor.exists_unitary_injective_fixedPoint_for_cocycle`.

Cohomologous unitary factor systems can be aligned by unit-modulus
rephasing. Projective representations with exactly the same factor
system admit a direct sum, and unitary summands give a unitary direct
sum. The on-site representation uses the transpose of the inverse
adjoint action, as required by the row convention for physical-index
mixing.

## Direct-sum bond interpolation

For positive endpoint dimensions, the diagonal bond matrix has weights
`1 − γ` and `γ` on the two summands. Its squared norm is
`D₀(1 − γ)² + D₁γ²`, which is positive for every real parameter.
The normalized matrix is continuous and invariant under conjugation by
the unitary virtual direct sum.

The weighted matrix-unit tensor has letters
`Aγ(a,b) = Ŵγ(a,a) Eab`. Its positive-length cyclic coefficients are
exactly the products of the incoming-bond amplitudes. The path has a
fixed physical symmetry. At its endpoints, equality is asserted for
physical states: some cross-block tensor letters can remain nonzero,
but their cyclic contributions vanish.

The independent-bond Hamiltonian is the sum of the complementary
rank-one projections. Its kernel is precisely the line through the
product of the normalized bond vectors, and its quadratic forms satisfy
`H² ≥ H`, uniformly in chain length and parameter. Its matrix entries
vary continuously with the parameter. Regrouping the registers is a
unitary permutation. The exact conjugation formula shows that each
bond term acts on the right register of one physical site and the left
register of its neighbor, with identities on every other register.
The two-site interaction has operator norm at most one, and the sum of
its cyclic translates is exactly the transported bond Hamiltonian. The
physical Hamiltonian commutes with the full on-site symmetry. Its spectrum
contains zero and has no values strictly between zero and one.

The definition `normalizedBondFixedPointGappedPath` now assembles these
results into the independent common-space path condition. It gives a
symmetric gapped path between the two direct-sum fixed-point interactions.
Path reversal and concatenation preserve that condition, with the minimum
of the two gap bounds serving for a concatenation. These statements are
recorded in the blueprint with their actual hypotheses. They do not by
themselves establish the classification of arbitrary injective endpoints.

## Remaining classification arguments

The rectangular polar factorization provides a continuous local
deformation from an injective physical map to an isometry. The map
remains injective along the interval and preserves a unitary symmetry
intertwining relation. The corresponding symmetric parent-Hamiltonian path is now constructed
in `exists_symmetric_injective_parent_path_to_isometry`. It starts from
any one-site injective tensor with exact unitary on-site symmetry.
Canonical normalization supplies unitary virtual implementers and leaves
every parent interaction unchanged; no virtual-unitarity or gap hypothesis
is imposed on the original tensor.
The many-body estimate uses the following independent gap argument. Fixed-window boundary maps, ground-space projections, and open and
periodic Hamiltonians are continuous. An explicit norm perturbation
estimate now proves that every strictly smaller finite-window gap persists
locally in the parameter. An open-chain comparison now transfers the primitive long-range gap to
range two. Together with finite-window stability and compactness, this
proves a positive gap uniform over any compact one-site injective family
and every periodic chain of at least two sites. For the finitely many
lengths below the common threshold, continuity of the rank-one periodic
ground-state projection gives a positive bound at each length; their
finite minimum completes the estimate. The declaration is
`exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths`.

The common-space path condition is now defined independently by
`SymmetricGappedInteractionPath`: it requires bounded continuous local
interactions, global symmetry, and a gap uniform in both parameter and
chain length. It allows ground-state degeneracy and nonzero ground energy.
For a given continuous unitary virtual projective representation on a
fixed positive-dimensional space, the endpoint factor systems are proved
cohomologous. Continuous roots of the determinants remove their continuous
phases, leaving factor systems valued in a finite set of roots of unity;
connectedness makes these constant. This argument does not assume that
the group is finite.

The converse still requires extracting such continuous virtual data from
the allowed smooth symmetric MPS parent-Hamiltonian paths, including
changes of bond dimension. The separation argument in the source explicitly
works within MPS; it does not establish separation along arbitrary gapped
Hamiltonian paths beyond that setting. The existing predicate `IsVirtualCocycleEquivalent`, defined
through cohomologous factor systems, does not supply this implication.
These obligations remain attached to the unready classification entry;
they must not be discharged by identifying phase equivalence with its
proposed invariant.

## Verification

Scoped locked Lake builds have passed for the two-site interaction,
its continuity and projection properties, and the physical spectral-gap
and symmetry modules. The corresponding kernel axiom checks report only
`propext`, `Classical.choice`, and `Quot.sound`. The finite-window
projection and Hamiltonian continuity modules also pass their scoped
locked builds and axiom checks. The source synchronization script passes, and a separate Lean file
importing the completed symmetry and compact-gap modules checks all
71 declaration references now present in the SPT chapter. This is a
scoped declaration check, not a full repository declaration check. The full `leanblueprint
checkdecls` command has not passed: its pinned Lake-dependent executable
terminates with a macOS runtime fault (exit 133).

## Mathematical terminology

The former predicate `IsSameSPTPhase` is renamed
`IsVirtualCocycleEquivalent`: its definition asserts only the existence of
cohomologous intertwining virtual representations. It has no proof
consumers, and no deprecated alias is retained. This removes a name that
suggested the still-unproved identification with symmetric gapped-path
equivalence. The independent path condition is unchanged.

The remaining forward classification step places the two isometric
endpoints and the bond interpolation in one symmetry-preserving physical
space. A rectangular physical isometry now transports each finite-window
ground space and its parent interaction exactly, while its orthogonal
complement has unit local energy. The two-site endpoint interactions are not
equal after padding a bond space into the direct sum. Write $D=D_0+D_1$,
and let $\eta_i$ be the normalized entangled bond on summand $i$. The
local kernel of the bond-product interaction is
$\mathbb C^D\otimes\mathbb C\eta_i\otimes\mathbb C^D$, of dimension $D^2$.
The canonical parent of the summand's embedded matrix-unit tensor has local
kernel $\mathbb C^{D_i}\otimes\mathbb C\eta_i\otimes\mathbb C^{D_i}$, of
dimension $D_i^2$. Since the other summand has positive dimension, equality
of these interactions is impossible. The endpoint argument must instead
prove that the embedded parent projection dominates the bond-product
projection and that both periodic Hamiltonians annihilate the same product
bond state. Their convex interpolation remains bounded and symmetric, and
the bond-product Hamiltonian's unit gap gives a uniform gap throughout.
The first projection comparison and both periodic kernel inclusions are now formalized, as detailed below; the complete endpoint-path assembly is not yet established.
The reverse implication still requires continuous virtual symmetry data
extracted from the allowed MPS paths.

The canonical normalization and arbitrary symmetric polar-parent theorem
pass strict elaboration with the package options. Their kernel audits
report only `propext`, `Classical.choice`, and `Quot.sound`. The compact
all-length gap and matrix representation, together with both affected
Beigi consumers, pass a scoped locked Lake build (9,321 jobs). The canonical unitary representation, normalized symmetric representative,
physical embedding module, and arbitrary symmetric polar-parent path also
pass their scoped locked build (9,398 jobs). The orthogonal-embedding path and its matrix rotation helper also pass
their scoped locked build (9,383 jobs).

`orthogonalEmbeddingGappedPath` now joins two orthogonal isometric physical
embeddings of the same injective tensor whenever both intertwine the
physical actions. The path rotates the two embeddings through angle
πt/2, remains isometric and injective, and uses the proved compact-family
gap. Strict elaboration and its kernel axiom audit pass; no spectral-gap
hypothesis is supplied to this construction.


The finite-matrix comparison used by the proposed endpoint path is now
proved as `Matrix.gap_interpolation_of_le`. If `0 ≤ A ≤ B` and `B` vanishes
on the kernel of `A`, then `A + t • (B − A)` is positive semidefinite for
every `t ≥ 0`, has the same kernel, and retains every quadratic lower
bound of `A` on that kernel's orthogonal complement. This supplies the
abstract gap argument. The concrete first-endpoint projection inequality and both common periodic ground lines are established below. The assembly of both endpoint paths remains a separate step.

The comparison lemma passes its scoped locked Lake build (2,709 jobs) without
warnings. Its kernel audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. The loaded Lean environment checks the existing 71 SPT
blueprint declarations and the new comparison lemma; the blueprint text
synchronization and duplicate-tag checks also pass. These remain scoped
checks, not a full repository build or full `leanblueprint checkdecls` run.

The subsequent full locked repository build passes (10,872 jobs). A direct
Lean environment check, importing `TNLean`, resolves all 9,940 names in
`blueprint/lean_decls`, including the newly added entries. This repeats the
declaration-membership test used by the upstream checker. The usual
`leanblueprint checkdecls` executable still terminates with exit 133 on
this macOS installation; no successful run of that executable is claimed.

The local-to-periodic order step is now proved in
`InteractionHamiltonianOrder.lean`: periodic summation preserves positive
semidefiniteness and operator inequalities, and commutes with the affine
interpolation `A + t • (B - A)`. The scoped locked build passes (9,338 jobs);
all three declarations have only `propext`, `Classical.choice`, and
`Quot.sound` in their kernel dependency lists. These facts still require
the concrete endpoint inequality before they can complete an endpoint path.

The ordered interpolation now also has a proved spectral formulation in
`CommonKernelSpectralGap.lean`. A quadratic lower bound on the orthogonal
complement of the kernel bounds every nonzero spectral value. If the
original kernel contains a nonzero vector, zero remains a spectral value
throughout the interpolation. The scoped build including the injective-parent
consumer passes (9,381 jobs), and the three spectral declarations use only
the standard logical axioms. The repeated conversion of a matrix eigenvector
equation into Euclidean-space coordinates has been replaced at all three
occurrences by one helper, recorded in the tactic ledger.

The spectral-to-quadratic conversion needed to use the independent-bond
gap is now proved as
`Matrix.orthogonal_quadratic_gap_of_spectrum_separated`. The statement
requires only Hermiticity and the specified spectral separation. Expanding
in an orthonormal eigenbasis gives the quadratic lower bound on the kernel's
orthogonal complement. The exact application to the physical bond
Hamiltonian with gap one passes strict elaboration. The scoped algebra build
passes (2,710 jobs), and the new theorem has only the standard logical axioms.

## Embedded endpoints and local order

Both embedded matrix-unit endpoints are now proved injective, with periodic
vectors equal to the corresponding normalized bond-product vectors. Their
canonical parent Hamiltonians annihilate these vectors, giving both required
periodic kernel inclusions. The periodic endpoint module passes its locked
build (9,417 jobs).

At the first endpoint, the two-site physical inclusion intertwines the bond
penalties. The resulting inclusion of local kernels proves that the bond
interaction lies below the embedded canonical parent interaction. The local
order module passes its locked build (9,418 jobs). The first inclusion also
intertwines the common on-site action; exact virtual covariance and symmetry
of the periodic parent follow. The symmetry module passes its locked build
(9,434 jobs). The audited declarations use only `propext`, `Classical.choice`,
and `Quot.sound`; these modules contain no proof placeholders.

The remaining classification argument still requires the second endpoint
connection and the composition with the physical embeddings and polar
deformations. The reverse implication requires extraction of continuous
virtual symmetry data from the allowed physical paths, including changes
of bond dimension. The source-labelled classification remains unformalized.

The final repository verification passes the locked full build (10,879 jobs)
and the generated-import check (62 aggregators, 1,472 production modules).
Blueprint synchronization passes. A direct check in the imported `TNLean`
environment resolves all 9,982 entries in `blueprint/lean_decls`. This is
the declaration-membership test used by the upstream checker; the native
`leanblueprint checkdecls` executable remains unavailable because it exits
with status 133 on this installation. Changes remain local.

The first endpoint's affine interaction has checked endpoints, Hermiticity,
continuity, and norm at most one. The periodic positivity, quadratic gap,
nonzero ground vector, and kernel-inclusion inputs are also checked. The
complete symmetric gapped-path construction has not been assembled; no
conditional substitute is presented as that construction. Thus both
endpoint-path assemblies, and their subsequent composition, remain open.
