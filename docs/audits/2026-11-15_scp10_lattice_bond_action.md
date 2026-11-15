# Periodic quantum-double bond-action recovery

Issue: [#8947](https://github.com/LionSR/TNLean/issues/8947).
Base: `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.

## Mathematical scope

The source is SCP10, `Papers/1001.3807/paper_v3.tex:2904–2923`,
equation `eq:ex:doubles-renorm-tensor` and the three Hamiltonian families.
The new module places coherent bond color changes on the full physical
configuration space `(G⁴)^V` of a periodic simple square lattice. Both
periods are at least three. No abelian-group assumption or flatness
restriction is imposed on that space.

It supplies the permutation representation of `G^E`, distinct-bond
commutation, the four horizontal/vertical incident actions, spectator
support, conjugation covariance of both product-one constraints, and the
intertwining identity for actual shared bond colorings. The hole readout is
identified directly with `quantumDoubleKPlaquetteHolonomy` on the four
periodically indexed blocks. There is no surjectivity claim from colorings
to all flat configurations: that would discard the nontrivial torus sectors.

These are auxiliary placement results. The three normalized matrix term
families, all their commutators, full common-kernel spanning and dimension,
comparison with the existing PEPS parent, and a globally tiled nonabelian
elementary-to-K physical renormalization remain open under #8947.

## Recovery provenance

The source is recovered from `QuantumDoubleLatticeGauge.lean` at the closed,
unmerged restoration head `a40184a42521cc1a11a0e99ee1ee4813b554f073`.
That restoration calls the lattice files reconstructions; this recovery
does not attribute them to the unlocated original full-kernel packet.
See [the earlier recovery audit](2026-10-29_scp10_packet_recovery_status.md).

Changes from that gauge module are an explicit import of the pinned
Mathlib's `Algebra.Group.Pi.Lemmas`, a module-level statement of the remaining
obligations, and the direct equality with the existing four-block holonomy.
The incomplete archived Hamiltonian, blocking, ground-space wrappers and
obsolete fixtures are not restored in this change.

## Interfaces and the next classification step

The action uses the existing `Edge (torusGraph width height)` and
`torusUpEdge`, `torusRightEdge`, `torusDownEdge`, `torusLeftEdge` incidence
conventions. It adds no competing lattice or parent type.
The horizontal restrictions return the existing `quantumDoubleKBondLeft`
and `quantumDoubleKBondRight`. The two holonomy invariance equivalences can
be consumed by the existing diagonal/permutation commutation lemma; the
bond representation can be consumed by normalized finite-group averaging.

Before a full-kernel implementation, identify the explicit source local
kernels with the hypotheses of `IsGInjective.torusParentKernel_eq_commutingClosureSpan`
in `ParentHamiltonian/TorusRegularParentGroundSpace.lean`, or the physical
padding variant `ker_nonuniformTorusPlaquetteParent_eq_map_nativeCommutingClosureSpan`
in `ParentHamiltonian/NonuniformNativeParentClassification.lean`.
Their dimension results already count `CommutingPairConjugacyClass G`.
They require an actual `IsRegionParentInteraction` proof for the regional
interaction, which the present bond-action identities do not supply.

Sibling [#8703](https://github.com/LionSR/TNLean/issues/8703) retains
bulk/open-boundary path deformation, exterior-support assumptions and local
unobservability. This change neither edits its path/homotopy modules nor
derives cross-winding equality. Its support lemma concerns the four physical
corners of a single bond action; it is not a reduced-density equality.

## Validation status

The task environment contains no Lean or Lake executable and no `.lake`
directory. Its enforced disabled network policy returns proxy HTTP 403
for the pinned Lean release download. No local Lean elaboration, Lake
build, Mathlib rebuild or compiled `checkdecls` is claimed.

The pins remain Lean `v4.36.0-rc1`, Mathlib
`625d8914199bc567cca9b91f90e8e5afafa5ae51`, and QICLean
`c457682404aa548b4acd16ac27be5d3835e68892`. The pinned Mathlib source was
inspected for `MonoidHom.mulSingle` and `Pi.mulSingle_commute`; the latter
is mapped through the permutation representation instead of reproved.

Local supporting checks pass: generated imports, numbered/oversized module
policy, blueprint mathematical roles, newly added reader-facing prose and
whitespace. All 22 declarations in the new module have unique matching
blueprint references. The whole-tree text-only declaration check still
reports 563 unresolved references because dependency checkouts are absent;
none of those references belongs to this change.

An independent symbolic calculation performed 4,736 exact free-group word
reductions on 3×3, 3×4, 4×3 and 4×5 periodic incidence models. It checks
composition, inverses, distinct-bond commutation, spectator support, all four
incident restrictions, the two conjugation identities and coloring
flatness, including seams. These are supporting algebra/order checks, not
Lean elaboration or a proof of all periods. The required pinned TeX
formatter is also unavailable locally.

Current-head hosted Lean verification is required before this recovery is
accepted. The new blueprint entries intentionally omit `\leanok` while
that verification is pending. No issue closure or merge is requested.
