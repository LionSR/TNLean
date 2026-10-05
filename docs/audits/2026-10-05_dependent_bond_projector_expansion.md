# Dependent-dimensional canonical projector expansion

## Mathematical scope

`TNLean.PEPS.DependentBondNetwork` now has an actual oriented incident
representation for a finite directed multigraph with edge-indexed coordinate
types `D e` and independent representations `U e`. The graph may have parallel
edges and self edges. A self edge retains both its endpoint incidences. The
canonical local tensor is the averaging projector on the dependent local
configuration space, rather than a replacement with uniform-dimensional legs.

The head carries `U e g`; the tail carries the transpose of `U e g⁻¹`.
`incidentMatrix_one` and `incidentMatrix_mul` derive the representation laws.
They require no finiteness of the group and no unitarity assumption.

For finite groups, `representationAveragingSite` also supports arbitrary
representations on each actual local configuration space. Its coefficient map
is exactly the average, and `isGInjective_representationAveragingSite` derives
both invariance and injectivity on the invariant subspace. Physical spaces in
`localSiteMap` may vary independently from vertex to vertex.

`network_averagingSite` computes the literal independent-endpoint contraction
with arbitrary matrices `B e`. It gives the normalization
`(card G : ℂ)⁻¹ ^ card Vertex` times the sum over `q : Vertex → G` of the product
of the entries of

`U e (q (head e)) * B e * U e ((q (tail e))⁻¹)`.

The head endpoint is the row index; the tail endpoint is the column index.
`network_averagingSite_bondGauge` derives canonical-network gauge invariance
for arbitrary inserted matrices by reindexing the vertex-label sum by right
multiplication. `network_averagingSite_vertexGauge` specializes this to edge
group labels. Neither theorem assumes that the group elements commute.

No expansion, Gram identity, global injectivity, or bond nondegeneracy is
assumed. The proof expands finite sums and regroups the actual endpoint
indices. This module does not itself assert the four-cut closure theorem.

## Source correspondence

Schuch, Cirac, Pérez-García, arXiv:1001.3807:

- Definition 5.1, `def:2d-Ug-inj`, lines 1278–1296: local invariance and the
  invariant projector obtained after a local left inverse.
- Lines 1310–1316: each link may carry its own representation, with its two
  incident tensors using the same representation. No equality of different
  links' dimensions is assumed here.
- Theorem 5.5, `eq:2d:closure-inv` and `eq:2d:close-in-in`: use of the actual
  local projectors in the closure argument.
- Theorem 5.9, lines 1582–1621: local inverse and representation-coefficient
  recovery in the ground-state spanning/independence argument.

The expansion is an algebraic consequence of these projectors, valid without
the additional semi-regularity used later in coefficient extraction. It is
not a new definition of the contraction.

## Regression coverage

`TNLeanTest/PEPS/DependentBondProjectors.lean` checks:

- Two separately labelled self edges, with respective dimensions two and three.
- Four incident endpoints and local configuration cardinality 36.
- Representation multiplicativity for arbitrary, possibly infinite groups.
- The literal coefficient-map equality and G-injectivity.
- Arbitrary independent edge representations and inserted matrices in the
  canonical network expansion.
- The trivial-group contraction with arbitrary, including non-diagonal, bond
  insertions: normalization one and the correct head-row/tail-column order.
- Canonical vertex-gauge invariance for an arbitrary finite group.
- Axiom guards for the representation law, generic G-injectivity, and network
  expansion and vertex-gauge invariance, all restricted to `propext`, `Classical.choice`, and `Quot.sound`.

## Validation

The new source and regression module compile with:

`-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false`
`-Dlinter.mathlibStandardSet=true -DmaxSynthPendingDepth=3`
`-DwarningAsError=true`.

Prebuilt dependency artifacts were reused through a private symlink overlay;
Mathlib was not rebuilt. The dependency is the frozen
`DependentBondNetwork.lean` from commit
`5f0a8d938e3a0b803026929d0caa09acbb72bd16`.

No `sorry`, `admit`, new axiom, `native_decide`, or unsafe cast occurs in the
new proof module. `git diff --check` passes. A focused tactic-pattern scan of
`TNLean/PEPS` was run; the highest repeated blocks were pre-existing graph
coordinate-transport proofs, not newly added expansion code. Shared import
routers, blueprint files, and existing proof modules are left for integration.

## Reuse observation

The direct average-map G-injectivity argument also occurs in earlier torus
and simple-graph canonical-site modules. The new generic dependent-site
constructor gives future callers a reusable result; consolidating those older
modules around a fully generic representation-average lemma is a separate
shared-file cleanup, not needed for this expansion.
