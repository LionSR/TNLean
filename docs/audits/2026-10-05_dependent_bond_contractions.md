# Edge-dependent contraction and cut foundation

## Mathematical contract

`TNLean.PEPS.DependentBondNetwork` supplies actual coordinate contractions on
finite directed multigraphs represented by arbitrary maps `tail head : Edge → Vertex`.
An edge label, rather than its pair of vertices, identifies a bond. Thus distinct
parallel edges survive, and a self edge has two distinct endpoint incidences.
The endpoint type is `Edge × Bool`, with false denoting tail and true head.

The virtual alphabet is an arbitrary family `D : Edge → Type*`; the physical
alphabet is an independent arbitrary family `Phys : Vertex → Type*`. Only the
virtual alphabets need be finite for contraction. No nonemptiness, equal-dimension,
simplicity, looplessness, representation, or injectivity assumption is imposed.
Matrices always have head-row and tail-column order.

`endpointSiteEquiv` is an actual equivalence from independent endpoint labels to
local incidence-fiber configurations. `endpointPairEquiv` regroups them into
head/tail pairs per edge. `prod_incident_eq_prod_endpoint`,
`prod_incident_eq_prod_edge`, and `sum_endpoint_prod_eq_prod_sum` implement the
product and sum reorganizations needed for local projector expansion. The
product-over-fibers proof reuses Mathlib's `Fintype.prod_fiberwise`; the independent
sum factorization reuses `Fintype.prod_sum`.

`network` is the sum over every independent endpoint assignment of the product
of inserted edge-matrix entries and the local physical tensor factors.
`network_eq_sum_site` proves the equivalent site-grouped contraction formula.

## Full joint cut boundaries

`DependentBondCut.lean` opens both endpoints of each edge in any finite cut set.
`CutConfig C D` is a dependent function on all those endpoints. A boundary tensor
is an arbitrary function `CutConfig C D → ℂ`, so it includes correlations across
edges and between their endpoints. `cutCoeff` contracts this tensor against
identities on uncut edges and actual local tensor entries. `cutMap` is the
resulting linear map and `cutSpace` its range.

`mem_cutSpace_iff` gives the coefficientwise realization criterion.
`cutMap_eq_sum_single` and `cutSpace_eq_span_single` give the complete
fixed-boundary column expansion and spanning characterization. The product
boundary construction is only a special case. `cutCoeff_bondBoundary` evaluates
that case as an inserted-matrix network. `cutBondBoundary_units` identifies each
coordinate boundary with a product of matrix units, and
`cutMap_single_eq_network` identifies its column with the corresponding literal
network, with identities on all uncut edges.

These are reusable prerequisites for removing the common-alphabet restriction
from SCP10, arXiv:1001.3807, Theorem 5.5 and equation
`eq:2d:closure-intersection`. They do not themselves assert its closure theorem.
The consuming packet owns the native four-cut specialization, blueprint entries,
and import-router integration.

## Focused regressions

`TNLeanTest/PEPS/DependentBondCut.lean` checks:

- Two labelled self edges of dimensions two and three have four distinct
  incidences and 36 independent endpoint configurations.
- Cutting the dimension-two edge gives four boundary configurations; opening
  both gives all 36.
- Distinct parallel edges between two different vertices remain distinct and
  give a six-dimensional local virtual configuration space.
- Endpoint regrouping is invertible, including for parallel self edges.
- Identity insertions with constant site factors give the nonzero contraction
  `2 × 3 = 6`, so the varying-dimension instance is not vacuous.
- Physical alphabets may simultaneously have dimensions five and seven.
- An explicit correlated boundary on the two unequal-dimensional edges cannot
  factor as a product of two bond matrices.
- Empty virtual alphabets and empty edge sets remain admissible.
- The matrix-unit and full-span theorems depend only on the standard Lean
  axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Validation

Both implementation modules and the regression module passed direct Lean
compilation with the repository toolchain and every requested strict option:

```
-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false
-Dlinter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 -DwarningAsError=true
```

Validation used a private symlink overlay of the exact available dependency
artifacts. No Mathlib source rebuild, shared artifact mutation, router edit, or
push was performed. `git diff --check` and the proof-integrity token scan passed.
The repository tactic-pattern scanner also ran. The new proofs reuse existing
finite-product identities rather than introducing another incidence-reindexing
proof pattern. Full aggregate builds and blueprint checks are the consuming
packet's integration responsibility.
